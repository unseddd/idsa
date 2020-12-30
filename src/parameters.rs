use alloc::vec::Vec;
use num::bigint::BigUint;
use num::Integer;
use rand::rngs::ThreadRng;
use rand::Rng;

use isha2::{sha256, Sha2};
use prime_math::is_prime;

use crate::{check_dsa_ln, Error};
use crate::{L_1024, L_2048, L_3072};

// "ggen" bit string for canonical G generation, see FIPS 186-4 A.2.3 Step 6.
const GGEN: [u8; 4] = [0x67, 0x67, 0x65, 0x6e];
// Excluding domain_parameter_seed, len("ggen") + len(index) + len(count),
// see FIPS 186-4 A.2.3 Step 7.
const GGEN_U_LEN: usize = 7;

/// DSA primes P and Q, and optional parameter validation values
pub struct DsaPrimes {
    pub(crate) p: BigUint,
    pub(crate) q: BigUint,
    pub(crate) seed: Option<BigUint>,
    pub(crate) counter: Option<u32>,
}

/// Prime generation validation selection
#[derive(PartialEq)]
pub enum ParameterValidation {
    /// Save validation parameters used to generate DSA primes
    Save,
    /// Discard validation parameters used to generate DSA primes
    Discard,
}

// Get the minimum recommended Miller-Rabin rounds for probabilistic prime testing
//
// See FIPS 186-4 C.3 Table C.1
fn miller_rabin_rounds(l_len: u32) -> u32 {
    match l_len {
        L_1024 => 40,
        L_2048 => 56,
        L_3072 => 64,
        _ => panic!("invalid L bit length"),
    }
}

/// Generate probablistic primes according to FIPS 186-4 A.1.1.2
///
/// L and N lengths must be approved pairs according to FIPS 186-4
/// seed_len is the bit length of the domain parameter seed
/// seed_len valid range: N <= seed_len <= L, and must be a multiple of 8-bits
///
/// Note: seed_len upper limit, and being an even multiple of 8-bits is an implementation choice
pub fn generate_prob_primes(
    l_len: u32,
    n_len: u32,
    seed_len: u32,
    parameter_validation: ParameterValidation,
    rng: &mut ThreadRng,
) -> Result<DsaPrimes, Error> {
    check_dsa_ln(l_len, n_len)?;

    if seed_len < n_len || seed_len > l_len || seed_len % 8 != 0 {
        return Err(Error::InvalidSeedLen);
    }

    let seed_byte_len = (seed_len / 8) as usize;
    // let outlen be the bit length of the output block
    let out_len = (sha256::DIGEST_LEN * 8) as u32;

    // 3. n = ceil(L/outlen)-1
    let n = ((l_len as f64 / out_len as f64).ceil() - 1_f64) as u32;

    // 4. b = L - 1 - (n * outlen)
    let b = l_len - 1 - (n * out_len);

    let mut domain_seed: Vec<u8> = Vec::with_capacity(seed_byte_len);
    domain_seed.resize(seed_byte_len, 0);

    let two = BigUint::from(2_u8);
    let two_n_1 = two.pow(n_len - 1);
    let two_l_1 = two.pow(l_len - 1);
    let two_b = two.pow(b as u32);
    let two_seed_len = two.pow(seed_len as u32);

    let mr_rounds = miller_rabin_rounds(l_len);

    loop {
        // 5. Get an arbitrary sequence of seedlen bits as the domain_parameter_seed
        rng.fill(domain_seed.as_mut_slice());
        domain_seed[0] |= 0x80;

        // 6. U = Hash(domain_parameter_seed) mod 2**(N-1)
        let u_bytes = sha256::Sha256::digest(&domain_seed).map_err(|e| Error::Sha256(e))?;
        let u = BigUint::from_bytes_be(u_bytes.as_ref()).mod_floor(&two_n_1);

        // 7. q = 2**(N-1) + U + 1 - (U mod 2)
        let q = (&two_n_1 + &u) + 1_u32 - u.mod_floor(&two);

        // 8. Test whether or not q is prime as specified in Appendix C.3
        if !is_prime(&q, mr_rounds, n_len as usize, rng) {
            // 9. If q is not a prime, then go to step 5
            continue;
        }

        // 10. offset = 1
        let mut offset = 1;
        let mut counter = 0;
        let two_q = &q * 2_u32;

        // 11. for counter = 0 to (4L - 1) do
        let seed = BigUint::from_bytes_be(&domain_seed);
        while counter < 4 * l_len {
            let mut x = BigUint::from(0_u8);
            // 11.1 For j = 0 to n do
            for j in 0..=n {
                // V[j] = Hash(domain_parameter_seed + offset + j) mod 2**seedlen)
                let v_in = (&seed + (offset + j))
                    .mod_floor(&two_seed_len)
                    .to_bytes_be();
                let v_j_bytes = sha256::Sha256::digest(&v_in).map_err(|e| Error::Sha256(e))?;
                let v_j = BigUint::from_bytes_be(v_j_bytes.as_ref());
                // 11.2
                // W = V[0] + (V[1] * 2**outlen) + ... + (V[n-1] * 2**((n-1)*outlen))
                //   + ((V[n] mod 2**b) * 2**(n*outlen))
                x += two.pow(j * out_len) * if j != n { v_j } else { v_j.mod_floor(&two_b) };
            }
            assert!(
                x < two_l_1,
                "W >= 2**L-1, counter: {}, offset: {}",
                counter,
                offset
            );
            // 11.3 X = W + 2**(L-1) Comment: 0 <= W < 2**(L-1); hence, 2**(L-1) <= X < 2**L
            x += &two_l_1;

            // 11.4 c = X mod 2q
            let c = x.mod_floor(&two_q);

            // 11.5 p = X - (c - 1) Comment: p == 1 mod 2q
            let p = x - (c - 1_u32);

            // 11.6 if (p < 2**(L-1), then go to step 11.9
            if p >= two_l_1 {
                // 11.7 Test whether or not p is prime as specified in Appendix C.3
                if is_prime(&p, mr_rounds, l_len as usize, rng) {
                    // 11.8 If p is determined to be prime, then return VALID and the values of
                    // p, q and (optionally) the values of domain_parameter_seed and counter
                    let (seed, count) = match parameter_validation {
                        ParameterValidation::Save => (Some(seed), Some(counter as u32)),
                        ParameterValidation::Discard => (None, None),
                    };
                    return Ok(DsaPrimes {
                        p: p,
                        q: q,
                        seed: seed,
                        counter: count,
                    });
                }
            }
            // 11.9 offset = offset + n + 1
            // Comment: Increment offset; then as part of the loop in step 11,
            // increment counter; if counter < 4L repeat steps 11.1 through 11.8
            offset += n + 1;
            counter += 1;
        }
        // 12. Go to step 5
    }
}

/// Validate probabilistic primes according to FIPS 186-4 A.1.1.3
pub fn validate_prob_primes(primes: &DsaPrimes, rng: &mut ThreadRng) -> Result<(), Error> {
    if primes.seed.is_none() || primes.counter.is_none() {
        return Err(Error::InvalidPrime);
    }

    let (seed, counter) = match (&primes.seed, primes.counter) {
        (Some(ref s), Some(c)) => (s.clone(), c),
        (_, None) => return Err(Error::InvalidPrime),
        (None, _) => return Err(Error::InvalidPrime),
    };

    // 1. L = len(p)
    let l_len = primes.p.bits() as u32;
    // 2. N = len(q)
    let n_len = primes.q.bits() as u32;
    // 3. Check that the (L, N) pair is in the list of acceptable (L,N) pairs (see section 4.2).
    check_dsa_ln(l_len, n_len)?;

    // 4. If (counter > (4L - 1)), then return INVALID
    if counter > (4 * l_len) - 1 {
        return Err(Error::InvalidPrime);
    }

    // 5. seedlen = len(domain_parameter_seed)
    let seed_len = seed.bits() as u32;

    // 6. If (seedlen < N), then return INVALID
    if seed_len < n_len {
        return Err(Error::InvalidPrime);
    }

    // 7. U = Hash(domain_parameter_seed) mod 2**(N-1)
    let two = BigUint::from(2_u8);
    let two_n_1 = two.pow(n_len - 1);
    let u_bytes = sha256::Sha256::digest(&seed.to_bytes_be()).map_err(|_| Error::InvalidPrime)?;
    let u = BigUint::from_bytes_be(&u_bytes).mod_floor(&two_n_1);

    // 8. computed_q = 2**(N-1) + U + 1 - (U mod 2)
    let computed_q = &two_n_1 + &u + 1_u32 - u.mod_floor(&two);
    let mr_rounds = miller_rabin_rounds(l_len);

    // 9. Test whether or not q is prime as specified in Appendix C.3.
    // If (computed_q != q) or (computed_q is not prime), then return INVALID
    let mut comp_prime = is_prime(&computed_q, mr_rounds, n_len as usize, rng);
    let mut comp_eq = computed_q == primes.q;
    if !comp_prime || !comp_eq {
        return Err(Error::InvalidPrime);
    }

    let two_seed_len = two.pow(seed_len);
    let two_q = &primes.q * 2_u32;
    let two_l_1 = two.pow(l_len - 1);
    let out_len = (sha256::DIGEST_LEN * 8) as u32;

    // 10. n = ceil(L / outlen) - 1
    let n = ((l_len as f64 / out_len as f64).ceil() - 1_f64) as u32;
    // 11. b = L - 1 - (n * out_len)
    let b = l_len - 1 - (n * out_len);
    // 12. offset = 1
    let mut offset = 1;

    let two_b = two.pow(b);
    comp_prime = false;
    comp_eq = false;
    let mut i_eq = false;

    // 13. For i = 0 to counter do
    for i in 0..=counter {
        let mut x = BigUint::from(0_u8);
        // 13.1 For j = 0 to n do
        for j in 0..=n {
            // Vj = Hash((domain_parameter_seed + offset + j) mod 2**seedlen)
            let v_in = (&seed + (offset + j))
                .mod_floor(&two_seed_len)
                .to_bytes_be();
            let v_j_bytes = sha256::Sha256::digest(&v_in).map_err(|_| Error::InvalidPrime)?;
            let v_j = BigUint::from_bytes_be(v_j_bytes.as_ref());
            // 13.2
            // W = V[0] + (V[1] * 2**outlen) + ... + (V[n-1] * 2**((n-1)*outlen))
            //   + ((V[n] mod 2**b) * 2**(n*outlen))
            x += two.pow(j * out_len) * if j != n { v_j } else { v_j.mod_floor(&two_b) };
        }
        assert!(
            x < two_l_1,
            "W >= 2**L-1, counter: {}, offset: {}",
            counter,
            offset
        );
        // 13.3 X = W + 2**(L-1)
        x += &two_l_1;
        // 13.4 c = X mod 2q
        let c = x.mod_floor(&two_q);
        // 13.5 computed_p = X - (c - 1)
        let computed_p = &x - (&c - 1_u32);
        // 13.6 If (computed_p < 2**L-1), then go to step 13.9
        if computed_p > two_l_1 {
            // 13.7 Test whether or not computed_p is prime as specified in Appendix C.3
            comp_prime = is_prime(&computed_p, mr_rounds, l_len as usize, rng);
            // 13.8 If computed_p is determined to be a prime, then go to step 14
            if comp_prime {
                i_eq = i == counter;
                comp_eq = computed_p == primes.p;
                break;
            }
        }
        // 13.9 offset = offset + n + 1
        offset += n + 1;
    }
    // 14. If ((i != counter) or (computed_p != p) or (computed_p is not a prime)),
    //     then return INVALID
    if !i_eq || !comp_eq || !comp_prime {
        return Err(Error::InvalidPrime);
    }
    // 15. Return VALID
    Ok(())
}

/// Generate the G parameter using the unverifiable method from FIPS 186-4 A.2.1
///
/// Useful when full verification is not needed, or possible (e.g. paraemeters generated by a trusted party)
pub fn generate_unverifiable_g(primes: &DsaPrimes) -> Result<BigUint, Error> {
    let p_1 = &primes.p - 1_u32;
    // 1. e = (p - 1) / q
    let e = &p_1 / &primes.q;

    // 2. Set h = any integer satisfying 1 < h < (p - 1)
    let mut h = BigUint::from(2_u8);
    let one = BigUint::from(1_u8);

    while h < p_1 {
        // 3. g = h**e mod p
        let g = h.modpow(&e, &primes.p);
        if g == one {
            // 4. If (g = 1), then go to step 2.
            h += 1_u8;
        } else {
            return Ok(g);
        }
    }

    // No valid h was found to produce a valid G
    Err(Error::InvalidPrime)
}

/// Partially verify the G parameter according to FIPS 186-4 A.2.2
pub fn partial_verify_g(primes: &DsaPrimes, g: &BigUint) -> Result<(), Error> {
    // 1. Verify that 2 <= g <= (p-1). If not true, return INVALID
    if g < &BigUint::from(2_u8) || g >= &primes.p {
        return Err(Error::InvalidPrime);
    }
    // 2. If (g**q = 1 mod p), then return PARTIALLY VALID
    if g.modpow(&primes.q, &primes.p) == BigUint::from(1_u8) {
        Ok(())
    } else {
        // 3. Return INVALID
        Err(Error::InvalidPrime)
    }
}

/// Generate the G parameter using the canonical method from FIPS 186-4 A.2.3
///
/// Index is used for generating G, and can be used for key separation using the same primes
///
/// The domain_parameter_seed must be available from prime generation
pub fn generate_canonical_g(primes: &DsaPrimes, index: u8) -> Result<BigUint, Error> {
    let seed = match &primes.seed {
        Some(ref s) => s.clone(),
        None => return Err(Error::InvalidPrime),
    };

    // 1. If (index is incorrect), then return INVALID.
    // Not possible given this implementation, `index` is always an 8-bit bit string
    // 2. N = len(q) (unused)
    // 3. e = (p - 1)/q
    let e = (&primes.p - 1_u32) / &primes.q;

    let mut u_bytes = seed.to_bytes_be();
    let seed_len = u_bytes.len();
    u_bytes.resize(seed_len + GGEN_U_LEN, 0);
    u_bytes[seed_len..seed_len + 4].copy_from_slice(GGEN.as_ref());
    u_bytes[seed_len + 4] = index;

    let two = BigUint::from(2_u8);

    // Note: count is an unsigned 16-bit integer
    // 4. count = 0
    // 5. count = count += 1
    for count in 1..=u16::MAX {
        // 7. U = domain_parameter_seed || "ggen" || index || count
        u_bytes[seed_len + 5..seed_len + GGEN_U_LEN].copy_from_slice(count.to_be_bytes().as_ref());
        // 8. W = Hash(U)
        let w_bytes = sha256::Sha256::digest(&u_bytes).map_err(|_| Error::InvalidPrime)?;
        let w = BigUint::from_bytes_be(w_bytes.as_ref());
        // 9. g = W**e mod p
        let g = w.modpow(&e, &primes.p);
        if g >= two {
            // 11. Return VALID and the value of g
            return Ok(g);
        }
        // 10. if (g < 2), then go to step 5
    }
    // 6. If (count = 0), then return INVALID
    // In this implementation, once count reaches u16::MAX, the loop ends, return INVALID
    Err(Error::InvalidPrime)
}

/// Validate the G parameter using the canonical method from FIPS 186-4 A.2.4
///
/// Index is used for generating G, and can be used for key separation using the same primes
///
/// The domain_parameter_seed must be available from prime generation
pub fn validate_canonical_g(primes: &DsaPrimes, g: &BigUint, index: u8) -> Result<(), Error> {
    let seed = match &primes.seed {
        Some(ref s) => s.clone(),
        None => return Err(Error::InvalidPrime),
    };

    // 1. If (index is incorrect), then return INVALID.
    // Not possible given this implementation, `index` is always an 8-bit bit string

    // 2. Verify that 2 <= g <= (p-1). If not true, return INVALID
    let two = BigUint::from(2_u8);
    let p_1 = &primes.p - 1_u32;
    if g < &two || g > &p_1 {
        return Err(Error::InvalidPrime);
    }

    // 3. If (g**q != 1 mod p), then return INVALID
    if g.modpow(&primes.q, &primes.p) != BigUint::from(1_u8) {
        return Err(Error::InvalidPrime);
    }

    // 4. N = len(q) (unused)
    // 5. e = (p-1)/q
    let e = &p_1 / &primes.q;

    let mut u_bytes = seed.to_bytes_be();
    let seed_len = u_bytes.len();
    u_bytes.resize(seed_len + GGEN_U_LEN, 0);
    u_bytes[seed_len..seed_len + 4].copy_from_slice(GGEN.as_ref());
    u_bytes[seed_len + 4] = index;

    // 6. count = 0
    // 7. count = count+1
    for count in 1..=u16::MAX {
        // 9. U = domain_paramet_seed || "ggen" || index || count
        u_bytes[seed_len + 5..seed_len + GGEN_U_LEN].copy_from_slice(count.to_be_bytes().as_ref());
        // 10. W = Hash(U)
        let w_bytes = sha256::Sha256::digest(&u_bytes).map_err(|_| Error::InvalidPrime)?;
        let w = BigUint::from_bytes_be(w_bytes.as_ref());
        // 11. computed_g = W**e mod p
        let computed_g = w.modpow(&e, &primes.p);
        if computed_g < two {
            // 12. if (g < 2), then go to step 7
            continue;
        } else if &computed_g == g {
            // 13. Return VALID
            return Ok(());
        } else {
            return Err(Error::InvalidPrime);
        }
    }
    // 8. If (count = 0), then return INVALID
    // In this implementation, once count reaches u16::MAX, the loop ends, return INVALID
    Err(Error::InvalidPrime)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::N_160;
    use rand::thread_rng;

    #[test]
    fn check_valid_prob_primes() {
        let mut rng = thread_rng();
        let dsa_primes = generate_prob_primes(
            L_1024 as u32,
            N_160 as u32,
            N_160 as u32,
            ParameterValidation::Save,
            &mut rng,
        )
        .unwrap();
        validate_prob_primes(&dsa_primes, &mut rng).unwrap();
    }

    #[test]
    fn check_unverifiable_g() {
        let mut rng = thread_rng();
        let dsa_primes = generate_prob_primes(
            L_1024 as u32,
            N_160 as u32,
            N_160 as u32,
            ParameterValidation::Discard,
            &mut rng,
        )
        .unwrap();
        let g = generate_unverifiable_g(&dsa_primes).unwrap();
        partial_verify_g(&dsa_primes, &g).unwrap();
    }

    #[test]
    fn check_canonical_g() {
        let mut rng = thread_rng();
        let dsa_primes = generate_prob_primes(
            L_1024 as u32,
            N_160 as u32,
            N_160 as u32,
            ParameterValidation::Save,
            &mut rng,
        )
        .unwrap();
        let index = 0;
        let g = generate_canonical_g(&dsa_primes, index).unwrap();
        validate_canonical_g(&dsa_primes, &g, index).unwrap();
    }
}
