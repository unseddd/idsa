#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use num::{BigUint, Integer};
use rand::rngs::ThreadRng;
use rand::{thread_rng, Rng};

use isha2::{sha256, Sha2};
use prime_math::InvMod;

mod parameters;

/// Utilities for generating and validation DSA parameters
pub use parameters::*;

#[derive(Debug)]
pub enum Error {
    Invalid,
    InvalidPrime,
    InvalidSeedLen,
    Sha256(isha2::Error),
}

/// DSA 1024-bits modulus length
pub const L_1024: u32 = 1024;

/// DSA 2048-bits modulus length
pub const L_2048: u32 = 2048;

/// DSA 3072-bits modulus length
pub const L_3072: u32 = 3072;

/// DSA 160-bit group size
pub const N_160: u32 = 160;

/// DSA 224-bit group size
pub const N_224: u32 = 224;

/// DSA 256-bit group size
pub const N_256: u32 = 256;

#[derive(PartialEq)]
pub enum Trusted {
    True,
    False,
}

/// DSA public key
#[derive(Clone)]
pub struct DsaPublicKey {
    p: BigUint,
    q: BigUint,
    g: BigUint,
    y: BigUint,
}

impl From<&DsaPrivateKey> for DsaPublicKey {
    fn from(key: &DsaPrivateKey) -> Self {
        Self {
            // assume domain parameters valid
            p: key.p.clone(),
            q: key.q.clone(),
            g: key.g.clone(),
            // FIPS 186-4 B.1.2 Step 8
            // y = g**x mod p
            y: key.g.modpow(&key.x, &key.p),
        }
    }
}

impl DsaPublicKey {
    /// Verify a signed message according to FIPS 186-4 4.7
    pub fn verify(&self, message: &[u8], r: &BigUint, s: &BigUint) -> Result<(), Error> {
        let zero = BigUint::from(0_u8);
        // 1. The verifier shall check that 0 < r' < q and 0 < s' < q;
        // if either is violated, the signature shall be rejected as invalid
        if r == &zero || r >= &self.q || s == &zero || s >= &self.q {
            return Err(Error::Invalid);
        }
        // 2. If the two conditions in step 1 are satisfied, the verifier computes the following:
        // w = s'**-1 mod q
        let w = s.invmod(&self.q);
        // z = the leftmost min(N, outlen) bits of Hash(M')
        let z_len = core::cmp::min(self.q.bits() / 8, sha256::DIGEST_LEN as u64);
        let z_bytes = sha256::Sha256::digest(message).map_err(|_| Error::Invalid)?;
        let z = BigUint::from_bytes_be(&z_bytes[..z_len as usize]);
        // u1 = (zw) mod q
        let u1 = (&z * &w).mod_floor(&self.q);
        // u2 = ((r')w) mod q
        let u2 = (r * &w).mod_floor(&self.q);
        // v = ((g**u1 * y**u2) mod p) mod q
        let v = (self.g.modpow(&u1, &self.p) * self.y.modpow(&u2, &self.p))
            .mod_floor(&self.p)
            .mod_floor(&self.q);
        // 3. If v = r', then the signature is verified
        //
        // 4. If v does not equal r', any number of things could have gone wrong. The only thing
        //    known is the signature is invalid.
        // 5. Prior to accepting the signature as valid, the verifier shall have the assurances as
        //    specified in Section 3.3
        constant_compare(&v, &r)
    }
    /// INSECURE Verify a signed message without checking parameter validity
    pub fn verify_insecure(&self, message: &[u8], r: &BigUint, s: &BigUint) -> Result<(), Error> {
        // 1. The verifier shall check that 0 < r' < q and 0 < s' < q;
        // if either is violated, the signature shall be rejected as invalid
        /* Don't need no stinking validity checks!
        let zero = BigUint::from(0_u8);
        if r == &zero || r >= &self.q || s == &zero || s >= &self.q {
            return Err(Error::Invalid);
        }
        */
        // 2. If the two conditions in step 1 are satisfied, the verifier computes the following:
        // w = s'**-1 mod q
        let w = s.invmod(&self.q);
        // z = the leftmost min(N, outlen) bits of Hash(M')
        let z_len = core::cmp::min(self.q.bits() / 8, sha256::DIGEST_LEN as u64);
        let z_bytes = sha256::Sha256::digest(message).map_err(|_| Error::Invalid)?;
        let z = BigUint::from_bytes_be(&z_bytes[..z_len as usize]);
        // u1 = (zw) mod q
        let u1 = (&z * &w).mod_floor(&self.q);
        // u2 = ((r')w) mod q
        let u2 = (r * &w).mod_floor(&self.q);
        // v = ((g**u1 * y**u2) mod p) mod q
        let v = (self.g.modpow(&u1, &self.p) * self.y.modpow(&u2, &self.p))
            .mod_floor(&self.p)
            .mod_floor(&self.q);
        // 3. If v = r', then the signature is verified
        //
        // 4. If v does not equal r', any number of things could have gone wrong. The only thing
        //    known is the signature is invalid.
        // 5. Prior to accepting the signature as valid, the verifier shall have the assurances as
        //    specified in Section 3.3
        constant_compare(&v, &r)
    }
}

/// Compare two BigUints in constant-time
///
/// Returns error if the lengths or contents are unequal
pub fn constant_compare(el: &BigUint, ar: &BigUint) -> Result<(), Error> {
    let el_bytes = el.to_bytes_le();
    let ar_bytes = ar.to_bytes_le();
    let el_len = el_bytes.len();
    let ar_len = ar_bytes.len();
    let len = core::cmp::min(el_len, ar_len);
    let mut res = 0_u8;
    // Compare whether the lengths are equal
    for (elb, arb) in el_len.to_le_bytes().iter().zip(ar_len.to_le_bytes().iter()) {
        res |= elb ^ arb;
    }
    // Compare whether the bytes making the BigUints are equal
    for (&e, &a) in el_bytes[..len].iter().zip(ar_bytes[..len].iter()) {
        res |= e ^ a;
    }
    if res == 0 {
        Ok(())
    } else {
        Err(Error::Invalid)
    }
}

/// DSA private key
pub struct DsaPrivateKey {
    pub(crate) p: BigUint,
    pub(crate) q: BigUint,
    pub(crate) g: BigUint,
    pub(crate) x: BigUint,
}

impl DsaPrivateKey {
    /// Create DsaPrivateKey from parameters according to FIPS 186-4 B.1.2
    ///
    /// Validates parameters if untrusted, skips validation otherwise
    /// If untrusted, supply optional g_index to validate g using canonical validation
    pub fn from_parameters(
        primes: DsaPrimes,
        g: BigUint,
        g_index: Option<u8>,
        trusted: Trusted,
        rng: &mut ThreadRng,
    ) -> Result<Self, Error> {
        if trusted != Trusted::True {
            validate_prob_primes(&primes, rng)?;
            match (&primes.seed, g_index) {
                (Some(_), Some(i)) => validate_canonical_g(&primes, &g, i)?,
                _ => partial_verify_g(&primes, &g)?,
            }
        }

        // 1. N = len(p); L = len(p)
        let n_len = primes.q.bits() as u32;
        let l_len = primes.p.bits() as u32;

        check_dsa_ln(l_len, n_len)?;

        let c_len = (n_len / 8) as usize;
        let mut c_bytes: Vec<u8> = Vec::with_capacity(c_len);
        c_bytes.resize(c_len, 0);

        let q_2 = &primes.q - 2_u32;

        // 3. requested_security_strength = the security strength associated with the (L,N) pair;
        // see SP 800-57
        //
        // TODO: verify internal ChaCha20-based PRNG in ThreadRng meets/exceeds SP 800-57 reqs.
        loop {
            // 4. Obtain a string of N returned bits from an RBG with a security strength of
            //    requested_security_strength or more.
            rng.fill(c_bytes.as_mut_slice());
            // ensure leading bit is set to produce an BigUint of the desired bit-length
            c_bytes[0] |= 0x80;
            // 5. Convert returned_bits to non-negative integer c
            let mut c = BigUint::from_bytes_be(&c_bytes);
            // 6. if (c > q-2), then go to step 4.
            if c > q_2 {
                continue;
            };
            // 7. x = c + 1
            c += 1_u32;
            return Ok(Self {
                p: primes.p,
                q: primes.q,
                g: g,
                x: c,
            });
        }
    }

    /// Generate per-message secret nonce according to FIPS 186-4 B.2.2
    fn generate_secret_nonce(&self, rng: &mut ThreadRng) -> Result<(BigUint, BigUint), Error> {
        // 1. N = len(q); L = len(p)
        let n_len = self.q.bits() as u32;
        let l_len = self.p.bits() as u32;
        // 2. If the (L, N) pair is invalid, then return an ERROR
        check_dsa_ln(l_len, n_len)?;

        // 3. requested_security_strength = the security strength associated with the (L,N) pair;
        // see SP 800-57
        //
        // TODO: verify internal ChaCha20-based PRNG in ThreadRng meets/exceeds SP 800-57 reqs.
        let c_len = (n_len / 8) as usize;
        let mut c_bytes: Vec<u8> = Vec::with_capacity(c_len);
        c_bytes.resize(c_len, 0);
        // ensure leading bit is set to produce an BigUint of the desired bit-length
        let q_2 = &self.q - 2_u32;
        loop {
            // 4. Obtain a string of N returned bits from an RBG with a security strength of
            //    requested_security_strength or more.
            rng.fill(c_bytes.as_mut_slice());
            // ensure leading bit is set to produce an BigUint of the desired bit-length
            c_bytes[0] |= 0x80;
            // 5. Convert returned_bits to the non-negative integer c
            let mut c = BigUint::from_bytes_be(&c_bytes);
            // 6. If (c > q-2), then go to step 4
            if c > q_2 {
                continue;
            };
            // 7. k = c + 1
            c += 1_u32;
            // 8. k**-1 = inverse(k, q)
            let c_inv = c.invmod(&self.q);
            // 9. Return k and k**-1
            return Ok((c, c_inv));
        }
    }

    /// Sign a message according to FIPS 186-4 4.6
    pub fn sign(&self, message: &[u8]) -> Result<(BigUint, BigUint), Error> {
        let mut rng = thread_rng();
        self.sign_inner(message, &mut rng)
    }

    fn sign_inner(&self, message: &[u8], rng: &mut ThreadRng) -> Result<(BigUint, BigUint), Error> {
        let zero = BigUint::from(0_u8);
        loop {
            let (k, k_inv) = self.generate_secret_nonce(rng)?;
            // r = (g**k mod p) mod q
            let r = self.g.modpow(&k, &self.p).mod_floor(&self.q);
            // z = the leftmost min(N, outlen) bits of Hash(M)
            let z_len = core::cmp::min(self.q.bits() / 8, sha256::DIGEST_LEN as u64);
            let z_bytes = sha256::Sha256::digest(message).map_err(|_| Error::Invalid)?;
            let z = BigUint::from_bytes_be(&z_bytes[..z_len as usize]);
            // s = (k**-1(z + xr)) mod q
            let s = (k_inv * (z + (&self.x * &r))).mod_floor(&self.q);
            // If either r = 0 or s = 0, a new value of k shall be generated, and the signature
            // shall be recalculated. It is extremely unlikely that r=0 or s=0 if signatures are
            // generated properly.
            if r == zero || s == zero {
                continue;
            };
            return Ok((r, s));
        }
    }

    /// INSECURE Return the secret nonce `k` with the signature as part of Cryptopals challenge #43
    pub fn sign_insecure(
        &self,
        message: &[u8],
        rng: &mut ThreadRng,
    ) -> Result<(BigUint, BigUint, BigUint), Error> {
        let zero = BigUint::from(0_u8);
        loop {
            let (k, k_inv) = self.generate_secret_nonce(rng)?;
            // r = (g**k mod p) mod q
            let r = self.g.modpow(&k, &self.p).mod_floor(&self.q);
            // z = the leftmost min(N, outlen) bits of Hash(M)
            let z_len = core::cmp::min(self.q.bits() / 8, sha256::DIGEST_LEN as u64);
            let z_bytes = sha256::Sha256::digest(message).map_err(|_| Error::Invalid)?;
            let z = BigUint::from_bytes_be(&z_bytes[..z_len as usize]);
            // s = (k**-1(z + xr)) mod q
            let s = (k_inv * (z + (&self.x * &r))).mod_floor(&self.q);
            // If either r = 0 or s = 0, a new value of k shall be generated, and the signature
            // shall be recalculated. It is extremely unlikely that r=0 or s=0 if signatures are
            // generated properly.
            if r == zero || s == zero {
                continue;
            };
            return Ok((r, s, k));
        }
    }

    /// INSECURE Sign the message with the provided secret nonce `k` as part of Cryptopals challenge #43
    pub fn sign_with_k_insecure(
        &self,
        message: &[u8],
        k: &BigUint,
    ) -> Result<(BigUint, BigUint), Error> {
        let k_inv = k.invmod(&self.q);
        // r = (g**k mod p) mod q
        let r = self.g.modpow(&k, &self.p).mod_floor(&self.q);
        // z = the leftmost min(N, outlen) bits of Hash(M)
        let z_len = core::cmp::min(self.q.bits() / 8, sha256::DIGEST_LEN as u64);
        let z_bytes = sha256::Sha256::digest(message).map_err(|_| Error::Invalid)?;
        let z = BigUint::from_bytes_be(&z_bytes[..z_len as usize]);
        // s = (k**-1(z + xr)) mod q
        let s = (k_inv * (z + (&self.x * &r))).mod_floor(&self.q);
        Ok((r, s))
    }

    /// Return the prime parameter `p`
    pub fn p(&self) -> &BigUint {
        &self.p
    }

    /// Return the prime parameter `q`
    pub fn q(&self) -> &BigUint {
        &self.q
    }

    /// Return the generator parameter `g`
    pub fn g(&self) -> &BigUint {
        &self.g
    }

    /// INSECURE Return the secret key `x`, used for Cryptopals challenge #43
    pub fn x(&self) -> &BigUint {
        &self.x
    }
}

fn check_dsa_ln(l: u32, n: u32) -> Result<(), Error> {
    match l {
        L_1024 => match n {
            N_160 => Ok(()),
            _ => Err(Error::Invalid),
        },
        L_2048 => match n {
            N_224 | N_256 => Ok(()),
            _ => Err(Error::Invalid),
        },
        L_3072 => match n {
            N_256 => Ok(()),
            _ => Err(Error::Invalid),
        },
        _ => Err(Error::Invalid),
    }
}

#[cfg(test)]
mod tests {
    use rand::thread_rng;

    use super::*;

    #[test]
    fn check_key_generation_trusted() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Discard, &mut rng)
                .unwrap();
        let g = generate_unverifiable_g(&primes).unwrap();
        let private_key =
            DsaPrivateKey::from_parameters(primes, g, None, Trusted::True, &mut rng).unwrap();
        let _ = DsaPublicKey::from(&private_key);
    }

    #[test]
    fn check_key_generation_untrusted() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();
        let private_key =
            DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng).unwrap();
        let _ = DsaPublicKey::from(&private_key);
    }

    #[test]
    fn check_key_generation_untrusted_2048_224() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_2048, N_224, N_224, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();
        let private_key =
            DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng).unwrap();
        let _ = DsaPublicKey::from(&private_key);
    }

    #[test]
    fn check_key_generation_untrusted_2048_256() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_2048, N_256, N_256, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();
        let private_key =
            DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng).unwrap();
        let _ = DsaPublicKey::from(&private_key);
    }

    #[test]
    fn check_key_generation_untrusted_3072() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_3072, N_256, N_256, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();
        let private_key =
            DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng).unwrap();
        let _ = DsaPublicKey::from(&private_key);
    }

    #[test]
    fn check_key_generation_invalid_p_untrusted() {
        let mut rng = thread_rng();
        let mut primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();

        // invalidate the prime p
        primes.p += 1_u32;
        let res = DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng);
        assert!(res.is_err());
    }

    #[test]
    fn check_key_generation_invalid_q_untrusted() {
        let mut rng = thread_rng();
        let mut primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();

        // invalidate the prime p
        primes.q += 1_u32;
        let res = DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng);
        assert!(res.is_err());
    }

    #[test]
    fn check_key_generation_invalid_domain_seed_untrusted() {
        let mut rng = thread_rng();
        let mut primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();

        // invalidate the domain_parameter_seed
        primes.seed = Some(primes.seed.unwrap() + 1_u32);
        let res = DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng);
        assert!(res.is_err());
    }

    #[test]
    fn check_key_generation_invalid_counter_untrusted() {
        let mut rng = thread_rng();
        let mut primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();

        // invalidate the domain_parameter_seed
        primes.counter = Some(primes.counter.unwrap() + 1_u32);
        let res = DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng);
        assert!(res.is_err());
    }

    #[test]
    fn check_key_generation_invalid_g_untrusted() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Save, &mut rng)
                .unwrap();
        let mut g = generate_canonical_g(&primes, 0).unwrap();

        // invalidate g
        g += 1_u32;
        let res = DsaPrivateKey::from_parameters(primes, g, Some(0), Trusted::False, &mut rng);
        assert!(res.is_err());
    }

    #[test]
    fn check_key_generation_invalid_g_index_untrusted() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Save, &mut rng)
                .unwrap();
        let g = generate_canonical_g(&primes, 0).unwrap();

        // provide invalid g_index
        let res = DsaPrivateKey::from_parameters(primes, g, Some(1), Trusted::False, &mut rng);
        assert!(res.is_err());
    }

    #[test]
    fn check_generate_secret_nonce() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Discard, &mut rng)
                .unwrap();
        let g = generate_unverifiable_g(&primes).unwrap();
        let private_key =
            DsaPrivateKey::from_parameters(primes, g, None, Trusted::True, &mut rng).unwrap();
        let (k, k_inv) = private_key.generate_secret_nonce(&mut rng).unwrap();
        let one = BigUint::from(1_u8);

        assert!(k <= &private_key.q - 1_u32);
        assert_eq!((k * k_inv).mod_floor(&private_key.q), one);
    }

    #[test]
    fn check_signature_and_verification() {
        let mut rng = thread_rng();
        let primes =
            generate_prob_primes(L_1024, N_160, N_160, ParameterValidation::Discard, &mut rng)
                .unwrap();
        let g = generate_unverifiable_g(&primes).unwrap();
        let private_key =
            DsaPrivateKey::from_parameters(primes, g, None, Trusted::True, &mut rng).unwrap();
        let public_key = DsaPublicKey::from(&private_key);
        let message = b"truly, many lies have been spoken about me.";
        let (r, s) = private_key.sign_inner(message.as_ref(), &mut rng).unwrap();
        public_key.verify(message.as_ref(), &r, &s).unwrap();
    }
}
