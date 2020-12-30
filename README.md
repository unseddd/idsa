# iDSA: the (inecure) DSA Algorithm

This is a largely untested, hopefully correct version of the DSA algorithm based on [FIPS 186-4](https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.186-4.pdf).

Any mistakes are my own, all credit to the original authors of the standard and algorithm.

# WARNING: CONTAINS CRYPTOGRAPHIC CODE UNTESTED BY THE CRYPTOGRAPHIC COMMUNITY

Cryptographic libraries should always go through rigorous review and testing by relevant experts before seeing practical use.

This library has received *neither* of those.

I have done my best to implement and test the algorithm to ensure correctness, but this library is purely to learn about how DSA actually works.

*Please* do not use this library for anything besides toy/educational purposes.

# Testing the library

Because some unit tests generate large primes, they can take a very long time in debug mode.

## Test in debug mode:

```
cargo test
```

## Test in release mode:

```
cargo test --release
```
