# KZG-FRI Polynomial Commitment Schemes

A Rust implementation comparing KZG and FRI polynomial commitment schemes.

## Overview

This project implements two different polynomial commitment schemes:

- **KZG (Kate-Zaverucha-Goldberg)**: Requires trusted setup, uses elliptic curve pairings
- **FRI (Fast Reed-Solomon Interactive Oracle Proof)**: Transparent (no trusted setup), uses Merkle trees

## Features

- KZG polynomial commitments with BLS12-381 curve
- FRI protocol with configurable blowup factor
- Separate prover/verifier implementations
- Performance benchmarks for both schemes

## Usage

```bash
# Run examples and benchmarks
cargo run --release

# Run tests
cargo test
```

## Key Differences

| Feature | KZG | FRI |
|---------|-----|-----|
| Trusted Setup | Required | Not required |
| Proof Size | Constant (1 group element) | Logarithmic |
| Verification Time | Constant | Logarithmic |
| Post-quantum | No | Yes |

## Dependencies

- `bls12_381` - BLS12-381 elliptic curve operations
- `ff` - Finite field arithmetic
- `group` - Elliptic curve group operations
- `rand` - Random number generation

## License

MIT