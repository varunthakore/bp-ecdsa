# bp-ecdsa

_ECDSA using secp256k1_

## Overview
This repository contains R1CS cicuit for ECDSA signature verification using secp256k1. The files are as follows:
* [`curve.rs`](./src/curve.rs): Implementation of circuits for secp256k1 curve operations
* [`ecdsa.rs`](./src/ecdsa.rs): Implementation of sinature verification circuit
* [`utils.rs`](./src/utils.rs): Contains utility functions used to implement curve operations

## Build

Clone the repository and run the following commands:
```bash
cd bp-ecdsa/
cargo build --release
```

## Tests

To run the tests:
```bash
cargo test --release
```

To run a specific test, specify it's name as follows:
```bash
cargo test [name_of_test] --release -- --nocapture
```

## References
1. [spartan-ecdsa by Personae Labs](https://github.com/personaelabs/spartan-ecdsa)
2. [Efficient ECDSA & the case for client-side proving by Personae Labs](https://personaelabs.org/posts/efficient-ecdsa-1/)
3. [Introducing Spartan-ecdsa by Personae Labs](https://personaelabs.org/posts/spartan-ecdsa/) 
