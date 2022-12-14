# A Generic Methodology for the Modular Verification of Security Protocol Implementations

[![Reusable Verification Library](https://github.com/ModularVerification/SecurityProtocolImplementations/actions/workflows/library.yml/badge.svg?branch=main)](https://github.com/ModularVerification/SecurityProtocolImplementations/actions/workflows/library.yml?query=branch%3Amain)
[![Verification of Reusable Verification Library for VeriFast](https://github.com/ModularVerification/SecurityProtocolImplementations/actions/workflows/verifast.yml/badge.svg?branch=main)](https://github.com/ModularVerification/SecurityProtocolImplementations/actions/workflows/verifast.yml?query=branch%3Amain)
[![NSL Case Study](https://github.com/ModularVerification/SecurityProtocolImplementations/actions/workflows/nsl.yml/badge.svg?branch=main)](https://github.com/ModularVerification/SecurityProtocolImplementations/actions/workflows/nsl.yml?query=branch%3Amain)
[![WireGuard Case Study](https://github.com/ModularVerification/SecurityProtocolImplementations/actions/workflows/wireguard.yml/badge.svg?branch=main)](https://github.com/ModularVerification/SecurityProtocolImplementations/actions/workflows/wireguard.yml?query=branch%3Amain)


## Structure
- `ReusableVerificationLibrary` contains the Gobra sources that constitute the Reusable Verification Library
- `casestudies/nsl` contains the sources of the NSL case study. The implementation consists of separate packages for the initiator, initiator2 (using a slightly different code structure), and responder role. The main package sets up communication via Go channels and executes the two protocol roles as threads (using Goroutines)
- `casestudies/wireguard` contains the sources of the WireGuard case study. The role implementations are mainly located in the `initiator` and `responder` packages. The trace invariants are defined in `verification/common` and `verification/labellemma` contains the WireGuard-specific lemmas and their proofs.
- `VeriFastPrototype` contains the C sources of our prototype for VeriFast. The prototype demonstrates that (1) a concurrent data structure can be built on top of VeriFast's built-in mutex offering the same local snapshots as our Reusable Verification Library, (2) a parameterized trace invariant in the form of a separation logic predicate can be defined, and (3) several lemmas, such as the uniqueness of events or the secrecy lemma, can be proven using the trace invariant.
