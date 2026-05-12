# Kotzig–Ringel–Rosa (KRR) Conjecture Formalization in Lean 4

This project aims to provide a complete formalization of the proof of the **Kotzig–Ringel–Rosa (KRR) Conjecture** (also known as the **Graceful Tree Conjecture**) as presented in the paper [*"A proof of the Kotzig–Ringel–Rosa Conjecture"*](https://arxiv.org/abs/2202.03178) by Edinah K. Gnang.

The conjecture states that every tree has a graceful labeling. This project formalizes the mathematical foundations, the functional reformulation of the labeling problem, and the verification of the labeling construction described in the proof using the Lean 4 theorem prover.

## Project Roadmap

The formalization is divided into 7 key phases, following the logical structure of the Gnang proof:

1.  **Phase 1: Foundations** (`Basic.lean`) — ℤₙ^ℤₙ transformation monoid and functional digraphs.
2.  **Phase 2: Graceful Labeling** (`Graceful.lean`) — Formal definitions of graceful graph labelings.
3.  **Phase 3: Functional Reformulation** (`FunctionalReformulation.lean`) — Bridging trees to endofunctions.
4.  **Phase 4: Graceful Expansion** (`GracefulExpansion.lean`) — Theorem 2.1: The core algebraic tool.
5.  **Phase 5: Polynomial Machinery** (`Polynomial.lean`) — Multivariate polynomial and determinantal constructions.
6.  **Phase 6: Composition Lemma** (`CompositionLemma.lean`) — The critical contradiction argument.
7.  **Phase 7: Main Theorem** (`MainTheorem.lean`) — Final assembly of the KRR Conjecture proof.

## Current Status

- [x] Initial project structure and mathlib integration.
- [x] Detailed implementation plan (7 phases).
- [x] Repository initialization and GitHub Sync.
- [/] **Phase 1: Foundations** (In Progress)
- [ ] Phase 2: Graceful Labeling
- [ ] Phase 3: Functional Reformulation
- [ ] Phase 4: Graceful Expansion Theorem
- [ ] Phase 5: Polynomial Machinery
- [ ] Phase 6: Composition Lemma
- [ ] Phase 7: Main Theorem

## Project Structure

```text
KRR/
├── Basic.lean                      # Foundation: ℤₙ^ℤₙ, functional digraphs
├── Graceful.lean                   # Graceful labeling definitions  
├── FunctionalReformulation.lean    # Trees ↔ endofunctions, τ-Zen
├── GracefulExpansion.lean          # Graceful expansion theorem
├── TransformationMonoid.lean       # Bounds on edge label counts
├── CompositionLemma.lean           # The critical composition lemma
├── MainTheorem.lean                # Final KRR Conjecture proof
└── Polynomial.lean                 # Polynomial/determinant machinery
```

## Getting Started

### Prerequisites

1.  **Lean 4**: Ensure you have Lean 4 installed via `elan`.
    ```powershell
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    ```
2.  **Visual Studio Code**: Use VS Code with the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).

### Building the Project

```powershell
lake build
```

## References

*   Gnang, E. K. (2022). *A proof of the Kotzig–Ringel–Rosa Conjecture*. [arXiv:2202.03178](https://arxiv.org/abs/2202.03178).

## License

This project is licensed under the Apache License 2.0.
