# Kotzig–Ringel–Rosa (KRR) Conjecture Formalization in Lean 4

This project provides a rigorous formalization and verification of the proof for the **Kotzig–Ringel–Rosa (KRR) Conjecture** (Graceful Tree Conjecture), based on the paper [*"A proof of the Kotzig–Ringel–Rosa Conjecture"*](https://arxiv.org/abs/2202.03178) by Edinah K. Gnang.

## Project Goal: Rigorous Verification

This is a **verification project**. We aim to stress-test the logical chain of the Gnang proof using the Lean 4 theorem prover. 

> [!IMPORTANT]
> **Constraint:** NO `sorry` placeholders are allowed in the final formalization. Every lemma and theorem must be fully proved to ensure the mathematical integrity of the result.

## Methodology: Functional Digraphs

Unlike standard graph theory projects that rely solely on undirected structures, this project adopts the paper's **Functional Reformulation**. We model trees as endofunctions $f: \mathbb{Z}_n \to \mathbb{Z}_n$ and leverage Mathlib's `Digraph` (directed graph) API. This allows us to use algebraic tools like the transformation monoid $\mathbb{Z}_n^{\mathbb{Z}_n}$ and function conjugation.

## Project Roadmap & Status

1.  **Phase 1: Foundations** (`Basic.lean`) — **[COMPLETE]**
    - ℤₙ^ℤₙ transformation monoid, `FunctionalDigraph` via Mathlib, `IsTreeFunction`.
2.  **Phase 2: Graceful Labeling** (`Graceful.lean`) — **[COMPLETE]**
    - Definitions for `edgeLabelSet`, conjugation by relabeling ($\sigma f \sigma^{-1}$), and a **rigorous proof** that constant-zero functions are already gracefully labeled.
3.  **Phase 3: Functional Reformulation** (`FunctionalReformulation.lean`) — **[IN PROGRESS]**
    - `IsValidPermutationBasis`, `signFunction`, and the count of valid bases.
4.  **Phase 4: Graceful Expansion** (`GracefulExpansion.lean`) — [PLANNED]
    - Theorem 2.1: The core algebraic tool.
5.  **Phase 5: Polynomial Machinery** (`Polynomial.lean`) — [PLANNED]
    - Multivariate polynomial and determinantal constructions.
6.  **Phase 6: Composition Lemma** (`CompositionLemma.lean`) — [PLANNED]
    - The critical contradiction argument.
7.  **Phase 7: Main Theorem** (`MainTheorem.lean`) — [PLANNED]
    - Final assembly of the KRR Conjecture proof.

## Current Build Status

- [x] Mathlib integration (`v4.29.1`).
- [x] Basic foundations and Digraph support.
- [x] Compilable scaffolding for Phases 1-3.
- [ ] Phase 3 Theorem Proofs.

## Build Instructions

```powershell
# Build the entire project
lake build KRR
```

## References

*   Gnang, E. K. (2022). *A proof of the Kotzig–Ringel–Rosa Conjecture*. [arXiv:2202.03178](https://arxiv.org/abs/2202.03178).

## License

This project is licensed under the Apache License 2.0.
