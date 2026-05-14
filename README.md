# 🌳 Kotzig–Ringel–Rosa (KRR) Conjecture

<p align="center">
  <img src="images/logo.png" width="120" alt="KRR Logo">
</p>

<p align="center">
  <b>Formal Verification of the Graceful Tree Conjecture in Lean 4</b><br/>
  <i>A rigorous verification effort based on the functional reformulation by Gnang (2022).</i>
</p>

<p align="center">
  <a href="https://github.com/Doublew08/KRR/actions"><img src="https://github.com/Doublew08/KRR/actions/workflows/lean_action_ci.yml/badge.svg" alt="CI Status"></a>
  <img src="https://img.shields.io/badge/Lean-4.29.1-blue" alt="Lean Version">
  <img src="https://img.shields.io/badge/Mathlib-v4.29.1-purple" alt="Mathlib Version">
  <img src="https://img.shields.io/badge/sorry%20count-10%20remaining-orange" alt="Sorry Count">
</p>

---

## 🏛️ Project Principles

- **Strict "No-Sorry" Mandate**: No code is merged into `master` unless every lemma is fully verified. We prioritize logical integrity over rapid scaffolding.
- **Mathlib-Native Design**: We leverage `Mathlib.Combinatorics.SimpleGraph`, `Mathlib.Data.MvPolynomial`, and `Mathlib.GroupTheory.Perm.Basic` to ensure our proofs are idiomatic and extensible.
- **Functional Clarity**: We model trees as endofunctions $\mathbb{Z}_n \to \mathbb{Z}_n$, providing a unique algebraic lens on a classical graph theory problem.

## 🧬 Proof Architecture

This project follows a 7-phase verification roadmap, driving any tree toward a star tree via functional composition.

```mermaid
graph TD
    A["Basic.lean<br/>Transformation Monoids"] --> B["Graceful.lean<br/>Star Tree Anchor"]
    B --> C["Combinatorics.lean<br/>Permutation Counting"]
    C --> D["GracefulExpansion.lean<br/>Algebraic Expansion"]
    D --> E["Polynomial.lean<br/>Determinantal Machinery"]
    E --> F["CompositionLemma.lean<br/>Iterative Descent"]
    F --> G["MainTheorem.lean<br/>KRR Conjecture ✓"]
```

## 📜 Key Formalized Statements

### The KRR Conjecture
The final goal of this project is the formal proof that every tree admits a graceful labeling.
```lean
theorem KRR_Conjecture (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] :
    G.IsTree → IsGraceful G
```

### The Functional Bridge
We bridge the functional model to classical graph theory, proving that our algebraic conditions are equivalent to the graph-theoretic ones.
```lean
theorem isGraceful_bridge (f : Fin n → Fin n) (h_tree : IsTreeFunction f) :
    isGraceful'' f ↔ G.IsGraceful 
```

## 📊 Verification Status

| Phase | Module | Status | Core Achievement |
| :---: | :--- | :---: | :--- |
| 1 | `Basic.lean` | ✅ Verified | **100% Verified**. Transformation monoids & digraph induction. |
| 2 | `Graceful.lean` | ✅ Verified | **Star Case Anchor**. Proved star trees are graceful. |
| 3 | `Combinatorics.lean` | ✅ Verified | **Isomorphism Bridge**. Verified permutation count $n! \cdot (n-1)!$. |
| 4 | `Expansion.lean` | 🔲 Scaffolded | Expansion formula for the determinantal polynomial. |
| 5 | `Polynomial.lean` | ✅ Verified | **Monomial Lemma**. Non-zero guarantee for tree indicators. |
| 6 | `Composition.lean` | 🚧 In Progress | **$n=2$ Base Case**. Composition preserves complexity. |
| 7 | `MainTheorem.lean` | 🔲 Scaffolded | Final Inductive synthesis. |

## 🛠️ Usage

### Prerequisites
- Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) via `elan`.
- Ensure you have `lake` (Lean build system) available.

### Installation & Build
```bash
# Clone the repository
git clone https://github.com/Doublew08/KRR.git
cd KRR

# Download precompiled Mathlib binaries (Highly Recommended)
lake exe cache get

# Build the entire project
lake build
```

## 🤝 Community & Contributing

We coordinate discussions on the **Lean Zulip Chat**. If you are interested in formalizing specific combinatorial bounds or algebraic expansions, please reach out!

- **Source Material**: [Gnang, E. K. (2022). *A proof of the Kotzig–Ringel–Rosa Conjecture*](https://arxiv.org/abs/2202.03178).
- **License**: Apache 2.0.

---
<p align="center">
  <i>"A tree is a function that eventually forgets everything but its root."</i>
</p>
