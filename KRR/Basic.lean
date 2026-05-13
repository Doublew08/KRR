import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Function.Iterate
import Mathlib.GroupTheory.Perm.Basic


/-!
# KRR Foundations: Transformation Monoid and Functional Digraphs

This module defines the basic structures for the Kotzig–Ringel–Rosa (KRR) formalization.
We model the transformation monoid ℤₙ^ℤₙ as endofunctions `Fin n → Fin n` and
define the associated functional directed graphs using `Digraph`.

## Main definitions

* `FunctionalDigraph` — the digraph of an endofunction where vertex `i` has edge to `f(i)`
* `IsTreeFunction` — predicate: `f` has a unique fixed point attractive over the domain
* `fixedPointSet` — the set of fixed points of `f`
* `iterateImage` — the image of `f^(k)` applied to the full domain

## References

* [Gnang, *A proof of the Kotzig–Ringel–Rosa Conjecture*][arXiv:2202.03178]
-/

namespace KRR

variable {n : ℕ}

/-- The functional directed graph of `f : Fin n → Fin n`.
Every vertex `i` has exactly one outgoing edge to `f(i)`. -/
def FunctionalDigraph (f : Fin n → Fin n) : Digraph (Fin n) where
  Adj u v := v = f u

/-- The set of fixed points of an endofunction `f`. -/
def fixedPointSet (f : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => f i = i)

/-- The image of `f^(k)` applied to the full domain. -/
def iterateImage (f : Fin n → Fin n) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.image (f^[k])

/-- A function `f : Fin n → Fin n` is a "tree function" if iterating it `(n-1)` times
on every element collapses everything to a single fixed point.
This corresponds to the paper's condition `|f^(n-1)(ℤₙ)| = 1`. -/
def IsTreeFunction (f : Fin n → Fin n) : Prop :=
  (iterateImage f (n - 1)).card = 1

/-- Two endofunctions differ by fixed point swaps if their underlying undirected edge sets
(excluding self-loops) are identical. This is Definition 2.4 from the paper. -/
def DifferByFixedPointSwaps (f g : Fin n → Fin n) : Prop :=
  (Finset.univ.filter (fun i => f i ≠ i)).image (fun i => ({i, f i} : Finset (Fin n))) =
  (Finset.univ.filter (fun i => g i ≠ i)).image (fun i => ({i, g i} : Finset (Fin n)))

/-- The number of distinct absolute subtractive edge labels for a specific relabeling `σ`.
This is `|{|σfσ⁻¹(i) - i| : i ∈ ℤₙ}|`. -/
def distinctEdgeLabelsCount (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.image (fun i : Fin n =>
    Int.natAbs ((σ (f (σ.symm i))).val - i.val))).card

/-- `IsMaxDistinctEdgeLabels f k` means `k` is the maximum number of distinct
absolute subtractive edge labels achievable by any relabeling of `f`.
This is `max_σ |{|σfσ⁻¹(i) - i| : i ∈ ℤₙ}| = k` from the paper. -/
def IsMaxDistinctEdgeLabels (f : Fin n → Fin n) (k : ℕ) : Prop :=
  (∃ σ : Equiv.Perm (Fin n), distinctEdgeLabelsCount f σ = k) ∧
  (∀ σ : Equiv.Perm (Fin n), distinctEdgeLabelsCount f σ ≤ k)

/-- The semigroup of "canonical" tree functions:
`{h ∈ ℤₙ^ℤₙ : h(0) = 0 ∧ h(i) < i, ∀ i > 0}`.
The paper uses this as WLOG for the Composition Lemma. -/
def IsCanonicalTreeFunction (hn : 0 < n) (f : Fin n → Fin n) : Prop :=
  f ⟨0, hn⟩ = ⟨0, hn⟩ ∧
  ∀ i : Fin n, i.val > 0 → (f i).val < i.val

/-- The diameter of the functional digraph. 
Placeholder for the actual graph-theoretic diameter. -/
def funcDiameter (_f : Fin n → Fin n) : ℕ := 0 -- Placeholder to fix build

end KRR
