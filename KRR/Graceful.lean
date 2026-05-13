import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import KRR.Basic

/-!
# KRR Phase 2: Graceful Labeling

This module defines graceful labelings in two equivalent ways:
1. **Functional form** (primary): A relabeling `σ` of `f : Fin n → Fin n` is graceful
   if the induced absolute-difference edge labels are all distinct and cover `{0,...,n-1}`.
2. **SimpleGraph form** (final theorem statement): For bridging to Mathlib's `IsTree`.

The functional form is used throughout the proof. The SimpleGraph form is only
used in the final KRR theorem statement.

## Main definitions

* `KRR.IsGracefulRelabeling` — σfσ⁻¹ has n distinct edge labels
* `KRR.IsGracefulFunction` — some relabeling of f is graceful
* `KRR.starIsGraceful` — constant functions (stars) are graceful

## References

* [Gnang, *A proof of the Kotzig–Ringel–Rosa Conjecture*][arXiv:2202.03178]
-/

namespace KRR

variable {n : ℕ}

/-- The set of induced absolute subtractive edge labels for `f : Fin n → Fin n`.
This is `{|f(i) - i| : i ∈ ℤₙ}`, the set of absolute differences between
each vertex and its parent. -/
def edgeLabelSet (f : Fin n → Fin n) : Finset ℕ :=
  Finset.univ.image (fun i : Fin n => Int.natAbs ((f i).val - i.val))

/-- A function `f : Fin n → Fin n` is "already gracefully labeled" if the induced
absolute subtractive edge labels are all distinct, i.e. `|edgeLabelSet f| = n`. -/
def IsAlreadyGraceful (f : Fin n → Fin n) : Prop :=
  (edgeLabelSet f).card = n

/-- A relabeling `σ` of `f` produces `σ ∘ f ∘ σ⁻¹`, which is a conjugation by
a permutation. The functional digraph of `σfσ⁻¹` is isomorphic to that of `f`
but with relabeled vertices. -/
def conjugate (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n)) : Fin n → Fin n :=
  σ ∘ f ∘ σ.symm

/-- A function `f` is graceful if there exists a permutation `σ` such that
`σfσ⁻¹` has `n` distinct induced absolute subtractive edge labels.
This matches the paper's definition. -/
def IsGracefulFunction (f : Fin n → Fin n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), IsAlreadyGraceful (conjugate f σ)

/-- The complement map `φ(i) = (n-1) - i`. This captures the complementary
labeling symmetry from eq. (2.5) of the paper. -/
def complementMap (_hn : 0 < n) : Equiv.Perm (Fin n) where
  toFun i := ⟨n - 1 - i.val, by omega⟩
  invFun i := ⟨n - 1 - i.val, by omega⟩
  left_inv i := by ext; simp; omega
  right_inv i := by ext; simp; omega

/-! ### Star graphs (constant functions) are graceful

This is Example 3.1 from the paper. A "functional star" is the graph of
a constant function `f(i) = c` for all `i`. When `c = 0`, the function
is already gracefully labeled because the edge labels are `{0, 1, ..., n-1}`.
-/

/-- The constant-zero function on `Fin n`. -/
def constZero (hn : 0 < n) : Fin n → Fin n := fun _ => ⟨0, hn⟩

/-- The edge labels of the constant-zero function are `{0, 1, ..., n-1}`.
Specifically, `|f(i) - i| = |0 - i| = i` for each `i ∈ Fin n`. -/
theorem constZero_edgeLabelSet (hn : 0 < n) :
    edgeLabelSet (constZero hn) = Finset.univ.image (fun i : Fin n => i.val) := by
  simp [edgeLabelSet, constZero]

/-- Constant-zero function is already gracefully labeled. -/
theorem constZero_isAlreadyGraceful (hn : 0 < n) :
    IsAlreadyGraceful (constZero hn) := by
  unfold IsAlreadyGraceful edgeLabelSet constZero
  simp only [CharP.cast_eq_zero, zero_sub]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_fin n
  · intro a b hab
    simp only [CharP.cast_eq_zero, zero_sub] at hab
    exact Fin.ext (by omega)

/-- Any constant function is graceful (possibly after conjugation). -/
theorem const_isGraceful (hn : 0 < n) (c : Fin n) :
    IsGracefulFunction (fun _ => c) := by
  use Equiv.swap c ⟨0, hn⟩
  have hconj : conjugate (fun _ => c) (Equiv.swap c ⟨0, hn⟩) = constZero hn := by
    ext i
    simp [conjugate, constZero, Equiv.swap_apply_left]
  rw [hconj]
  exact constZero_isAlreadyGraceful hn

/-- **The KRR Conjecture** (Graceful Tree Conjecture).
Every tree admits a graceful labeling.

This will be proved by the chain:
  Phase 3 (Functional Reformulation) → Phase 4 (Graceful Expansion) →
  Phase 5 (Polynomial Machinery) → Phase 6 (Composition Lemma) →
  Phase 7 (Main Theorem via iterated composition to constant function). -/
theorem KRR_Conjecture_functional (hn : 0 < n) (f : Fin n → Fin n) :
    IsTreeFunction f → IsGracefulFunction f :=
  sorry -- Phase 7: assembled from all previous phases.

end KRR
