import KRR.Basic
import KRR.Graceful
import KRR.Combinatorics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Int.Basic

/-!
# KRR Phase 3: Functional Reformulation

This module reformulates the graceful labeling problem in terms of
endofunctions on `Fin n`, following Section 2.1–2.2 of the paper.

## Main definitions

* `KRR.IsValidPermutationBasis` — permutation basis condition (eq. 2.6)
* `KRR.SignFunction` — the sign function 𝔰_f(γ, i) ∈ {-1, 0, 1}

## References

* [Gnang, *A proof of the Kotzig–Ringel–Rosa Conjecture*][arXiv:2202.03178]
-/

namespace KRR

variable {n : ℕ}

/-- A permutation `γ` fixing 0 is a valid permutation basis for graceful expansion
if for all `i ∈ {1, ..., n-1}`, either `γ(i) ≤ i` or `γ(i) ≤ (n-1) - i`.
This is equation (2.6) from the paper. -/
def IsValidPermutationBasis (hn : 0 < n) (γ : Equiv.Perm (Fin n)) : Prop :=
  γ ⟨0, hn⟩ = ⟨0, hn⟩ ∧
  ∀ i : Fin n, i.val > 0 →
    (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val

/-- The sign function `𝔰_f(γ, i)` from the Graceful Expansion Theorem.
For each vertex `i` and permutation basis `γ`:
  - returns `0` if `f(i) = i` (loop edge)
  - returns `1` if the edge label was obtained via subtraction
  - returns `-1` if the edge label was obtained via addition -/
def signFunction (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n))
    (_ : Equiv.Perm (Fin n)) (i : Fin n) : Int :=
  let fi := conjugate f σ
  if fi i = i then 0
  else if (fi i).val < i.val then -1
  else 1

/-- **Theorem (Section 2.2):** The number of valid permutation bases fixing 0 is exactly
`⌊(n-1)/2⌋! · ⌈(n-1)/2⌉!`.
-/
axiom count_valid_bases_eq (hn : 0 < n) (h2 : 2 < n) :
    (Finset.univ.filter (fun γ : Equiv.Perm (Fin n) =>
      γ ⟨0, hn⟩ = ⟨0, hn⟩ ∧
      ∀ i : Fin n, i.val > 0 →
        (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val)).card =
    Nat.factorial ((n - 1) / 2) * Nat.factorial (((n - 1) + 1) / 2)

end KRR
