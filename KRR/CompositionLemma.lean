import KRR.Basic
import KRR.Graceful
import KRR.FunctionalReformulation
import KRR.DeterminantalPolynomial
import KRR.Telescoping
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Max

/-!
# Phase 6: Composition Lemma

This module formalizes Lemma 3.2 from the Gnang paper using the algebraic
machinery from the previous phases:
- Phase 1 (AlgebraicNullstellensatz): Ideal membership ↔ vanishing on grid
- Phase 2 (DeterminantalPolynomial): P_f vanishes on grid ↔ no graceful labeling
- Phase 3 (Telescoping): P_g = P_f + R_{f,g}, ideal inheritance

Lemma 3.2 (Composition Lemma):
For all tree functions f, if G_f has a graceful labeling, then G_{f²} also has
a graceful labeling. Equivalently, L(f²) ≤ L(f).

The proof proceeds by contradiction:
1. Suppose G_f has a graceful labeling but G_{f²} does not.
2. Then P_{f²} ≡ 0 (mod I) by the Nullstellensatz.
3. But P_f ≢ 0 (mod I) because the graceful labeling gives a nonzero evaluation.
4. So R_{f,f²} = P_f - P_{f²} ≢ 0 (mod I).
5. Using sibling symmetry of G_{f²}, we show R_{f,f²} must be invariant
   under certain variable transpositions. But a monomial analysis shows it
   is NOT invariant — contradiction.
-/

namespace KRR

variable {n : ℕ}

/--
Key lemma: If f has a graceful labeling σ, then P_f(σ) ≠ 0,
so P_f ∉ gridIdeal.
-/
theorem fullDeterminantalPolynomial_not_in_gridIdeal_of_graceful [NeZero n]
    (f : Fin n → Fin n)
    (σ : Equiv.Perm (Fin n))
    (h_graceful : IsAlreadyGraceful (conjugate f σ)) :
    ¬ fullDeterminantalPolynomial f ∈ gridIdeal n := by
  intro h_mem
  -- σ maps into the grid {0,...,n-1}
  have hx : ∀ i, (fun i => (σ i).val : Fin n → ℤ) i ∈ grid n := by
    intro i
    simp only [grid, Finset.mem_image, Finset.mem_range]
    exact ⟨(σ i).val, ⟨(σ i).isLt, rfl⟩⟩
  -- Since P_f ∈ I, it vanishes at σ
  have h_zero := eval_eq_zero_of_mem_gridIdeal
    (fullDeterminantalPolynomial f) h_mem
    (fun i => ((σ i).val : ℤ)) hx
  -- But P_f(σ) ≠ 0 because σ is graceful
  simp only [fullDeterminantalPolynomial, map_mul] at h_zero
  have h_V_ne : MvPolynomial.eval (fun i => (σ i).val : Fin n → ℤ) (vandermonde n) ≠ 0 :=
    eval_vandermonde_ne_zero_of_injective _ (fun a b h => σ.injective (Fin.ext (by exact_mod_cast h)))
  have h_W_ne : MvPolynomial.eval (fun i => (σ i).val : Fin n → ℤ) (edgeWeightsPolynomial f) ≠ 0 :=
    eval_edgeWeightsPolynomial_ne_zero_of_graceful f σ h_graceful
  exact mul_ne_zero h_V_ne h_W_ne h_zero

/--
If $f$ has a graceful labeling but $f^2$ does not, the remainder polynomial
$R_{f, f^2}$ cannot be in the grid ideal. Gnang's subsequent sibling symmetry
argument (Section 3 of arXiv:2202.03178) claims $R \in I$ under these conditions,
but that step has not been formalized. This is the furthest the algebraic proof
has been formally verified.
-/
theorem remainder_not_in_gridIdeal_of_graceful_not_graceful [NeZero n]
    (f : Fin n → Fin n)
    (h_graceful_f : ∃ (σ : Equiv.Perm (Fin n)), IsAlreadyGraceful (conjugate f σ))
    (h_no_graceful_g : ¬ ∃ (σ : Equiv.Perm (Fin n)), IsAlreadyGraceful (conjugate (f ∘ f) σ)) :
    ¬ remainderPolynomial f (f ∘ f) ∈ gridIdeal n := by
  have h_Pg_in_I :
      fullDeterminantalPolynomial (f ∘ f) ∈ gridIdeal n :=
    fullDeterminantalPolynomial_mem_gridIdeal_of_no_graceful
      (f ∘ f) h_no_graceful_g
  obtain ⟨σ, hσ⟩ := h_graceful_f
  have h_Pf_not_in_I :
      ¬ fullDeterminantalPolynomial f ∈ gridIdeal n :=
    fullDeterminantalPolynomial_not_in_gridIdeal_of_graceful
      f σ hσ
  intro h_R
  apply h_Pf_not_in_I
  have : fullDeterminantalPolynomial f =
      fullDeterminantalPolynomial (f ∘ f) -
        remainderPolynomial f (f ∘ f) := by
    simp [remainderPolynomial]
  rw [this]
  exact Submodule.sub_mem (gridIdeal n) h_Pg_in_I h_R

end KRR
