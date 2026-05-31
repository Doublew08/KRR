import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import KRR.AlgebraicNullstellensatz
import KRR.DeterminantalPolynomial

namespace KRR

variable {n : ℕ}

/--
The remainder polynomial R_{f,g} defined as the difference between P_g and P_f.
By definition, P_g = P_f + R_{f,g}.
-/
noncomputable def remainderPolynomial (f g : Fin n → Fin n) : MvPolynomial (Fin n) ℤ :=
  fullDeterminantalPolynomial g - fullDeterminantalPolynomial f

/--
Telescoping substitution theorem:
If no graceful labeling exists for f, then P_f ∈ I.
If a graceful labeling exists for g, then P_g ∉ I.
This implies R_{f,g} ∉ I.
-/
theorem remainder_not_in_ideal [NeZero n] (f g : Fin n → Fin n)
    (hf : ¬ ∃ (σ : Equiv.Perm (Fin n)), IsAlreadyGraceful (conjugate f σ))
    (hg : ¬ fullDeterminantalPolynomial g ∈ gridIdeal n) :
    ¬ remainderPolynomial f g ∈ gridIdeal n := by
  intro h_rem
  have h_Pf : fullDeterminantalPolynomial f ∈ gridIdeal n :=
    fullDeterminantalPolynomial_mem_gridIdeal_of_no_graceful f hf
  have h_Pg_eq : fullDeterminantalPolynomial g = remainderPolynomial f g + fullDeterminantalPolynomial f := by
    simp [remainderPolynomial]
  have h_Pg_in_I : fullDeterminantalPolynomial g ∈ gridIdeal n := by
    rw [h_Pg_eq]
    exact Submodule.add_mem (gridIdeal n) h_rem h_Pf
  exact hg h_Pg_in_I

end KRR
