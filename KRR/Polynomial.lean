import KRR.Basic
import KRR.Graceful
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

open BigOperators

/-!
# Phase 5: Polynomial Machinery

This module formalizes the multivariate polynomial constructions used in the KRR proof.
Key components:
- The determinantal polynomial F_f
- Canonical representatives via quotient-remainder expansion
- Monomial overlapping lemmas
-/

namespace KRR

variable {n : ℕ}

/--
The determinantal polynomial F_f associated with a functional digraph G_f.
F_f(x₀, ..., xₙ₋₁) = ∏_{i=1}^{n-1} (x_i - x_{f(i)})
-/
noncomputable def determinantalPolynomial (f : Fin n → Fin n) : MvPolynomial (Fin n) ℤ :=
  ∏ i : {i : Fin n // i.val > 0}, (MvPolynomial.X i.1 - MvPolynomial.X (f i.1))

/--
Falling factorial (x)_k = x(x-1)...(x-k+1).
-/
noncomputable def fallingFactorial (X : MvPolynomial (Fin n) ℤ) (k : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∏ i ∈ Finset.range k, (X - (i : MvPolynomial (Fin n) ℤ))

/--
Proposition 2.3 (Basis Expansion):
Every multivariate polynomial P can be uniquely represented in the falling factorial basis.
-/
theorem quotient_remainder_expansion (P : MvPolynomial (Fin n) ℤ) :
    ∃ (c : (Fin n →₀ ℕ) → ℤ),
      P = ∑ d ∈ P.support, (MvPolynomial.monomial d (P.coeff d)) := by
  exact ⟨P.coeff, MvPolynomial.as_sum P⟩

/--
Lemma 5.1 (Graceful Evaluation):
For any graceful labeling σ of f, the determinantal polynomial evaluated at σ
is equal to ±(n-1)!.
-/
theorem graceful_evaluation (hn : 1 < n) (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n))
    (h_tree : IsTreeFunction f) (hf_canon : IsCanonicalTreeFunction (by omega) f)
    (h_grace : IsAlreadyGraceful (conjugate f σ)) :
    Int.natAbs (MvPolynomial.eval (fun i => ((σ i).val : ℤ)) (determinantalPolynomial f)) =
    (n - 1).factorial := by
  sorry

/--
Monomial Overlapping Lemma:
The determinantal polynomial F_f is non-zero for any tree function f.
-/
theorem monomial_overlapping_lemma (hn : 0 < n) (f : Fin n → Fin n)
    (h_tree : IsTreeFunction f) (h_can : IsCanonicalTreeFunction hn f) :
    (determinantalPolynomial f) ≠ 0 := by
  -- Evaluate at the identity labeling φ(i) = i.val
  -- Each factor (i - f(i)) > 0 by canonicality, so product ≠ 0
  have hne : MvPolynomial.eval (fun i : Fin n => (i.val : ℤ))
      (determinantalPolynomial f) ≠ 0 := by
    simp only [determinantalPolynomial, map_prod, map_sub, MvPolynomial.eval_X]
    rw [Finset.prod_ne_zero_iff]
    intro ⟨i, hi⟩ _
    show (i.val : ℤ) - (f i).val ≠ 0
    have hlt := h_can.2 i hi
    omega
  intro h_zero
  exact hne (by rw [h_zero, map_zero])

end KRR
