import KRR.Basic
import KRR.Graceful
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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
  ∏ i : {i : Fin n // i.val > 0}, (MvPolynomial.X i.val - MvPolynomial.X (f i.val))

/--
Proposition 2.3 (Quotient-Remainder Expansion):
Every multivariate polynomial P can be uniquely represented as:
  P = ∑_d c_d ∏_i (x_i)_d_i
where (x)_k is the falling factorial.
-/
theorem quotient_remainder_expansion (P : MvPolynomial (Fin n) ℤ) :
  ∃ (c : (Fin n →₀ ℕ) → ℤ), 
    P = ∑ d in P.support, (MvPolynomial.monomial d (c d)) -- This needs falling factorial basis
  := sorry
/--
Lemma 5.1 (Graceful Evaluation):
For any graceful labeling σ of f, the determinantal polynomial evaluated at σ
is equal to ±(n-1)!.
-/
theorem graceful_evaluation (hn : 1 < n) (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n))
    (h_grace : IsAlreadyGraceful (conjugate f σ)) :
    Int.natAbs (MvPolynomial.eval σ (determinantalPolynomial f)) = (n - 1).factorial := by
  unfold determinantalPolynomial
  rw [MvPolynomial.eval_prod]
  let labels := (Finset.univ.filter (fun i : Fin n => i.val > 0)).image (fun i => 
    (Int.natAbs (↑(σ i).val - ↑(σ (f i)).val)))
  have h_labels : labels = (Finset.range (n - 1)).image (· + 1) := by
    -- From IsAlreadyGraceful, the set of labels is exactly {1, ..., n-1}
    unfold IsAlreadyGraceful at h_grace
    let S := (Finset.univ.filter (fun i : Fin n => i.val > 0)).image (fun i => 
      Int.natAbs (↑(σ i).val - ↑(σ (f i)).val))
    have hS_card : S.card = n - 1 := h_grace
    -- Since S ⊆ {1, ..., n-1} and |S| = n-1, S = {1, ..., n-1}
    have hS_sub : S ⊆ (Finset.range (n - 1)).image (· + 1) := by
      intro k hk; simp at hk; obtain ⟨i, hi, rfl⟩ := hk
      simp; constructor; swap; omega
      -- Label must be at least 1 because σ i ≠ σ (f i)
      have : σ i ≠ σ (f i) := by
        intro heq; have := σ.injective heq
        have hLT := (IsTreeFunction.isTreeFunction hn f (by sorry)).2 i hi
        omega
      omega
    exact Finset.eq_of_subset_of_card_le hS_sub (by simp; omega)
  have : (∏ i : {i // 0 < i.val}, Int.natAbs ((σ i.val).val - (σ (f i.val)).val)) = 
         (∏ k in Finset.Icc 1 (n - 1), k) := by
    -- Use the fact that labels are a permutation of 1..n-1
    rw [← Finset.prod_image]
    · congr; exact h_labels
    · intro x hx y hy heq; exact heq -- Magnitude is the identity on labels
  rw [this, Nat.factorial_prod_Icc]

/--
Monomial Overlapping Lemma:
The determinantal polynomial F_f is non-zero for any tree function f.
Specifically, there exists a monomial with coefficient ±1.
-/
theorem monomial_overlapping_lemma (f : Fin n → Fin n) (h_tree : IsTreeFunction f) :
  (determinantalPolynomial f) ≠ 0 := by
  unfold determinantalPolynomial
  -- A product of non-zero polynomials in an integral domain is non-zero.
  -- Each (x_i - x_j) is non-zero because i ≠ j for a loopless tree.
  sorry

end KRR
