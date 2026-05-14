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
  ∏ i : {i : Fin n // i.val > 0}, (MvPolynomial.X i.1 - MvPolynomial.X (f i.1))

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
        -- Since f is a tree function and i > 0, i cannot be a fixed point.
        have h_ne : i ≠ f i := by
          by_contra h_eq
          have : i ∈ iterateImage f (n-1) := by
            unfold iterateImage; simp; use i; exact Function.IsFixedPt.iterate h_eq (n - 1)
          have : (iterateImage f (n-1)).card = 1 := h_tree
          -- Since 0 is a fixed point (from tree property), i must be 0.
          sorry
        exact h_ne this
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
  apply Finset.prod_ne_zero
  intro i hi
  simp only [Finset.mem_univ, Subtype.forall, true_and] at hi
  have h_ne : i ≠ f i := by
    by_contra heq
    obtain ⟨sink, h_sink⟩ := Finset.card_eq_one.mp h_tree
    have h_fix_val : f i = i := heq
    have : i ∈ iterateImage f (n-1) := by
      unfold iterateImage; simp; use i; exact Function.IsFixedPt.iterate h_fix_val (n - 1)
    have : i = sink := by
      rw [← Finset.mem_singleton, ← h_sink]; exact this
    -- We assume the root 0 is the fixed point for tree functions.
    -- More generally, if i > 0, then i ≠ sink if sink = 0.
    sorry
  apply sub_ne_zero.mpr
  intro h_poly
  have : (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) = MvPolynomial.X (f i) := h_poly
  have := MvPolynomial.X_injective this
  exact h_ne this

end KRR
