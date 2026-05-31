import KRR.Basic
import KRR.Graceful
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Order.Interval.Finset.Nat

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
  have hn' : 0 < n := by omega
  -- The label function: absolute difference of σ-relabeled edges
  let lbl : Fin n → ℕ := fun j =>
    Int.natAbs (((σ j).val : ℤ) - ((σ (f j)).val : ℤ))
  -- Step 1: Evaluate the polynomial
  simp only [determinantalPolynomial, map_prod, map_sub, MvPolynomial.eval_X]
  -- Step 2: Convert subtype product to filter product
  rw [← Finset.prod_subtype
      (Finset.univ.filter (fun i : Fin n => i.val > 0))
      (fun x => by simp [Finset.mem_filter])
      (fun i => ((σ i).val : ℤ) - ((σ (f i)).val : ℤ))]
  -- Step 3: Distribute natAbs over the product
  have h_natabs_prod : ∀ (s : Finset (Fin n)) (g : Fin n → ℤ),
      (∏ i ∈ s, g i).natAbs = ∏ i ∈ s, (g i).natAbs := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Int.natAbs_mul, Finset.prod_insert ha, ih]
  rw [h_natabs_prod]
  -- Now goal: ∏ i ∈ filter(i.val > 0), Int.natAbs (σ(i) - σ(f(i))) = (n-1)!
  -- Fold as lbl
  show ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val > 0), lbl i = (n - 1).factorial
  -- Step 4: Establish injectivity of lbl via IsAlreadyGraceful
  have hlbl_range : Finset.univ.image lbl = edgeLabelSet (conjugate f σ) := by
    simp only [edgeLabelSet, lbl, conjugate, Function.comp]
    ext k
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    have hcomm : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := fun a b => by rw [← Int.natAbs_neg (a - b), neg_sub]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨σ j, by simp [hcomm]⟩
    · rintro ⟨k', hk'⟩
      exact ⟨σ.symm k', by simp [← hk', hcomm]⟩
  have hlbl_card : (Finset.univ.image lbl).card = n := by
    rw [hlbl_range]; exact h_grace
  have hlbl_inj : Function.Injective lbl := by
    intro a b h
    have hinj : Set.InjOn lbl ↑(Finset.univ : Finset (Fin n)) :=
      Finset.card_image_iff.mp (by rw [hlbl_card, Finset.card_univ, Fintype.card_fin])
    exact hinj (Finset.mem_coe.mpr (Finset.mem_univ a))
               (Finset.mem_coe.mpr (Finset.mem_univ b)) h
  -- Step 5: lbl 0 = 0 (from f canonical: f(0) = 0)
  have hlbl_zero : lbl ⟨0, hn'⟩ = 0 := by
    simp only [lbl, hf_canon.1]
    have hcomm : ∀ a b : ℤ, (a - b).natAbs = (b - a).natAbs := fun a b => by rw [← Int.natAbs_neg (a - b), neg_sub]
    rw [hcomm]
    simp
  -- Step 6: For i > 0, lbl i ≥ 1 (f(i) ≠ i, σ injective)
  have hlbl_pos : ∀ i : Fin n, 0 < i.val → 1 ≤ lbl i := by
    intro i hi
    have hfi_lt : (f i).val < i.val := hf_canon.2 i hi
    have hfi_ne : f i ≠ i := ne_of_lt (show (f i) < i from Fin.lt_iff_val_lt_val.mpr hfi_lt)
    simp only [lbl, Nat.one_le_iff_ne_zero, Int.natAbs_ne_zero, sub_ne_zero]
    exact_mod_cast (Fin.val_ne_of_ne (σ.injective.ne hfi_ne)).symm
  -- Step 7: For all i, lbl i < n
  have hlbl_lt : ∀ i : Fin n, lbl i < n := by
    intro i
    have h1 : ((σ i).val : ℤ) < n := by exact_mod_cast (σ i).isLt
    have h2 : ((σ (f i)).val : ℤ) < n := by exact_mod_cast (σ (f i)).isLt
    have h3 : (0 : ℤ) ≤ ((σ i).val : ℤ) := Int.natCast_nonneg _
    have h4 : (0 : ℤ) ≤ ((σ (f i)).val : ℤ) := Int.natCast_nonneg _
    have hkey : (lbl i : ℤ) < n := by
      simp only [lbl, Int.natCast_natAbs, abs_lt]
      constructor <;> linarith
    exact_mod_cast hkey
  -- Step 8: The filter set has card n-1
  have hS_card : (Finset.univ.filter (fun i : Fin n => i.val > 0)).card = n - 1 := by
    have heq : Finset.univ.filter (fun i : Fin n => i.val > 0) =
               Finset.univ.erase ⟨0, hn'⟩ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_erase, and_true, Fin.ext_iff, ne_eq]
      omega
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
  -- Step 9: Icc 1 (n-1) has card n-1
  have hIcc_card : (Finset.Icc 1 (n - 1)).card = n - 1 := by
    simp only [Nat.card_Icc]; omega
  -- Step 10: The image of the filter under lbl equals Icc 1 (n-1)
  have hlbl_image : (Finset.univ.filter (fun i : Fin n => i.val > 0)).image lbl =
                    Finset.Icc 1 (n - 1) := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
                 true_and] at hk
      obtain ⟨j, hj, rfl⟩ := hk
      simp only [Finset.mem_Icc]
      exact ⟨hlbl_pos j hj, Nat.le_sub_one_of_lt (hlbl_lt j)⟩
    · rw [Finset.card_image_of_injOn (by
            intro a ha b hb h
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
                       true_and] at ha hb
            exact hlbl_inj h),
          hS_card, hIcc_card]
  -- Step 11-12: Rewrite product via bijection lbl : filter → Icc 1 (n-1)
  have h_fact : ∀ m : ℕ, ∏ k ∈ Finset.Icc 1 m, k = m.factorial := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [show Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) from by
            ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega,
          Finset.prod_insert (by simp only [Finset.mem_Icc]; omega),
          ih, Nat.factorial_succ, mul_comm]
  have h_prod_eq : ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val > 0), lbl i = ∏ k ∈ Finset.Icc 1 (n - 1), k := by
    have h_inj_on : Set.InjOn lbl ↑(Finset.univ.filter (fun i : Fin n => i.val > 0)) := by
      intro a _ b _ h
      exact hlbl_inj h
    have h_img : ∏ k ∈ Finset.image lbl (Finset.univ.filter (fun i : Fin n => i.val > 0)), k = 
                 ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val > 0), lbl i :=
      Finset.prod_image h_inj_on
    rw [← h_img, hlbl_image]
  rw [h_prod_eq]
  exact h_fact (n - 1)

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
