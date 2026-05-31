import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Int.Lemmas
import KRR.AlgebraicNullstellensatz
import KRR.Polynomial
import KRR.Graceful

open BigOperators

set_option linter.style.longLine false

namespace KRR

variable {n : ℕ}

/--
The Vandermonde polynomial: V(x) = ∏_{i < j} (x_j - x_i).
Vanishes iff two variables share a value.
-/
noncomputable def vandermonde (n : ℕ) : MvPolynomial (Fin n) ℤ :=
  ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
    (MvPolynomial.X j - MvPolynomial.X i)

/--
The edge-weight factor from Gnang's Certificate of Grace (Proposition 3.1):
  W_f(x) = ∏_{i < j} ((x_{f(j)} − x_j)² − (x_{f(i)} − x_i)²)
Vanishes iff two edges share the same absolute weight.
F_f = V · W_f is Gnang's full determinantal polynomial.
-/
noncomputable def edgeWeightsPolynomial (f : Fin n → Fin n) : MvPolynomial (Fin n) ℤ :=
  ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
    ((MvPolynomial.X (f j) - MvPolynomial.X j) ^ 2 -
     (MvPolynomial.X (f i) - MvPolynomial.X i) ^ 2)

/-- P_f(x) = V(x) · W_f(x) -/
noncomputable def fullDeterminantalPolynomial (f : Fin n → Fin n) : MvPolynomial (Fin n) ℤ :=
  vandermonde n * edgeWeightsPolynomial f

/-! ### Vandermonde vanishing / non-vanishing -/

theorem eval_vandermonde_eq_zero_of_not_injective (x : Fin n → ℤ)
    (h_not_inj : ¬ Function.Injective x) :
    MvPolynomial.eval x (vandermonde n) = 0 := by
  rw [Function.Injective] at h_not_inj
  push_neg at h_not_inj
  obtain ⟨i, j, h_eq, h_ne⟩ := h_not_inj
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne h_ne) with h_lt | h_lt
  · simp only [vandermonde, map_prod, map_sub, MvPolynomial.eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h_lt⟩) (by simp [h_eq]))
  · simp only [vandermonde, map_prod, map_sub, MvPolynomial.eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_lt⟩) (by simp [h_eq]))

theorem eval_vandermonde_ne_zero_of_injective (x : Fin n → ℤ)
    (h_inj : Function.Injective x) :
    MvPolynomial.eval x (vandermonde n) ≠ 0 := by
  simp only [vandermonde, map_prod, map_sub, MvPolynomial.eval_X]
  intro h_zero
  rw [Finset.prod_eq_zero_iff] at h_zero
  obtain ⟨i, -, hi⟩ := h_zero
  rw [Finset.prod_eq_zero_iff] at hi
  obtain ⟨j, hj_mem, h_factor⟩ := hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj_mem
  rw [sub_eq_zero] at h_factor
  exact (Fin.ne_of_lt hj_mem) (h_inj h_factor).symm

/-! ### Helpers: build a permutation from an injective grid map -/

private lemma grid_nonneg (x : Fin n → ℤ) (hx : ∀ i, x i ∈ grid n) (i : Fin n) :
    0 ≤ x i := by
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hx i)
  rw [← hk]; exact Int.ofNat_nonneg k

private lemma grid_toNat_lt (x : Fin n → ℤ) (hx : ∀ i, x i ∈ grid n) (i : Fin n) :
    (x i).toNat < n := by
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp (hx i)
  simp only [Finset.mem_range] at hk
  rw [← heq, Int.toNat_natCast]
  exact hk

/-- A permutation of Fin n induced by an injective map x : Fin n → {0,…,n−1} ⊆ ℤ. -/
private noncomputable def permOfGridMap (x : Fin n → ℤ) (hx : ∀ i, x i ∈ grid n)
    (h_inj : Function.Injective x) : Equiv.Perm (Fin n) :=
  let φ : Fin n → Fin n := fun i => ⟨(x i).toNat, grid_toNat_lt x hx i⟩
  have h_φ_inj : Function.Injective φ := fun a b hab => h_inj (by
    have heq : (x a).toNat = (x b).toNat := congr_arg Fin.val hab
    calc x a = ((x a).toNat : ℤ) := (Int.toNat_of_nonneg (grid_nonneg x hx a)).symm
         _ = ((x b).toNat : ℤ) := by exact_mod_cast heq
         _ = x b := Int.toNat_of_nonneg (grid_nonneg x hx b))
  Equiv.ofBijective φ ⟨h_φ_inj, Finite.surjective_of_injective h_φ_inj⟩

private lemma permOfGridMap_cast (x : Fin n → ℤ) (hx : ∀ i, x i ∈ grid n)
    (h_inj : Function.Injective x) (i : Fin n) :
    ((permOfGridMap x hx h_inj i).val : ℤ) = x i := by
  simp only [permOfGridMap, Equiv.ofBijective_apply]
  exact Int.toNat_of_nonneg (grid_nonneg x hx i)

/-! ### Main theorems -/

/--
W_f(σ) ≠ 0 when σ is a graceful labeling of f.
The n squared edge-weight values are pairwise distinct, so every factor is nonzero.
-/
theorem eval_edgeWeightsPolynomial_ne_zero_of_graceful (f : Fin n → Fin n)
    (σ : Equiv.Perm (Fin n)) (h_graceful : IsAlreadyGraceful (conjugate f σ)) :
    MvPolynomial.eval (fun i => (σ i).val : Fin n → ℤ) (edgeWeightsPolynomial f) ≠ 0 := by
  intro h_zero
  simp only [edgeWeightsPolynomial, map_prod, map_sub, map_pow, MvPolynomial.eval_X] at h_zero
  rw [Finset.prod_eq_zero_iff] at h_zero
  obtain ⟨i, -, hi⟩ := h_zero
  rw [Finset.prod_eq_zero_iff] at hi
  obtain ⟨j, hj_mem, h_factor⟩ := hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj_mem
  -- Factor = 0 means the two squared edge weights are equal
  have h_sq_eq : (((σ (f j)).val : ℤ) - (σ j).val) ^ 2 =
                 (((σ (f i)).val : ℤ) - (σ i).val) ^ 2 := by linarith
  -- Equal squares → equal natAbs
  have h_natAbs_eq : Int.natAbs (((σ (f j)).val : ℤ) - (σ j).val) =
                     Int.natAbs (((σ (f i)).val : ℤ) - (σ i).val) :=
    Int.natAbs_eq_iff_sq_eq.mpr h_sq_eq
  -- Connect to edge labels of conjugate f σ at vertices σ j and σ i
  have h_label_j : Int.natAbs ((conjugate f σ (σ j)).val - (σ j).val : ℤ) =
                   Int.natAbs (((σ (f j)).val : ℤ) - (σ j).val) := by
    congr 1; push_cast; simp [conjugate, Equiv.symm_apply_apply]
  have h_label_i : Int.natAbs ((conjugate f σ (σ i)).val - (σ i).val : ℤ) =
                   Int.natAbs (((σ (f i)).val : ℤ) - (σ i).val) := by
    congr 1; push_cast; simp [conjugate, Equiv.symm_apply_apply]
  have h_label_eq : Int.natAbs ((conjugate f σ (σ j)).val - (σ j).val : ℤ) =
                    Int.natAbs ((conjugate f σ (σ i)).val - (σ i).val : ℤ) :=
    h_label_j.trans (h_natAbs_eq.trans h_label_i.symm)
  -- σ j ≠ σ i since i < j and σ is injective
  have h_ne_σ : σ j ≠ σ i :=
    (σ.injective.ne (Fin.ne_of_lt hj_mem)).symm
  -- Extract injectivity of the edge-label function from IsAlreadyGraceful
  have h_inj_lbl : Function.Injective
      (fun k : Fin n => Int.natAbs ((conjugate f σ k).val - k.val : ℤ)) := by
    intro a b hab
    have hcard : (Finset.univ.image (fun k : Fin n =>
        Int.natAbs ((conjugate f σ k).val - k.val : ℤ))).card =
                 (Finset.univ : Finset (Fin n)).card := by
      unfold IsAlreadyGraceful edgeLabelSet at h_graceful
      rw [Finset.card_univ, Fintype.card_fin]
      exact h_graceful
    exact Finset.card_image_iff.mp hcard
          (Finset.mem_coe.mpr (Finset.mem_univ a))
          (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  exact h_ne_σ (h_inj_lbl h_label_eq)

/--
If no graceful labeling exists for f, then P_f(x) = 0 for all x in the grid.
(Gnang's Certificate of Grace, direction: ungraceful → P_f ≡ 0 mod I.)
-/
theorem eval_fullDeterminantalPolynomial_eq_zero_of_no_graceful (f : Fin n → Fin n)
    (h_no_graceful : ¬ ∃ (σ : Equiv.Perm (Fin n)), IsAlreadyGraceful (conjugate f σ))
    (x : Fin n → ℤ) (hx : ∀ i, x i ∈ grid n) :
    MvPolynomial.eval x (fullDeterminantalPolynomial f) = 0 := by
  simp only [fullDeterminantalPolynomial, map_mul]
  by_cases h_inj : Function.Injective x
  · -- x is a permutation: Vandermonde ≠ 0, so need W_f(x) = 0.
    suffices h : MvPolynomial.eval x (edgeWeightsPolynomial f) = 0 by rw [h, mul_zero]
    by_contra h_ne
    -- Every factor nonzero → squared edge weights pairwise distinct.
    have h_all_ne : ∀ i j : Fin n, i.val < j.val →
        (x (f j) - x j) ^ 2 ≠ (x (f i) - x i) ^ 2 := by
      intro i j hij h_eq
      apply h_ne
      simp only [edgeWeightsPolynomial, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
      exact Finset.prod_eq_zero (Finset.mem_univ i)
        (Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hij⟩) (by linarith))
    -- The map j ↦ |x(f j) − x j| is injective.
    have h_natAbs_inj : Function.Injective
        (fun j : Fin n => Int.natAbs (x (f j) - x j)) := by
      intro a b hab
      -- Equal natAbs → equal squares
      have h_sq : (x (f a) - x a) ^ 2 = (x (f b) - x b) ^ 2 :=
        Int.natAbs_eq_iff_sq_eq.mp hab
      rcases Nat.lt_trichotomy a.val b.val with h | h | h
      · exact absurd h_sq.symm (h_all_ne a b h)
      · exact Fin.ext h
      · exact absurd h_sq (h_all_ne b a h)
    -- Build permutation σ_x from x.
    let σ_x := permOfGridMap x hx h_inj
    have σ_x_cast : ∀ i : Fin n, ((σ_x i).val : ℤ) = x i := permOfGridMap_cast x hx h_inj
    -- Key identity: differences at σ_x equal x-differences.
    have key : ∀ i : Fin n,
        ((σ_x (f (σ_x.symm i))).val : ℤ) - (i.val : ℤ) =
        x (f (σ_x.symm i)) - x (σ_x.symm i) := by
      intro i
      have h1 : ((σ_x (f (σ_x.symm i))).val : ℤ) = x (f (σ_x.symm i)) := σ_x_cast _
      have h2 : (i.val : ℤ) = x (σ_x.symm i) := by
        conv_lhs => rw [show i = σ_x (σ_x.symm i) from (Equiv.apply_symm_apply σ_x i).symm]
        exact σ_x_cast _
      linarith
    -- conjugate f σ_x is gracefully labeled, contradicting h_no_graceful.
    exact h_no_graceful ⟨σ_x, by
      unfold IsAlreadyGraceful edgeLabelSet conjugate
      simp only [Function.comp]
      have h_lbl_inj : Function.Injective
          (fun i : Fin n => Int.natAbs ((σ_x (f (σ_x.symm i))).val - i.val : ℤ)) := by
        intro a b hab
        dsimp only at hab
        have ha : Int.natAbs ((σ_x (f (σ_x.symm a))).val - a.val : ℤ) =
                  Int.natAbs (x (f (σ_x.symm a)) - x (σ_x.symm a)) := by
          congr 1; exact_mod_cast key a
        have hb : Int.natAbs ((σ_x (f (σ_x.symm b))).val - b.val : ℤ) =
                  Int.natAbs (x (f (σ_x.symm b)) - x (σ_x.symm b)) := by
          congr 1; exact_mod_cast key b
        rw [ha, hb] at hab
        exact σ_x.symm.injective (h_natAbs_inj hab)
      have heq := Finset.card_image_of_injective Finset.univ h_lbl_inj
      simp only [Finset.card_univ, Fintype.card_fin] at heq
      exact heq⟩
  · -- Not injective: Vandermonde = 0.
    rw [eval_vandermonde_eq_zero_of_not_injective x h_inj, zero_mul]

/--
By the Combinatorial Nullstellensatz, if no graceful labeling exists,
P_f is in the grid ideal.
-/
theorem fullDeterminantalPolynomial_mem_gridIdeal_of_no_graceful [NeZero n] (f : Fin n → Fin n)
    (h_no_graceful : ¬ ∃ (σ : Equiv.Perm (Fin n)), IsAlreadyGraceful (conjugate f σ)) :
    fullDeterminantalPolynomial f ∈ gridIdeal n := by
  rw [mem_gridIdeal_iff_eval_zero]
  exact fun x hx => eval_fullDeterminantalPolynomial_eq_zero_of_no_graceful f h_no_graceful x hx

end KRR
