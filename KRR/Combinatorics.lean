import KRR.Basic
import KRR.Graceful
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group

namespace KRR

variable {m : ℕ}

def mySuccAbove {k : ℕ} (v : Fin (k + 1)) (z : Fin k) : {x : Fin (k + 1) // x ≠ v} :=
  if h : z.val < v.val then
    ⟨⟨z.val, by omega⟩, by intro eq; have eq2 : z.val = v.val := congrArg Fin.val eq; omega⟩
  else
    ⟨⟨z.val + 1, by omega⟩, by intro eq; have eq2 : z.val + 1 = v.val := congrArg Fin.val eq; omega⟩

def myPredAbove {k : ℕ} (v : Fin (k + 1)) (y : {x : Fin (k + 1) // x ≠ v}) : Fin k :=
  if h : y.val.val < v.val then
    ⟨y.val.val, by
      have hy : y.val.val < k + 1 := y.val.isLt
      omega⟩
  else
    ⟨y.val.val - 1, by
      have hy : y.val.val < k + 1 := y.val.isLt
      have h_ne : y.val.val ≠ v.val := by intro eq; exact y.2 (Fin.ext eq)
      omega⟩

def myEquiv {k : ℕ} (v : Fin (k + 1)) : Fin k ≃ {x : Fin (k + 1) // x ≠ v} :=
  { toFun := mySuccAbove v
    invFun := myPredAbove v
    left_inv := fun z => by
      ext
      dsimp [mySuccAbove]
      split_ifs with h
      · dsimp [myPredAbove]
        rw [dif_pos h]
      · dsimp [myPredAbove]
        have h_not : ¬(z.val + 1 < v.val) := by omega
        simp only [dif_neg h_not]
        try omega
    right_inv := fun y => by
      ext
      have hy_ne : y.val.val ≠ v.val := by intro eq; exact y.2 (Fin.ext eq)
      dsimp [myPredAbove]
      split_ifs with h
      · dsimp [mySuccAbove]
        rw [dif_pos h]
      · dsimp [mySuccAbove]
        have h_not : ¬(y.val.val - 1 < v.val) := by omega
        rw [dif_neg h_not]
        dsimp; omega }

private lemma prod_Fin_descFactorial {n : ℕ} (m : ℕ) (h : m ≤ n) :
    ∏ k : Fin m, (n - (k : ℕ)) = n.descFactorial m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih (Nat.le_of_succ_le h), mul_comm, Nat.descFactorial_succ]

private lemma descFactorial_pred_factorial (m : ℕ) : (m + 1).descFactorial m = (m + 1).factorial := by
  have h := Nat.descFactorial_succ (m + 1) m
  have hone : m + 1 - m = 1 := by omega
  rw [hone, one_mul] at h
  rw [← h]; exact Nat.descFactorial_self (m + 1)

/--
Theorem 4.1: The product formula for permutation bounds.
For a specific sequence s = [m+1, m+1, m+2, m+2, ...], the product is (m+1)! m!.
-/
theorem product_formula_even :
    (∏ j : Fin (2 * m), (m + (j : ℕ) / 2 + 1 - (j : ℕ))) =
    (Nat.factorial m) * (Nat.factorial (m + 1)) := by
  -- Bijection (k, b) ↦ 2k+b : Fin m × Fin 2 → Fin (2m)
  let e : Fin m × Fin 2 ≃ Fin (2 * m) :=
  { toFun  := fun ⟨k, b⟩ => ⟨2 * k.val + b.val, by have := k.isLt; have := b.isLt; omega⟩
    invFun := fun j => ⟨⟨j.val / 2, by have := j.isLt; omega⟩,
                        ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩⟩
    left_inv := by
      rintro ⟨⟨k, hk⟩, ⟨b, hb⟩⟩
      simp only [Prod.mk.injEq, Fin.mk.injEq]; omega
    right_inv := by intro ⟨j, hj⟩; simp only [Fin.mk.injEq]; omega }
  -- Chain of equalities
  calc (∏ j : Fin (2 * m), (m + (j : ℕ) / 2 + 1 - (j : ℕ)))
      = (∏ p : Fin m × Fin 2, (m + (e p : ℕ) / 2 + 1 - (e p : ℕ))) :=
          (Equiv.prod_comp e (fun j => m + (j : ℕ) / 2 + 1 - (j : ℕ))).symm
    _ = (∏ k : Fin m, ∏ b : Fin 2, (m + (e (k, b) : ℕ) / 2 + 1 - (e (k, b) : ℕ))) :=
          Fintype.prod_prod_type _
    _ = (∏ k : Fin m, ((m + (e (k, 0) : ℕ) / 2 + 1 - (e (k, 0) : ℕ)) *
                       (m + (e (k, 1) : ℕ) / 2 + 1 - (e (k, 1) : ℕ)))) := by
          congr 1; ext k; exact Fin.prod_univ_two _
    _ = (∏ k : Fin m, ((m + 1 - k.val) * (m - k.val))) := by
          congr 1; ext k
          simp only [e, Equiv.coe_fn_mk,
                     show (0 : Fin 2).val = 0 from rfl,
                     show (1 : Fin 2).val = 1 from rfl]
          have := k.isLt; congr 1 <;> omega
    _ = (∏ k : Fin m, (m + 1 - k.val)) * (∏ k : Fin m, (m - k.val)) :=
          Finset.prod_mul_distrib
    _ = (m + 1).descFactorial m * m.descFactorial m := by
          rw [prod_Fin_descFactorial m (Nat.le_succ m),
              prod_Fin_descFactorial m (Nat.le_refl m)]
    _ = m.factorial * (m + 1).factorial := by
          rw [Nat.descFactorial_self, descFactorial_pred_factorial]; ring

/--
Helper: Counting injections Fin k ↪ Fin n with monotone upper bounds.
-/
theorem count_perm_le_product {n : ℕ} (s : Fin n → ℕ) (h_mono : Monotone s) (h_bound : ∀ i, s i ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, (σ i).val < s i)).card =
    ∏ i, (s i - i.val) := by
  induction n with
  | zero => 
    have h_empty_prod : ∏ i : Fin 0, (s i - i.val) = 1 := rfl
    rw [h_empty_prod]
    have h_perm_univ : (Finset.univ : Finset (Equiv.Perm (Fin 0))) = {1} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim x 1
    rw [h_perm_univ]
    have h_filter : ({1} : Finset (Equiv.Perm (Fin 0))).filter (fun σ => ∀ i, (σ i).val < s i) = {1} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, _⟩; exact h1
      · intro h1; rw [h1]; exact ⟨rfl, fun i => i.elim0⟩
    rw [h_filter, Finset.card_singleton]
  | succ k ih =>
    have h_decomp : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => ∀ i, (σ i).val < s i)).card =
        (s 0) * (Finset.univ.filter (fun τ : Equiv.Perm (Fin k) => ∀ j, (τ j).val < s (Fin.succ j) - 1)).card := by
      have h_sum : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => ∀ i, (σ i).val < s i)).card =
          ∑ v ∈ Finset.univ.filter (fun v : Fin (k + 1) => v.val < s 0),
            (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ 0 = v ∧ ∀ i, (σ i).val < s i)).card := by
        have h_bind : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => ∀ i, (σ i).val < s i)) =
            (Finset.univ.filter (fun v : Fin (k + 1) => v.val < s 0)).biUnion
            (fun v => Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ 0 = v ∧ ∀ i, (σ i).val < s i)) := by
          ext σ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
          constructor
          · intro hσ
            use σ 0
            refine ⟨by exact hσ 0, ⟨rfl, hσ⟩⟩
          · rintro ⟨v, _, hvσ⟩
            exact hvσ.2
        rw [h_bind, Finset.card_biUnion]
        intro v1 _ v2 _ hneq
        dsimp [Function.onFun]
        rw [Finset.disjoint_left]
        intro σ h1 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        have eq1 := h1.1
        have eq2 := h2.1
        rw [← eq1, ← eq2] at hneq
        exact hneq rfl
      have h_sum_eval : ∑ v ∈ Finset.univ.filter (fun v : Fin (k + 1) => v.val < s 0),
            (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ 0 = v ∧ ∀ i, (σ i).val < s i)).card =
          ∑ v ∈ Finset.univ.filter (fun v : Fin (k + 1) => v.val < s 0),
            (Finset.univ.filter (fun τ : Equiv.Perm (Fin k) => ∀ j, (τ j).val < s (Fin.succ j) - 1)).card := by
        apply Finset.sum_congr rfl
        intro v hv
        let e1 : Fin k ≃ {x : Fin (k+1) // x ≠ 0} := myEquiv 0
        let e2 : Fin k ≃ {x : Fin (k+1) // x ≠ v} := myEquiv v
        apply Finset.card_bij (fun σ hσ => 
          let e_sub : {x : Fin (k+1) // x ≠ 0} ≃ {x : Fin (k+1) // x ≠ v} :=
            { toFun := fun x => ⟨σ x.val, by
                intro eq
                have h0 := (Finset.mem_filter.mp hσ).2.1
                have := σ.injective (eq.trans h0.symm)
                exact x.2 this⟩
              invFun := fun y => ⟨σ.symm y.val, by
                intro eq
                have h0 := (Finset.mem_filter.mp hσ).2.1
                have : y.val = v := by
                  have h_symm : σ (σ.symm y.val) = y.val := Equiv.apply_symm_apply σ y.val
                  rw [eq] at h_symm
                  rw [← h_symm, h0]
                exact y.2 this⟩
              left_inv := fun x => Subtype.ext (Equiv.symm_apply_apply σ x.val)
              right_inv := fun y => Subtype.ext (Equiv.apply_symm_apply σ y.val) }
          e1.trans (e_sub.trans e2.symm))
        · intro σ hσ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
          intro j
          have hv_lt : v.val < s 0 := (Finset.mem_filter.mp hv).2
          have h_mono0 : s 0 ≤ s (Fin.succ j) := h_mono (Fin.zero_le _)
          have h_lt : (σ (Fin.succ j)).val < s (Fin.succ j) := hσ.2 (Fin.succ j)
          have h0 : σ 0 = v := hσ.1
          have h_neq : (σ (Fin.succ j)).val ≠ v.val := by
            intro eq
            have eq_fin : σ (Fin.succ j) = σ 0 := by ext; rw [eq, h0]
            have h_eq := σ.injective eq_fin
            revert h_eq
            exact Fin.succ_ne_zero j
          dsimp [e1, e2, myEquiv, myPredAbove, mySuccAbove]
          split_ifs with h_v
          · change (σ (Fin.succ j)).val < v.val at h_v
            change (σ (Fin.succ j)).val < s (Fin.succ j) - 1
            omega
          · change ¬((σ (Fin.succ j)).val < v.val) at h_v
            change (σ (Fin.succ j)).val - 1 < s (Fin.succ j) - 1
            omega
        · intro a1 ha1 a2 ha2 eq
          apply Equiv.ext; intro x
          by_cases hx : x = 0
          · rw [hx]
            have h1 := (Finset.mem_filter.mp ha1).2.1
            have h2 := (Finset.mem_filter.mp ha2).2.1
            rw [h1, h2]
          · have h_eq_fun := Equiv.ext_iff.mp eq
            let y : {z : Fin (k+1) // z ≠ 0} := ⟨x, hx⟩
            have h_j := h_eq_fun (e1.symm y)
            simp only [Equiv.trans_apply, Equiv.apply_symm_apply] at h_j
            have h_j2 := congrArg e2 h_j
            simp only [Equiv.apply_symm_apply] at h_j2
            have h_j3 := congrArg Subtype.val h_j2
            exact h_j3
        · intro τ hτ
          let a : Equiv.Perm (Fin (k + 1)) :=
            { toFun := fun x => if h : x = 0 then v else (e2 (τ (e1.symm ⟨x, h⟩))).val
              invFun := fun y => if h : y = v then 0 else (e1 (τ.symm (e2.symm ⟨y, h⟩))).val
              left_inv := fun x => by
                ext
                dsimp
                by_cases hx : x = 0
                · simp only [hx, dif_pos]
                · have h_τ_val : (e2 (τ (e1.symm ⟨x, hx⟩))).val ≠ v := (e2 _).2
                  simp only [hx, h_τ_val, not_false_eq_true, dif_neg]
                  have h_eta1 : (⟨(e2 (τ (e1.symm ⟨x, hx⟩))).val, h_τ_val⟩ : {y : Fin (k+1) // y ≠ v}) = e2 (τ (e1.symm ⟨x, hx⟩)) := Subtype.ext rfl
                  rw [h_eta1]
                  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
              right_inv := fun y => by
                ext
                dsimp
                by_cases hy : y = v
                · simp only [hy, dif_pos]
                · have h_τ_val : (e1 (τ.symm (e2.symm ⟨y, hy⟩))).val ≠ 0 := (e1 _).2
                  simp only [hy, h_τ_val, not_false_eq_true, dif_neg]
                  have h_eta1 : (⟨(e1 (τ.symm (e2.symm ⟨y, hy⟩))).val, h_τ_val⟩ : {x : Fin (k+1) // x ≠ 0}) = e1 (τ.symm (e2.symm ⟨y, hy⟩)) := Subtype.ext rfl
                  rw [h_eta1]
                  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply] }
          have ha_v : a 0 = v := by ext; simp [a]
          have ha_lt : ∀ i, (a i).val < s i := by
            intro i
            dsimp [a]
            split_ifs with h
            · rw [h]; exact (Finset.mem_filter.mp hv).2
            · have h_τ_lt := (Finset.mem_filter.mp hτ).2 (e1.symm ⟨i, h⟩)
              have hi_eq : (e1.symm ⟨i, h⟩).succ = i := by
                ext
                dsimp [e1, myEquiv, myPredAbove]
                have hi_ne : i.val ≠ 0 := by intro eq; exact h (Fin.ext eq)
                omega
              rw [hi_eq] at h_τ_lt
              have hv_lt : v.val < s 0 := (Finset.mem_filter.mp hv).2
              have h_mono_i : s 0 ≤ s i := h_mono (Fin.zero_le _)
              dsimp [e2, myEquiv, mySuccAbove]
              split_ifs with h_τ_v
              · change (τ (e1.symm ⟨i, h⟩)).val < s i
                omega
              · change (τ (e1.symm ⟨i, h⟩)).val + 1 < s i
                omega
          have ha : a ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ 0 = v ∧ ∀ i, (σ i).val < s i) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨ha_v, ha_lt⟩
          exact ⟨a, ha, by
            ext x
            have h_x_ne : (e1 x).val ≠ 0 := (e1 x).2
            have h_ax : a (e1 x) = (e2 (τ x)).val := by
              dsimp [a]
              rw [dif_neg h_x_ne]
              have h_eta : (⟨(e1 x).val, h_x_ne⟩ : {y : Fin (k+1) // y ≠ 0}) = e1 x := Subtype.ext rfl
              rw [h_eta, Equiv.symm_apply_apply]
            have h_ax_prop : a (e1 x) ≠ v := by rw [h_ax]; exact (e2 (τ x)).2
            have h_eq : (⟨a (e1 x), h_ax_prop⟩ : {y : Fin (k+1) // y ≠ v}) = e2 (τ x) := Subtype.ext h_ax
            have h_res : e2.symm ⟨a (e1 x), h_ax_prop⟩ = τ x := by
              calc
                e2.symm ⟨a (e1 x), h_ax_prop⟩ = e2.symm (e2 (τ x)) := congrArg e2.symm h_eq
                _ = τ x := Equiv.symm_apply_apply e2 (τ x)
            exact congrArg Fin.val h_res⟩
      rw [h_sum, h_sum_eval, Finset.sum_const, smul_eq_mul]
      congr 1
      have h_bound0 : s 0 ≤ k + 1 := h_bound 0
      have h_card_v : (Finset.univ.filter (fun v : Fin (k + 1) => v.val < s 0)).card = s 0 := by
        have h_eq : (Finset.univ.filter (fun v : Fin (k + 1) => v.val < s 0)).card = (Finset.range (s 0)).card := by
          apply Finset.card_bij (fun v _ => v.val)
          · intro v hv; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
            exact Finset.mem_range.mpr hv
          · intro _ _ _ _ h; exact Fin.ext h
          · intro y hy
            have hy' := Finset.mem_range.mp hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨y, by omega⟩, hy', rfl⟩
        rw [h_eq, Finset.card_range]
      rw [h_card_v]
    rw [h_decomp]
    let s' : Fin k → ℕ := fun j => s (Fin.succ j) - 1
    have h_mono' : Monotone s' := by
      intro a b hab
      have hab' : Fin.succ a ≤ Fin.succ b := by
        have : a.val ≤ b.val := hab
        have h_succ_a : (Fin.succ a).val = a.val + 1 := rfl
        have h_succ_b : (Fin.succ b).val = b.val + 1 := rfl
        omega
      have := h_mono hab'
      dsimp [s']
      omega
    have h_bound' : ∀ j, s' j ≤ k := by
      intro j
      dsimp [s']
      have := h_bound (Fin.succ j)
      omega
    rw [ih s' h_mono' h_bound']
    -- Re-index the product
    have h_prod : ∏ i : Fin (k + 1), (s i - i.val) = (s 0 - 0) * ∏ j : Fin k, (s (Fin.succ j) - (Fin.succ j).val) := by
      exact Fin.prod_univ_succ (fun i => s i - i.val)
    rw [h_prod]
    have h_s0 : s 0 - 0 = s 0 := by omega
    rw [h_s0]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    dsimp [s']
    have : (Fin.succ j).val = j.val + 1 := by rfl
    omega

/--
Explicit sorting permutation for the even case bounds.
-/
def p_fun_even (m : ℕ) (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if h : i.val < m then
    ⟨2 * (m - 1 - i.val) + 1, by omega⟩
  else
    ⟨2 * (i.val - m), by omega⟩

lemma p_fun_even_inj (m : ℕ) : Function.Injective (p_fun_even m) := by
  intro a b hab
  dsimp [p_fun_even] at hab
  split_ifs at hab with h1 h2 h3 h4
  · simp only [Fin.mk.injEq] at hab
    have : a.val = b.val := by omega
    exact Fin.eq_of_val_eq this
  · simp only [Fin.mk.injEq] at hab
    have h_odd : (2 * (m - 1 - a.val) + 1) % 2 = 1 := by omega
    have h_even : (2 * (b.val - m)) % 2 = 0 := by omega
    rw [hab] at h_odd
    omega
  · simp only [Fin.mk.injEq] at hab
    have h_even : (2 * (a.val - m)) % 2 = 0 := by omega
    have h_odd : (2 * (m - 1 - b.val) + 1) % 2 = 1 := by omega
    rw [hab] at h_even
    omega
  · simp only [Fin.mk.injEq] at hab
    have : a.val = b.val := by omega
    exact Fin.eq_of_val_eq this

noncomputable def p_equiv_even (m : ℕ) : Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.ofBijective (p_fun_even m) (Finite.injective_iff_bijective.mp (p_fun_even_inj m))

lemma p_equiv_even_apply (m : ℕ) (i : Fin (2 * m + 1)) :
    let s : Fin (2 * m + 1) → ℕ := fun j => if j.val < 2 * m then m + j.val / 2 + 1 else 2 * m + 1
    s (p_equiv_even m i) = max (i.val + 1) (2 * m - i.val) := by
  intro s
  dsimp [s, p_equiv_even, p_fun_even]
  by_cases h1 : i.val < m
  · rw [dif_pos h1]
    dsimp
    have h_lt : 2 * (m - 1 - i.val) + 1 < 2 * m := by omega
    rw [if_pos h_lt]
    have h_div : (2 * (m - 1 - i.val) + 1) / 2 = m - 1 - i.val := by omega
    rw [h_div]
    have h_max : max (i.val + 1) (2 * m - i.val) = 2 * m - i.val := by exact max_eq_right (by omega)
    rw [h_max]
    omega
  · rw [dif_neg h1]
    dsimp
    by_cases h2 : i.val < 2 * m
    · have h_lt3 : 2 * (i.val - m) < 2 * m := by omega
      rw [if_pos h_lt3]
      have h_div2 : 2 * (i.val - m) / 2 = i.val - m := by omega
      rw [h_div2]
      have h_max2 : max (i.val + 1) (2 * m - i.val) = i.val + 1 := by exact max_eq_left (by omega)
      rw [h_max2]
      omega
    · have h_eq : i.val = 2 * m := by omega
      have h_ge2 : ¬(2 * (i.val - m) < 2 * m) := by omega
      rw [if_neg h_ge2]
      have h_max3 : max (i.val + 1) (2 * m - i.val) = i.val + 1 := by exact max_eq_left (by omega)
      rw [h_max3]
      omega

/--
Reordering lemma for permutation bounds.
-/
theorem card_perm_le_bounds_reorder (s : Fin n → ℕ) (p : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, (σ i).val < s (p i))).card =
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, (σ i).val < s i)).card := by
  -- Bijection: σ ↦ σ * p⁻¹, inverse τ ↦ τ * p
  apply Finset.card_bij (fun σ _ => σ * p.symm)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    intro i
    have h := hσ (p.symm i)
    simp only [Equiv.Perm.mul_apply, Equiv.apply_symm_apply] at h ⊢
    exact h
  · intro σ₁ _ σ₂ _ h
    exact mul_right_cancel h
  · intro τ hτ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
    have hmem : τ * p ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, (σ i).val < s (p i)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i; rw [Equiv.Perm.mul_apply]; exact hτ (p i)
    exact ⟨τ * p, hmem, by simp [mul_assoc]⟩

/--
Lemma: Number of permutations satisfying a(i) bounds.
This is the combinatorial core of Phase 4.
-/
theorem card_perm_max_bounds_even :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m + 1)) =>
      ∀ i : Fin (2 * m + 1), (σ i).val + 1 ≤ max (i.val + 1) (2 * m - i.val))).card =
    Nat.factorial m * Nat.factorial (m + 1) := by
  -- 1. Rewrite the inequality to strict inequality
  have h_eq : (fun σ : Equiv.Perm (Fin (2 * m + 1)) => ∀ i, (σ i).val + 1 ≤ max (i.val + 1) (2 * m - i.val)) =
              (fun σ : Equiv.Perm (Fin (2 * m + 1)) => ∀ i, (σ i).val < max (i.val + 1) (2 * m - i.val)) := by
    ext σ; simp only [Nat.succ_le_iff]
  simp_rw [h_eq]
  -- 2. Define the sorted monotone sequence s
  let s : Fin (2 * m + 1) → ℕ := fun j => if j.val < 2 * m then m + j.val / 2 + 1 else 2 * m + 1
  have h_mono : Monotone s := by
    intro a b hab
    dsimp [s]; split_ifs <;> omega
  have h_bound : ∀ i, s i ≤ 2 * m + 1 := by
    intro i
    dsimp [s]; split_ifs <;> omega
  -- 3. The reordering step: the graceful bounds max (i+1) (2m-i) is a permutation of s.
  -- Thus, the cardinality of the filtered permutations is equal to the cardinality with s.
  have h_reorder : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m + 1)) => ∀ i, (σ i).val < max (i.val + 1) (2 * m - i.val))).card =
                   (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m + 1)) => ∀ i, (σ i).val < s i)).card := by
    have h_p : ∀ i, s (p_equiv_even m i) = max (i.val + 1) (2 * m - i.val) := p_equiv_even_apply m
    simp_rw [← h_p]
    exact card_perm_le_bounds_reorder s (p_equiv_even m)
  rw [h_reorder]
  -- 4. Apply count_perm_le_product to count the sorted permutation set
  rw [count_perm_le_product s h_mono h_bound]
  -- 5. Split the product into the first 2m terms and the last term
  rw [Fin.prod_univ_castSucc]
  -- The last term is s(last) - last = (2m+1) - 2m = 1
  have h_last : s (Fin.last (2 * m)) - (Fin.last (2 * m) : ℕ) = 1 := by
    dsimp [s]
    split_ifs <;> omega
  rw [h_last, mul_one]
  -- Now we show that for i < 2m, s (Fin.castSucc i) is exactly m + i/2 + 1
  have h_cast : ∀ i : Fin (2 * m), s (Fin.castSucc i) = m + (i : ℕ) / 2 + 1 := by
    intro i
    dsimp [s]
    have h_lt : (i : ℕ) < 2 * m := i.isLt
    rw [if_pos h_lt]
  -- Rewrite the product to use product_formula_even
  have h_prod_eq : ∏ i : Fin (2 * m), (s (Fin.castSucc i) - (Fin.castSucc i : ℕ)) =
                   ∏ i : Fin (2 * m), (m + (i : ℕ) / 2 + 1 - (i : ℕ)) := by
    congr 1; ext i
    rw [h_cast i, Fin.val_castSucc]
  rw [h_prod_eq]
  -- 6. Apply product_formula_even to evaluate the product to m! * (m+1)!
  rw [product_formula_even]



end KRR
