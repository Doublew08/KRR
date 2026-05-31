import KRR.Basic
import KRR.Combinatorics
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

def IsValidPermutationBasis {n : ℕ} (γ : Equiv.Perm (Fin n)) : Prop :=
  -- Evaluated on an edge `e = {x, y}`, the weight `x - y` modulo `n`
  -- gives a sum that must be unique. To represent `c_{γ(x), γ(y)}`,
  -- the valid choices reduce to ensuring the permutation doesn't map
  -- diametrically opposite vertices to valid sets.
  -- This is formalized via bounds on the permutation values.
  ∀ i : Fin n, i.val > 0 → (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val

-- Sign of the signed edge displacement for a canonical labeling: for a
-- canonical tree function `g i ≤ i`, so `γ i = |g i − i| = i − g i ≤ i` and
-- the displacement `g i − i ≤ 0` carries sign `-1`.
def signFunction {n : ℕ} (γ : Equiv.Perm (Fin n)) : Fin n → ℤ
  | i => if (γ i).val ≤ i.val then -1 else 1

def p_fun_odd (m : ℕ) (i : Fin (2 * m)) : Fin (2 * m) :=
  if h : i.val < m then
    ⟨2 * (m - 1 - i.val), by omega⟩
  else
    ⟨2 * (i.val - m) + 1, by omega⟩

lemma p_fun_odd_inj (m : ℕ) : Function.Injective (p_fun_odd m) := by
  intro a b hab
  dsimp [p_fun_odd] at hab
  split_ifs at hab with h1 h2 h3 h4
  · simp only [Fin.mk.injEq] at hab; omega
  · simp only [Fin.mk.injEq] at hab
    have h_even : (2 * (m - 1 - a.val)) % 2 = 0 := by omega
    have h_odd : (2 * (b.val - m) + 1) % 2 = 1 := by omega
    rw [hab] at h_even; omega
  · simp only [Fin.mk.injEq] at hab
    have h_odd : (2 * (a.val - m) + 1) % 2 = 1 := by omega
    have h_even : (2 * (m - 1 - b.val)) % 2 = 0 := by omega
    rw [hab] at h_odd; omega
  · simp only [Fin.mk.injEq] at hab; omega

noncomputable def p_equiv_odd (m : ℕ) : Equiv.Perm (Fin (2 * m)) :=
  Equiv.ofBijective (p_fun_odd m) (Finite.injective_iff_bijective.mp (p_fun_odd_inj m))

lemma p_equiv_odd_apply (m : ℕ) (i : Fin (2 * m)) :
    let s : Fin (2 * m) → ℕ := fun j => m + (j.val + 1) / 2
    s (p_equiv_odd m i) = max (i.val + 1) (2 * m - 1 - i.val) := by
  intro s
  dsimp [s, p_equiv_odd, p_fun_odd]
  by_cases h1 : i.val < m
  · rw [dif_pos h1]
    dsimp
    have h_div : (2 * (m - 1 - i.val) + 1) / 2 = m - 1 - i.val := by omega
    rw [h_div]
    have h_max : max (i.val + 1) (2 * m - 1 - i.val) = 2 * m - 1 - i.val := by exact max_eq_right (by omega)
    rw [h_max]
    omega
  · rw [dif_neg h1]
    dsimp
    have h_div2 : (2 * (i.val - m) + 1 + 1) / 2 = i.val - m + 1 := by omega
    rw [h_div2]
    have h_max2 : max (i.val + 1) (2 * m - 1 - i.val) = i.val + 1 := by exact max_eq_left (by omega)
    rw [h_max2]
    omega

lemma prod_Fin_rev_fact (m : ℕ) : ∏ k : Fin m, (m - k.val) = m.factorial := by
  sorry

theorem product_formula_odd (m : ℕ) :
    (∏ j : Fin (2 * m), (m + ((j : ℕ) + 1) / 2 - (j : ℕ))) =
    (Nat.factorial m) * (Nat.factorial m) := by
  let e : Fin m × Fin 2 ≃ Fin (2 * m) :=
  { toFun  := fun ⟨k, b⟩ => ⟨2 * k.val + b.val, by have := k.isLt; have := b.isLt; omega⟩
    invFun := fun j => ⟨⟨j.val / 2, by have := j.isLt; omega⟩,
                        ⟨j.val % 2, Nat.mod_lt _ (by norm_num)⟩⟩
    left_inv := by
      rintro ⟨⟨k, hk⟩, ⟨b, hb⟩⟩
      simp only [Prod.mk.injEq, Fin.mk.injEq]; omega
    right_inv := by intro ⟨j, hj⟩; simp only [Fin.mk.injEq]; omega }
  calc (∏ j : Fin (2 * m), (m + ((j : ℕ) + 1) / 2 - (j : ℕ)))
      = (∏ p : Fin m × Fin 2, (m + ((e p : ℕ) + 1) / 2 - (e p : ℕ))) :=
          (Equiv.prod_comp e (fun j => m + ((j : ℕ) + 1) / 2 - (j : ℕ))).symm
    _ = (∏ k : Fin m, ∏ b : Fin 2, (m + ((e (k, b) : ℕ) + 1) / 2 - (e (k, b) : ℕ))) :=
          Fintype.prod_prod_type _
    _ = (∏ k : Fin m, ((m + ((e (k, 0) : ℕ) + 1) / 2 - (e (k, 0) : ℕ)) *
                       (m + ((e (k, 1) : ℕ) + 1) / 2 - (e (k, 1) : ℕ)))) := by
          congr 1; ext k; exact Fin.prod_univ_two _
    _ = (∏ k : Fin m, ((m - k.val) * (m - k.val))) := by
          congr 1; ext k
          simp only [e, Equiv.coe_fn_mk,
                     show (0 : Fin 2).val = 0 from rfl,
                     show (1 : Fin 2).val = 1 from rfl]
          have := k.isLt; congr 1 <;> omega
    _ = (∏ k : Fin m, (m - k.val)) * (∏ k : Fin m, (m - k.val)) :=
          Finset.prod_mul_distrib
    _ = m.factorial * m.factorial := by
          have h_subst : (∏ k : Fin m, (m - k.val)) = m.factorial := prod_Fin_rev_fact m
          rw [h_subst]

theorem card_perm_max_bounds_odd (m : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m)) =>
      ∀ i : Fin (2 * m), (σ i).val < max (i.val + 1) (2 * m - 1 - i.val))).card =
    Nat.factorial m * Nat.factorial m := by
  let s : Fin (2 * m) → ℕ := fun j => m + (j.val + 1) / 2
  have h_mono : Monotone s := by
    intro a b hab
    dsimp [s]; omega
  have h_bound : ∀ i, s i ≤ 2 * m := by
    intro i
    dsimp [s]; omega
  have h_reorder : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m)) => ∀ i, (σ i).val < max (i.val + 1) (2 * m - 1 - i.val))).card =
                   (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m)) => ∀ i, (σ i).val < s i)).card := by
    have h_p : ∀ i, s (p_equiv_odd m i) = max (i.val + 1) (2 * m - 1 - i.val) := p_equiv_odd_apply m
    simp_rw [← h_p]
    exact card_perm_le_bounds_reorder s (p_equiv_odd m)
  rw [h_reorder]
  rw [count_perm_le_product s h_mono h_bound]
  exact product_formula_odd m

lemma count_valid_bases_eq (hn : 0 < n) (h2 : 2 < n) :
    (Finset.univ.filter (fun γ : Equiv.Perm (Fin n) =>
      γ ⟨0, hn⟩ = ⟨0, hn⟩ ∧
      ∀ i : Fin n, i.val > 0 →
        (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val)).card =
    Nat.factorial ((n - 1) / 2) * Nat.factorial (((n - 1) + 1) / 2) := by
  have h_bij : (Finset.univ.filter (fun γ : Equiv.Perm (Fin n) =>
      γ ⟨0, hn⟩ = ⟨0, hn⟩ ∧
      ∀ i : Fin n, i.val > 0 →
        (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n - 1)) =>
        ∀ j : Fin (n - 1), (σ j).val < max (j.val + 1) (n - 1 - 1 - j.val))).card := by
    sorry
  rw [h_bij]
  by_cases hm_even : Even (n - 1)
  · rcases hm_even with ⟨m, hm_eq⟩
    have hm : n - 1 = 2 * m := by omega
    have h_card := card_perm_max_bounds_odd m
    have h_div1 : (n - 1) / 2 = m := by omega
    have h_div2 : ((n - 1) + 1) / 2 = m := by omega
    rw [h_div1, h_div2]
    have h_subst : 2 * m = n - 1 := by omega
    rw [h_subst] at h_card
    exact h_card
  · have hm_odd : Odd (n - 1) := by sorry
    rcases hm_odd with ⟨m, hm_eq⟩
    have hm : n - 1 = 2 * m + 1 := by omega
    have h_card := card_perm_max_bounds_even (m := m)
    have h_div1 : (n - 1) / 2 = m := by omega
    have h_div2 : ((n - 1) + 1) / 2 = m + 1 := by omega
    rw [h_div1, h_div2]
    have h_subst : 2 * m + 1 = n - 1 := by omega
    rw [h_subst] at h_card
    sorry

end KRR
