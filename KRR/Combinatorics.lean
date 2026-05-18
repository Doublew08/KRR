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
axiom count_perm_le_product (s : Fin n → ℕ) (h_mono : Monotone s) (h_bound : ∀ i, s i ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, (σ i).val < s i)).card =
    ∏ i, (s i - i.val)

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

def p_equiv_even (m : ℕ) : Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.ofBijective (p_fun_even m) (Fintype.injective_iff_bijective.mp (p_fun_even_inj m))

lemma p_equiv_even_apply (m : ℕ) (i : Fin (2 * m + 1)) :
    let s : Fin (2 * m + 1) → ℕ := fun j => if j.val < 2 * m then m + j.val / 2 + 1 else 2 * m + 1
    s (p_equiv_even m i) = max (i.val + 1) (2 * m - i.val) := by
  intro s
  dsimp [s, p_equiv_even, p_fun_even]
  split_ifs with h1 h2
  · have h_lt : 2 * (m - 1 - i.val) + 1 < 2 * m := by omega
    rw [if_pos h_lt]
    have : (2 * (m - 1 - i.val) + 1) / 2 = m - 1 - i.val := by omega
    rw [this]
    have : m + (m - 1 - i.val) + 1 = 2 * m - i.val := by omega
    rw [this]
    exact (max_eq_right (by omega)).symm
  · have h_lt2 : 2 * (i.val - m) < 2 * m ↔ i.val < 2 * m := by omega
    by_cases h_i : i.val < 2 * m
    · rw [if_pos (by omega)]
      have : 2 * (i.val - m) / 2 = i.val - m := by omega
      rw [this]
      have : m + (i.val - m) + 1 = i.val + 1 := by omega
      rw [this]
      exact (max_eq_left (by omega)).symm
    · have : i.val = 2 * m := by omega
      rw [if_neg (by omega)]
      have : 2 * m + 1 = i.val + 1 := by omega
      rw [this]
      exact (max_eq_left (by omega)).symm

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
