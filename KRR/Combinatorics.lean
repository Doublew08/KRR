import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open BigOperators

namespace KRR

/-- 
The number of permutations σ of {1, ..., k} such that σ(i) ≤ max(i, k-i).
Even case: k = 2m.
-/
theorem card_perm_max_bounds_even (m : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m)) =>
      ∀ i : Fin (2 * m), (σ i).val + 1 ≤ max (i.val + 1) (2 * m - i.val))).card = 
    (Nat.factorial m) ^ 2 := by
  rcases m with rfl | m
  · simp
  rcases m with rfl
  · -- m = 1 case (k = 2)
    simp only [Nat.factorial_one, one_pow, Nat.mul_one, Nat.zero_add]
    have : (Finset.univ : Finset (Equiv.Perm (Fin 2))).card = 2 := by simp
    rw [← this, Finset.card_eq_filter_iff]
    intro σ _ i
    simp only [Nat.reduceMax]
    fin_cases i
    · simp; omega
    · simp; omega
  rcases m with rfl
  · -- m = 2 case (k = 4)
    simp only [Nat.factorial_two, pow_two, Nat.reduceMax]
    have : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = 24 := by simp
    rw [Finset.filter_card]
    -- We expect 4 permutations
    -- Fin 4 = {0, 1, 2, 3}. Bounds: σ(0) ≤ 2, σ(1) ≤ 1, σ(2) ≤ 2, σ(3) ≤ 3
    -- Sorted: σ(1) ≤ 1, σ(0) ≤ 2, σ(2) ≤ 2, σ(3) ≤ 3
    -- Choices: (1+1) * (2-1+1) * (2-2+1) * (3-3+1) = 2 * 2 * 1 * 1 = 4.
    decide
  · sorry

/-- 
The number of permutations σ of {1, ..., k} such that σ(i) ≤ max(i, k-i).
Odd case: k = 2m + 1.
-/
theorem card_perm_max_bounds_odd (m : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m + 1)) =>
      ∀ i : Fin (2 * m + 1), (σ i).val + 1 ≤ max (i.val + 1) (2 * m + 1 - i.val))).card = 
    Nat.factorial m * Nat.factorial (m + 1) := by
  rcases m with rfl | m
  · simp only [Nat.factorial_zero, Nat.factorial_one, Nat.mul_one, Nat.zero_add]
    -- Fin 1 case
    have : (Finset.univ : Finset (Equiv.Perm (Fin 1))).card = 1 := by simp
    rw [← this, Finset.card_eq_filter_iff]
    intro σ _ i
    fin_cases i; simp
  rcases m with rfl
  · -- m = 1 case (k = 3)
    simp only [Nat.factorial_one, Nat.factorial_two, Nat.mul_one, Nat.reduceMax]
    have : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by simp
    rw [Finset.filter_card]
    -- We expect 2 permutations
    -- Fin 3 = {0, 1, 2}. Bounds: σ(0) ≤ 1, σ(1) ≤ 1, σ(2) ≤ 2
    -- σ(0), σ(1) must be {0, 1} in some order. σ(2) must be 2.
    -- (0, 1, 2) and (1, 0, 2).
    decide
  · sorry

/-- 
General product formula for counting permutations with upper bounds.
If a_j is a non-decreasing sequence of bounds, the number of permutations 
σ such that σ(j) ≤ a_j is ∏ (a_j - j + 1).
-/
theorem count_perm_le_product {k : ℕ} (a : Fin k → ℕ) (ha : Monotone a) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => ∀ j, (σ j).val ≤ a j)).card = 
    ∏ j : Fin k, (a j - j.val + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    let a' (i : Fin k) : ℕ := a i.succ
    have ha' : Monotone a' := fun i j h => ha (Fin.succ_le_succ h)
    -- Sequential choice argument: σ(0) has (a 0 + 1) choices.
    -- Each subsequent σ(j) has (a j - j + 1) choices.
    sorry

/-- 
Permutations of α fixing a point are equivalent to permutations of the remaining elements.
-/
/- 
def permFixEquiv {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    {σ : Equiv.Perm α // σ a = a} ≃ Equiv.Perm {x // x ≠ a} :=
  Equiv.subtypePermEquivSubtypePerm (fun σ => σ a = a) (fun σ => ∀ x, x ≠ a → σ x ≠ a)
    (fun σ h => by 
      intro x hx; intro heq; 
      have := σ.injective (heq.trans h.symm); exact hx this)
    (fun σ h => by 
      use a; constructor; swap; exact h;
      intro x hx; rcases Decidable.eq_or_ne x a with rfl | hne
      · exact h
      · exact (h x hne).elim)
  -- This is a bit complex to prove fully, but the statement is correct.
  sorry
-/

end KRR
