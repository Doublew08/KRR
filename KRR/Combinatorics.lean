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
  cases m with
  | zero => -- m = 0 case (k = 0)
    simp
  | succ m =>
    rcases m with rfl
    · -- m = 1 case (k = 2)
      simp only [Nat.factorial_one, one_pow, Nat.mul_one, Nat.zero_add]
    have : (Finset.univ : Finset (Equiv.Perm (Fin 2))).card = 2 := by simp
    rw [Finset.filter_card]
    decide
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
  cases m with
  | zero => -- m = 0 case (k = 1)
    simp only [Nat.factorial_zero, Nat.factorial_one, Nat.mul_one, Nat.zero_add]
    have : (Finset.univ : Finset (Equiv.Perm (Fin 1))).card = 1 := by simp
    rw [Finset.filter_card]
    decide
  | succ m =>
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
    let S := Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => ∀ j, (σ j).val ≤ a j)
    let f (σ : Equiv.Perm (Fin (k + 1))) : Fin k → Fin k := sorry -- Relabeling
    -- Use the fact that for each σ' on Fin k, there are (a k - k + 1) extensions.
    sorry

/-- 
Permutations of α fixing a point are equivalent to permutations of the remaining elements.
-/
def permFixEquiv {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    {σ : Equiv.Perm α // σ a = a} ≃ Equiv.Perm {x // x ≠ a} :=
  Equiv.subtypePermEquiv (fun σ => σ a = a) (fun σ => ∀ x, x ≠ a → σ x ≠ a)
    (fun σ h => by 
      intro x hx; intro heq; 
      have := σ.injective (heq.trans h.symm); exact hx this)
    (fun σ h => by 
      use a; constructor; swap; exact h;
      intro x hx; rcases Decidable.eq_or_ne x a with rfl | hne
      · exact h
      · exact (h x hne).elim)

end KRR
