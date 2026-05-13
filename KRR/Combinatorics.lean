import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic

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
  let k := 2 * m
  let a (i : Fin k) : ℕ := max (i.val + 1) (k - (i.val + 1)) - 1
  -- Use count_perm_le_product after sorting a
  -- This requires showing that the card is the same for any permutation of the bounds
  sorry

/-- 
The number of permutations σ of {1, ..., k} such that σ(i) ≤ max(i, k-i).
Odd case: k = 2m + 1.
-/
theorem card_perm_max_bounds_odd (m : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m + 1)) =>
      ∀ i : Fin (2 * m + 1), (σ i).val + 1 ≤ max (i.val + 1) (2 * m + 1 - i.val))).card = 
    Nat.factorial m * Nat.factorial (m + 1) :=
  sorry

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
    -- Use the fact that any permutation σ of Fin (k+1) is 
    -- uniquely determined by σ(k) and a permutation of Fin k.
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
