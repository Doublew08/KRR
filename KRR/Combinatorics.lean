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
    -- Sequential choice: for each permutation of Fin k satisfying the bounds,
    -- there are exactly (a k - k + 1) choices for σ(k) such that σ is a permutation of Fin (k+1).
    -- This is because a is monotone, so a(j) ≤ a(k) for all j < k.
    -- Thus σ(0), ..., σ(k-1) are all in {0, ..., a k}.
    -- The number of available values in {0, ..., a k} is (a k + 1) - k = a k - k + 1.
    set f := fun (σ : Equiv.Perm (Fin k)) => 
      (Finset.univ.filter (fun (x : Fin (k + 1)) => x.val ≤ a (Fin.last k) ∧ ∀ j, x ≠ σ j)).card
    have h_card : ∀ σ, (∀ j, (σ j).val ≤ a (Fin.castSucc j)) → 
        (Finset.univ.filter (fun (x : Fin (k + 1)) => x.val ≤ a (Fin.last k) ∧ ∀ j : Fin k, x ≠ Fin.castSucc (σ j))).card = 
        (a (Fin.last k) - k + 1) := by
      intro σ hσ
      let S := Finset.univ.filter (fun (x : Fin (k + 1)) => x.val ≤ a (Fin.last k))
      let T := (Finset.univ : Finset (Fin k)).image (fun j => Fin.castSucc (σ j))
      have hT_sub : T ⊆ S := by
        intro y hy; simp at hy; obtain ⟨j, rfl⟩ := hy
        simp [S]; calc (Fin.castSucc (σ j)).val = (σ j).val := by rfl
          _ ≤ a (Fin.castSucc j) := hσ j
          _ ≤ a (Fin.last k) := ha (Fin.castSucc_le_last j)
      have hS_card : S.card = a (Fin.last k) + 1 := by
        rw [Finset.filter_range (fun x => x ≤ a (Fin.last k))]
        · simp; omega
        · exact fun _ => by rfl
      have hT_card : T.card = k := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro j1 j2 heq; exact σ.injective (Fin.castSucc_injective heq)
      have : (S \ T).card = S.card - T.card := Finset.card_sdiff hT_sub
      rw [this, hS_card, hT_card] at *
      have : S \ T = Finset.univ.filter (fun (x : Fin (k + 1)) => x.val ≤ a (Fin.last k) ∧ ∀ j : Fin k, x ≠ Fin.castSucc (σ j)) := by
        ext x; simp [S, T]; aesop
      rw [← this]
      omega
    -- Now relate permutations of Fin (k+1) to permutations of Fin k and choice of σ(k)
    -- This part is technically involved in Lean, using Equiv.extend_perm or similar.
    -- We'll use a simpler counting argument if possible.
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
