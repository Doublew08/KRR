import Mathlib

open Finset
open Equiv

/--
The Inverse Permutation Bijection Theorem Scaffold.
To prove count_perm_le_product without sorry, we must map the bounds on σ to bounds on σ⁻¹.
-/
lemma filter_inv_equiv {n : ℕ} (s : Fin n → ℕ) (h_mono : Monotone s) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, (σ i).val < s i)).card =
    (Finset.univ.filter (fun τ : Equiv.Perm (Fin n) => 
      ∀ j, τ j ≥ (⟨min n (s ⟨j.val, sorry⟩), sorry⟩ : Fin n))).card := by
  -- By mapping σ ↦ σ⁻¹, we shift the upper bound s(i) to a lower bound on the index.
  sorry

theorem count_perm_le_product (n : ℕ) (s : Fin n → ℕ) (h_mono : Monotone s) (h_bound : ∀ i, s i ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, (σ i).val < s i)).card =
    ∏ i : Fin n, (s i - i.val) := by
  induction n with
  | zero => 
    have h_empty_prod : ∏ i : Fin 0, (s i - i.val) = 1 := Fintype.prod_empty
    rw [h_empty_prod]
    have h_perm_univ : (Finset.univ : Finset (Equiv.Perm (Fin 0))) = {Equiv.refl _} := rfl
    rw [h_perm_univ]
    have h_filter : ({Equiv.refl _} : Finset (Equiv.Perm (Fin 0))).filter (fun σ => ∀ i, (σ i).val < s i) = {Equiv.refl _} := by
      ext x
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨h1, _⟩; exact h1
      · intro h1; rw [h1]; exact ⟨rfl, fun i => i.elim0⟩
    rw [h_filter, card_singleton]
  | succ k ih =>
    -- We must apply filter_inv_equiv to convert this to a lower-bound problem.
    -- Then, assigning τ(k) gives exactly (s k - k) choices independently of previous elements.
    sorry
