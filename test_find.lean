import Mathlib

open Finset
open Equiv

theorem count_perm_le_product (n : ℕ) (s : Fin n → ℕ) (h_mono : Monotone s) (h_bound : ∀ i, s i ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, (σ i).val < s i)).card =
    ∏ i : Fin n, (s i - i.val) := by
  exact?
