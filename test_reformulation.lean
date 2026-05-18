import KRR.Basic
import KRR.Graceful
import KRR.Combinatorics
import KRR.FunctionalReformulation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

open Finset
open Equiv
open KRR

variable {n : ℕ}

-- We want to prove:
theorem count_valid_bases_eq_proof (hn : 0 < n) (h2 : 2 < n) :
    (Finset.univ.filter (fun γ : Equiv.Perm (Fin n) =>
      γ ⟨0, hn⟩ = ⟨0, hn⟩ ∧
      ∀ i : Fin n, i.val > 0 →
        (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val)).card =
    Nat.factorial ((n - 1) / 2) * Nat.factorial (((n - 1) + 1) / 2) := by
  sorry

