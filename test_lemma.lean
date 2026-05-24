import Mathlib
open Finset

namespace KRR

variable {k : ℕ}

theorem h_sum_test (s : Fin (k+1) → ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => ∀ i, (σ i).val < s i)).card =
    ∑ v in Finset.univ.filter (fun v : Fin (k + 1) => v.val < s 0),
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ 0 = v ∧ ∀ i, (σ i).val < s i)).card := by
  have h_bind : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => ∀ i, (σ i).val < s i)) =
      (Finset.univ.filter (fun v : Fin (k + 1) => v.val < s 0)).biUnion
      (fun v => Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ 0 = v ∧ ∀ i, (σ i).val < s i)) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro hσ
      use σ 0
      refine ⟨by exact hσ 0, ⟨rfl, hσ⟩⟩
    · rintro ⟨v, _, hvσ⟩
      exact hvσ.2
  rw [h_bind, card_biUnion]
  intro v1 _ v2 _ hneq
  rw [disjoint_left]
  intro σ h1 h2
  rw [mem_filter] at h1 h2
  have eq1 := h1.2.1
  have eq2 := h2.2.1
  rw [← eq1, ← eq2] at hneq
  exact hneq rfl

end KRR
