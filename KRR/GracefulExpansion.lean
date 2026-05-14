import KRR.Basic
import KRR.Graceful
import KRR.FunctionalReformulation
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs

/-!
# Phase 4: Graceful Expansion Theorem

This module formalizes Theorem 2.1 from the Gnang paper, which provides
an algebraic expansion for graceful labelings of functional digraphs.

Theorem 2.1: 
f(i) = σ⁻¹ · φ^t (φ^t(σ(i)) + (-1)^t · 𝔰_f(γ, σ(i)) · γ(σ(i)))
-/

namespace KRR

variable {n : ℕ}

/--
Theorem 2.1 (Graceful Expansion):
Every graceful labeling σ of a functional tree f admits an expansion:
  σ(f(i)) = σ(i) + s_f(σ(i)) * γ(σ(i))
where γ is a valid permutation basis and s_f is the sign function.
-/
theorem graceful_expansion (hn : 1 < n) (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n))
    (h_tree : IsTreeFunction f)
    (h_graceful : IsAlreadyGraceful (conjugate f σ))
    (h_canonical : IsCanonicalTreeFunction (by omega) (conjugate f σ)) :

    ∃ (γ : Equiv.Perm (Fin n)), 
      IsValidPermutationBasis (by omega) γ ∧ 
      ∀ i : Fin n, 
    (conjugate f σ) i = ⟨Int.natAbs (↑i.val + (signFunction f σ γ i) * ↑(γ i).val), by
      have h_id : (Int.natAbs (↑i.val + (signFunction f σ γ i) * ↑(γ i).val)) = (conjugate f σ i).val := by
        let g := conjugate f σ
        unfold signFunction
        split_ifs with h_loop h_lt
        · simp [h_loop]
        · have h_gamma : (γ i).val = (g i).val - i.val := by
            simp [γ, γ_fun]; rw [Int.natAbs_of_nonneg]; omega
          simp [h_gt, h_gamma]; omega
        · have h_gamma : (γ i).val = i.val - (g i).val := by
            simp [γ, γ_fun]; rw [Int.natAbs_of_nonneg]; omega
          simp [h_lt, h_gamma]; omega

      rw [h_id]
      exact (conjugate f σ i).isLt⟩ := by

  let g := conjugate f σ
  -- Define γ(i) = |g(i) - i|
  let γ_fun : Fin n → Fin n := fun i => 
    ⟨Int.natAbs (g i - i), by
      have h1 : (g i).val < n := (g i).isLt
      have h2 : i.val < n := i.isLt
      omega⟩
  -- Show γ is a permutation
  have h_inj : Function.Injective γ_fun := by
    have h_surj : ∀ k : Fin n, ∃ i, γ_fun i = k := by
      intro k
      have h_range : Finset.image γ_fun Finset.univ = Finset.range n := by
        apply Finset.eq_of_subset_of_card_le
        · intro x hx; simp at hx; obtain ⟨i, rfl⟩ := hx; exact x.isLt
        · rw [h_graceful, Finset.card_range]
      have : k ∈ Finset.range n := Finset.mem_range.mpr k.isLt
      rw [← h_range] at this; simp at this; exact this
    exact Fintype.injective_iff_surjective.mpr h_surj hij

  let γ : Equiv.Perm (Fin n) := Equiv.ofBijective γ_fun (Fintype.injective_iff_bijective.mpr ⟨h_inj, by simp⟩)
  use γ
  constructor
  · -- IsValidPermutationBasis
    constructor
    · simp [γ, γ_fun]
      -- Since g is a tree function, g(0) = 0.
      have hg0 : g 0 = 0 := h_canonical.1
      simp [hg0]


    · intro i hi
      simp [γ, γ_fun]
      rcases Int.natAbs_eq (g i - i) with h | h
      · -- g i - i = label
        right; have := (g i).isLt; omega
      · -- g i - i = -label
        left; have := i.isLt; omega
  · intro i
    simp [signFunction, g, γ, γ_fun]
    split_ifs with h1 h2
    · -- g i = i. label = 0.
      simp [h1]
    · -- g i < i. sign = -1.
      simp at h2
      have h_abs : Int.natAbs (↑(g i).val - ↑i.val) = i.val - (g i).val := by
        rw [Int.natAbs_eq_iff]; left; omega
      rw [h_abs]; simp; omega
    · -- g i > i. sign = 1.
      simp at h2
      have h_abs : Int.natAbs (↑(g i).val - ↑i.val) = (g i).val - i.val := by
        rw [Int.natAbs_eq_iff]; right; omega
      rw [h_abs]; simp; omega



end KRR
