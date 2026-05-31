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
      IsValidPermutationBasis γ ∧
      ∀ i : Fin n,
        ((conjugate f σ) i).val = Int.natAbs (↑i.val + (signFunction γ i) * ↑(γ i).val) := by
  let g := conjugate f σ
  have hg_canon := h_canonical.1
  have hg_lt : ∀ i, i.val > 0 → (g i).val < i.val := h_canonical.2
  
  let labelMap (i : Fin n) : ℕ := Int.natAbs ((g i).val - i.val)
  
  have h_label_lt (i : Fin n) : labelMap i < n := by
    dsimp [labelMap]
    have h1 := i.isLt
    have h2 := (g i).isLt
    omega
    
  let valMap (i : Fin n) : Fin n := ⟨labelMap i, h_label_lt i⟩
  
  have h_img : Finset.univ.image valMap = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Fintype.card_fin]
    have h1 : (Finset.univ.image valMap).card = (edgeLabelSet g).card := by
      have h_eq : edgeLabelSet g = (Finset.univ.image valMap).image (fun x : Fin n => x.val) := by
        ext k
        simp only [edgeLabelSet, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨valMap i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
      rw [h_eq]
      exact (Finset.card_image_of_injective _ Fin.val_injective).symm
    rw [h1]
    exact h_graceful
  
  have h_surj : Function.Surjective valMap := by
    intro y
    have hy : y ∈ Finset.univ := Finset.mem_univ y
    rw [← h_img, Finset.mem_image] at hy
    rcases hy with ⟨x, _, hx⟩
    exact ⟨x, hx⟩
    
  have h_bij : Function.Bijective valMap :=
    (Fintype.bijective_iff_surjective_and_card valMap).mpr ⟨h_surj, rfl⟩
    
  let γ := Equiv.ofBijective valMap h_bij
  
  use γ
  have hn0 : 0 < n := by omega
  constructor
  · -- IsValidPermutationBasis γ : ∀ i > 0, (γ i).val ≤ i.val ∨ …
    dsimp [IsValidPermutationBasis]
    intro i hi
    left
    have hl : (g i).val < i.val := hg_lt i hi
    have hγnat : (γ i).val = Int.natAbs ((g i).val - i.val : ℤ) := by
      dsimp [γ, Equiv.ofBijective, valMap, labelMap]
    omega
  · intro i
    change (g i).val = Int.natAbs (↑i.val + signFunction γ i * ↑(γ i).val)
    have hle : (g i).val ≤ i.val := by
      rcases Nat.eq_zero_or_pos i.val with h0 | hpos
      · have hi0 : i = ⟨0, hn0⟩ := Fin.ext h0
        have h_g0 : g ⟨0, hn0⟩ = ⟨0, hn0⟩ := h_canonical.1
        have heq : (g i).val = i.val := by rw [hi0, h_g0]
        omega
      · exact le_of_lt (hg_lt i hpos)
    have hγnat : (γ i).val = Int.natAbs ((g i).val - i.val : ℤ) := by
      dsimp [γ, Equiv.ofBijective, valMap, labelMap]
    have hsum : (g i).val + (γ i).val = i.val := by omega
    have hsign : signFunction γ i = -1 := by
      dsimp [signFunction]
      rw [if_pos (show (γ i).val ≤ i.val by omega)]
    rw [hsign]
    omega

end KRR
