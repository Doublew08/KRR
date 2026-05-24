import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Finset.Basic

open Finset
open Equiv

namespace KRR

variable {k : ℕ}

/--
Helper: Equivalence between {x : Fin (k+1) // x ≠ Fin.last k} and Fin k
-/
def castSuccEquiv : {x : Fin (k + 1) // x ≠ Fin.last k} ≃ Fin k where
  toFun x := ⟨x.1.val, by
    have h1 := x.1.isLt
    have h2 := x.2
    have : x.1.val ≠ k := by
      intro h
      apply h2
      exact Fin.ext h
    omega⟩
  invFun y := ⟨Fin.castSucc y, by
    intro h
    have : (Fin.castSucc y).val = k := by rw [h]; rfl
    have : y.val = k := this
    have := y.isLt
    omega⟩
  left_inv := fun ⟨x_val, h_neq⟩ => by simp; exact Subtype.ext (Fin.ext rfl)
  right_inv := fun y => by simp; exact Fin.ext rfl

/--
Helper: Equivalence between {x : Fin (k+1) // x ≠ v} and Fin k
-/
def succAboveEquiv (v : Fin (k + 1)) : {x : Fin (k + 1) // x ≠ v} ≃ Fin k where
  toFun x := if h : x.1.val < v.val then
               ⟨x.1.val, by omega⟩
             else
               ⟨x.1.val - 1, by
                 have h_neq := x.2
                 have h_lt := x.1.isLt
                 have : x.1.val ≠ v.val := fun eq => h_neq (Fin.ext eq)
                 omega⟩
  invFun y := if h : y.val < v.val then
                ⟨⟨y.val, by omega⟩, by
                  intro eq
                  have : y.val = v.val := congrArg Fin.val eq
                  omega⟩
              else
                ⟨⟨y.val + 1, by omega⟩, by
                  intro eq
                  have : y.val + 1 = v.val := congrArg Fin.val eq
                  omega⟩
  left_inv := by
    rintro ⟨⟨x_val, hx_lt⟩, hx_neq⟩
    apply Subtype.ext
    apply Fin.ext
    dsimp
    by_cases h : x_val < v.val
    · rw [dif_pos h]
      dsimp
      rw [dif_pos h]
    · rw [dif_neg h]
      dsimp
      have h2 : ¬(x_val - 1 < v.val) := by 
        have : x_val ≠ v.val := fun eq => hx_neq (Fin.ext eq)
        omega
      rw [dif_neg h2]
      dsimp
      omega
  right_inv := by
    rintro ⟨y_val, hy_lt⟩
    apply Fin.ext
    dsimp
    by_cases h : y_val < v.val
    · rw [dif_pos h]
      dsimp
      rw [dif_pos h]
    · rw [dif_neg h]
      dsimp
      have h2 : ¬(y_val + 1 < v.val) := by omega
      rw [dif_neg h2]
      dsimp
      omega

lemma succAboveEquiv_lt (v : Fin (k + 1)) (x : {x : Fin (k + 1) // x ≠ v}) (S : ℕ) (hv : v.val < S) :
    (x.1.val < S) ↔ ((succAboveEquiv v x).val < S - 1) := by
  dsimp [succAboveEquiv]
  by_cases h : x.1.val < v.val
  · rw [dif_pos h]
    dsimp
    constructor
    · intro _
      omega
    · intro _
      omega
  · rw [dif_neg h]
    dsimp
    constructor
    · intro hx
      omega
    · intro hx
      have h_neq := x.2
      have : x.1.val ≠ v.val := fun eq => h_neq (Fin.ext eq)
      omega

end KRR
