import Mathlib
open Equiv

variable (n : ℕ) (hn : 0 < n)

-- Let S be the type of elements of Fin n not equal to 0
def NonZeroFin := {x : Fin n // x ≠ ⟨0, hn⟩}

-- We can map NonZeroFin to Fin (n-1)
def nonZeroFinEquiv : NonZeroFin n hn ≃ Fin (n - 1) where
  toFun x := ⟨x.1.val - 1, by have := x.1.isLt; omega⟩
  invFun y := ⟨⟨y.val + 1, by have := y.isLt; omega⟩, by omega⟩
  left_inv := fun ⟨⟨x_val, h_lt⟩, h_gt⟩ => by simp; exact Subtype.ext (Fin.ext (by omega))
  right_inv := fun ⟨y_val, h_lt⟩ => by simp

-- A permutation of Fin n fixing 0 restricts to a permutation of NonZeroFin
def permFixZeroEquiv : {γ : Equiv.Perm (Fin n) // γ ⟨0, hn⟩ = ⟨0, hn⟩} ≃ Equiv.Perm (NonZeroFin n hn) :=
  Equiv.Perm.subtypeEquivSubtype (fun x => x ≠ ⟨0, hn⟩) (fun γ hγ => by
    -- wait, subtypeEquivSubtype might not exist. Let's check.
    sorry
  )
