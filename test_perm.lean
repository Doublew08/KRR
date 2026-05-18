import Mathlib
import KRR.Basic
import KRR.Graceful

open Finset
open Equiv

variable {m : ℕ}

def p_fun (m : ℕ) (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if h : i.val < m then
    ⟨2 * (m - 1 - i.val) + 1, by omega⟩
  else
    ⟨2 * (i.val - m), by omega⟩

lemma p_fun_inj (m : ℕ) : Function.Injective (p_fun m) := by
  intro a b hab
  dsimp [p_fun] at hab
  split_ifs at hab with h1 h2 h3 h4
  · simp only [Fin.mk.injEq] at hab
    have : a.val = b.val := by omega
    exact Fin.eq_of_val_eq this
  · simp only [Fin.mk.injEq] at hab
    -- One is odd, one is even, impossible!
    have h_odd : (2 * (m - 1 - a.val) + 1) % 2 = 1 := by omega
    have h_even : (2 * (b.val - m)) % 2 = 0 := by omega
    rw [hab] at h_odd
    omega
  · simp only [Fin.mk.injEq] at hab
    have h_even : (2 * (a.val - m)) % 2 = 0 := by omega
    have h_odd : (2 * (m - 1 - b.val) + 1) % 2 = 1 := by omega
    rw [hab] at h_even
    omega
  · simp only [Fin.mk.injEq] at hab
    have : a.val = b.val := by omega
    exact Fin.eq_of_val_eq this

def p_equiv (m : ℕ) : Equiv.Perm (Fin (2 * m + 1)) :=
  Equiv.ofBijective (p_fun m) (Fintype.injective_iff_bijective.mp (p_fun_inj m))

lemma p_equiv_apply_s (m : ℕ) (i : Fin (2 * m + 1)) :
    let s : Fin (2 * m + 1) → ℕ := fun j => if j.val < 2 * m then m + j.val / 2 + 1 else 2 * m + 1
    s (p_equiv m i) = max (i.val + 1) (2 * m - i.val) := by
  intro s
  dsimp [s, p_equiv, p_fun]
  split_ifs with h1 h2
  · -- i < m
    have h_lt : 2 * (m - 1 - i.val) + 1 < 2 * m := by omega
    rw [if_pos h_lt]
    have : (2 * (m - 1 - i.val) + 1) / 2 = m - 1 - i.val := by omega
    rw [this]
    have : m + (m - 1 - i.val) + 1 = 2 * m - i.val := by omega
    rw [this]
    exact (max_eq_right (by omega)).symm
  · -- i >= m
    have h_lt2 : 2 * (i.val - m) < 2 * m ↔ i.val < 2 * m := by omega
    by_cases h_i : i.val < 2 * m
    · rw [if_pos (by omega)]
      have : 2 * (i.val - m) / 2 = i.val - m := by omega
      rw [this]
      have : m + (i.val - m) + 1 = i.val + 1 := by omega
      rw [this]
      exact (max_eq_left (by omega)).symm
    · have : i.val = 2 * m := by omega
      rw [if_neg (by omega)]
      have : 2 * m + 1 = i.val + 1 := by omega
      rw [this]
      exact (max_eq_left (by omega)).symm
