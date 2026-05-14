import KRR.Basic
import KRR.Graceful
import KRR.Combinatorics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Int.Basic

/-!
# KRR Phase 3: Functional Reformulation

This module reformulates the graceful labeling problem in terms of
endofunctions on `Fin n`, following Section 2.1–2.2 of the paper.

## Main definitions

* `KRR.IsValidPermutationBasis` — permutation basis condition (eq. 2.6)
* `KRR.SignFunction` — the sign function 𝔰_f(γ, i) ∈ {-1, 0, 1}

## References

* [Gnang, *A proof of the Kotzig–Ringel–Rosa Conjecture*][arXiv:2202.03178]
-/

namespace KRR

variable {n : ℕ}

/-- A permutation `γ` fixing 0 is a valid permutation basis for graceful expansion
if for all `i ∈ {1, ..., n-1}`, either `γ(i) ≤ i` or `γ(i) ≤ (n-1) - i`.
This is equation (2.6) from the paper. -/
def IsValidPermutationBasis (hn : 0 < n) (γ : Equiv.Perm (Fin n)) : Prop :=
  γ ⟨0, hn⟩ = ⟨0, hn⟩ ∧
  ∀ i : Fin n, i.val > 0 →
    (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val

/-- The sign function `𝔰_f(γ, i)` from the Graceful Expansion Theorem.
For each vertex `i` and permutation basis `γ`:
  - returns `0` if `f(i) = i` (loop edge)
  - returns `1` if the edge label was obtained via subtraction
  - returns `-1` if the edge label was obtained via addition -/
def signFunction (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n))
    (_ : Equiv.Perm (Fin n)) (i : Fin n) : Int :=
  let fi := conjugate f σ
  if fi i = i then 0
  else if (fi i).val < i.val then -1
  else 1

/-- **Theorem (Section 2.2):** The number of valid permutation bases fixing 0 is exactly
`⌊(n-1)/2⌋! · ⌈(n-1)/2⌉!`.

Proof sketch: The condition partitions indices `{1, ..., n-1}` into two groups
(those where `γ(i) ≤ i` is forced, and those where `γ(i) ≤ (n-1) - i` is forced),
whose sizes are `⌊(n-1)/2⌋` and `⌈(n-1)/2⌉`. Within each group, `γ` can be any
bijection.
-/
theorem count_valid_bases_eq (hn : 0 < n) (h2 : 2 < n) :
    (Finset.univ.filter (fun γ : Equiv.Perm (Fin n) =>
      γ ⟨0, hn⟩ = ⟨0, hn⟩ ∧
      ∀ i : Fin n, i.val > 0 →
        (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val)).card =
    Nat.factorial ((n - 1) / 2) * Nat.factorial (((n - 1) + 1) / 2) := by
  let k := n - 1
  let S := (Finset.univ.filter (fun γ : Equiv.Perm (Fin n) =>
      γ ⟨0, hn⟩ = ⟨0, hn⟩ ∧
      ∀ i : Fin n, i.val > 0 →
        (γ i).val ≤ i.val ∨ (γ i).val ≤ (n - 1) - i.val))
  let T := (Finset.univ.filter (fun γ : Equiv.Perm (Fin k) =>
      ∀ i : Fin k, (γ i).val + 1 ≤ max (i.val + 1) (k - (i.val + 1))))
  
  have h_iso : S.card = T.card := by
    let e_opt : Fin n ≃ Option (Fin k) := finSuccEquiv 0
    let f_iso := Equiv.Perm.congr e_opt
    let Φ (γ : Equiv.Perm (Fin n)) (h : γ ⟨0, hn⟩ = ⟨0, hn⟩) : Equiv.Perm (Fin k) :=
      Equiv.removeNone (f_iso γ)
    
    -- Show that Φ is a bijection between S and T
    apply Finset.card_congr (fun γ hγ => Φ γ (Finset.mem_filter.1 hγ).2.1)
    · intro γ hγ
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
      intro j
      let i := e_opt.symm (some j)
      have hi_pos : i.val > 0 := by
        have : i ≠ 0 := by
          intro h; have := e_opt.injective (h.symm ▸ rfl : e_opt i = e_opt 0)
          simp [e_opt, finSuccEquiv] at this
        rcases Nat.eq_zero_or_pos i.val with hz | hp; swap; exact hp
        exact (this (Fin.ext hz)).elim
      have hcond := hγ.2.2 i hi_pos
      have h_phi : (Φ γ hγ.2.1 j).val + 1 = (γ i).val := by
        unfold Φ f_iso i
        let σ := Equiv.Perm.congr e_opt γ
        have hσ0 : σ none = none := by 
          simp [σ, e_opt, finSuccEquiv, hγ.2.1]
        let v := γ i
        have hv0 : v ≠ 0 := by
          intro hv; have := γ.injective (hv.symm ▸ hγ.2.1.symm : γ 0 = γ i)
          exact hi_pos.ne this.symm
        have h_σj : σ (some j) = some ⟨v.val - 1, by 
          have := v.isLt; omega⟩ := by
          simp [σ, e_opt, finSuccEquiv, hv0, i]
        have h_rem : σ (some j) = some (Equiv.removeNone σ j) := by
          rw [Equiv.removeNone_some σ j hσ0]
        rw [h_rem] at h_σj; simp at h_σj
        rw [h_σj]; omega
      rw [h_phi]
      apply hγ.2.2 i hi_pos
    · intro γ1 γ2 hγ1 hγ2 heq
      simp only [Φ] at heq
      let σ1 := Equiv.Perm.congr e_opt γ1
      let σ2 := Equiv.Perm.congr e_opt γ2
      have hσ1 : σ1 none = none := by simp [σ1, e_opt, finSuccEquiv, (Finset.mem_filter.1 hγ1).2.1]
      have hσ2 : σ2 none = none := by simp [σ2, e_opt, finSuccEquiv, (Finset.mem_filter.1 hγ2).2.1]
      have : σ1 = σ2 := by
        apply Equiv.Perm.decomposeOption.injective
        simp [Equiv.Perm.decomposeOption, hσ1, hσ2, heq]
      exact (Equiv.Perm.congr e_opt).injective this
    · intro φ hφ
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hφ
      let σ : Equiv.Perm (Option (Fin k)) := Equiv.Perm.decomposeOption.symm (none, φ)
      let γ := (Equiv.Perm.congr e_opt).symm σ
      use γ
      have hγ0 : γ ⟨0, hn⟩ = ⟨0, hn⟩ := by
        simp [γ, σ, e_opt, finSuccEquiv]
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hγ0, ?_⟩
      · intro i hi
        let j := (e_opt i).get (by simp [e_opt, finSuccEquiv, hi.ne'])
        have hi_j : some j = e_opt i := by simp [j]
        have : (γ i).val = (φ j).val + 1 := by
          simp [γ, σ, ← hi_j, e_opt, finSuccEquiv]
          have hσj : σ (e_opt i) = some (φ j) := by
            simp [σ, hi_j]
          have : (e_opt (γ i)).val = (φ j).val := by
            simp [γ, hσj]
          have h_γi : γ i ≠ 0 := by
            intro h; simp [h, e_opt, finSuccEquiv] at hσj
          have : (e_opt (γ i)).val = (γ i).val - 1 := by
            simp [e_opt, finSuccEquiv, h_γi]
          omega
        rw [this]
        have hφj := hφ j
        convert hφj using 1
        · simp [j, e_opt, finSuccEquiv]; omega
        · simp [j, e_opt, finSuccEquiv]; omega
  
  -- 2. Use the product of bounds formula for permutations with restricted ranges.
  rw [h_iso]
  obtain ⟨m, hm⟩ := Nat.even_or_odd k
  · rcases hm with rfl
    have h1 : (2 * m) / 2 = m := Nat.mul_div_right _ (by omega)
    have h2 : (2 * m + 1) / 2 = m := by rw [Nat.add_comm, Nat.add_div_right _ (by omega)]; simp
    rw [h1, h2]
    convert card_perm_max_bounds_even m
    · simp; omega
    · simp; rfl
  · rcases hm with rfl
    have h1 : (2 * m + 1) / 2 = m := by rw [Nat.add_comm, Nat.add_div_right _ (by omega)]; simp
    have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by 
      have : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
      rw [this, Nat.mul_div_right _ (by omega)]
    rw [h1, h2]
    convert card_perm_max_bounds_odd m
    · simp; omega
    · simp; rfl

end KRR

