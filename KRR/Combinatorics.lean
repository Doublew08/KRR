import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card

open BigOperators

namespace KRR

/-- 
The number of permutations σ of {1, ..., k} such that σ(i) ≤ max(i, k-i).
Even case: k = 2m.
-/
theorem card_perm_max_bounds_even (m : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m)) =>
      ∀ i : Fin (2 * m), (σ i).val + 1 ≤ max (i.val + 1) (2 * m - 1 - i.val))).card = 
    (Nat.factorial m) ^ 2 := by
  let a (i : Fin (2 * m)) : ℕ := max (i.val + 1) (2 * m - 1 - i.val)
  -- The product formula requires monotonicity. We reorder the domain.
  -- But wait, the product formula lemma we have assumes monotonicity.
  -- Every permutation of bounds gives the same count if the bounds are a permutation of each other.
  -- For now, we skip the reordering proof and focus on the result.
  sorry

theorem card_perm_max_bounds_odd (m : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * m + 1)) =>
      ∀ i : Fin (2 * m + 1), (σ i).val + 1 ≤ max (i.val + 1) (2 * m - i.val))).card = 
    Nat.factorial m * Nat.factorial (m + 1) := by
  sorry


/-- 
Helper: Counting injections Fin k ↪ Fin n with monotone upper bounds.
-/
theorem count_injections_le_product {k n : ℕ} (a : Fin k → ℕ) (ha : Monotone a) (han : ∀ j, a j < n) :
    (Finset.univ.filter (fun f : Fin k ↪ Fin n => ∀ j, (f j).val ≤ a j)).card = 
    ∏ j : Fin k, (a j - j.val + 1) := by
  induction k generalizing n a with
  | zero => 
    simp; rfl
  | succ k ih =>
    -- Induction step for k+1
    let S_k1 := (Finset.univ.filter (fun f : Fin (k + 1) ↪ Fin n => ∀ j, (f j).val ≤ a j))
    let S_k := (Finset.univ.filter (fun f : Fin k ↪ Fin n => ∀ j, (f j).val ≤ a (Fin.castSucc j)))
    have h_card : S_k1.card = ∑ f' in S_k, (Finset.univ.filter (fun (x : Fin n) => x.val ≤ a (Fin.last k) ∧ x ∉ (Finset.univ : Finset (Fin k)).image (fun j => f' j))).card := by
      rw [← Finset.card_sigma]
      let Φ : (f : Fin (k + 1) ↪ Fin n) → Σ f' : Fin k ↪ Fin n, Fin n := fun f => 
        ⟨Function.Embedding.restr (fun j => Fin.castSucc j) f, f (Fin.last k)⟩
      apply Finset.card_congr (fun f hf => ⟨Φ f, ⟨(Φ f).2, by
        simp at hf ⊢
        obtain ⟨h_bounds, h_inj⟩ := ⟨hf, f.injective⟩
        constructor
        · exact h_bounds (Fin.last k)
        · intro j; exact f.injective.ne (Fin.castSucc_ne_last j).symm⟩⟩)
      · intro f hf; simp at hf ⊢; intro j; exact hf (Fin.castSucc j)
      · intro f1 f2 hf1 hf2 heq
        simp [Φ] at heq; obtain ⟨h_restr, h_last⟩ := heq
        apply Function.Embedding.ext; intro j
        rcases Fin.exists_castSucc_or_last j with ⟨j', rfl⟩ | rfl
        · exact Function.Embedding.congr_arg h_restr j'
        · exact h_last
      · rintro ⟨f', x, ⟨hx_bound, hx_range⟩⟩ hf'
        simp at hf'
        let f_fun : Fin (k + 1) → Fin n := fun j => 
          if h : j.val < k then f' ⟨j.val, h⟩ else x
        have hf_inj : Function.Injective f_fun := by
          intro j1 j2 heq
          unfold f_fun at heq
          split_ifs at heq with h1 h2
          · exact Fin.ext (Fin.ext_iff.mp (f'.injective heq))
          · simp at hx_range; exfalso; exact hx_range ⟨j1.val, h1⟩ (Fin.ext_iff.mpr heq)
          · simp at hx_range; exfalso; exact hx_range ⟨j2.val, h2⟩ (Fin.ext_iff.mpr heq.symm)
          · have hj1 : j1 = Fin.last k := by have := j1.isLt; omega
            have hj2 : j2 = Fin.last k := by have := j2.isLt; omega
            rw [hj1, hj2]
        let f : Fin (k + 1) ↪ Fin n := ⟨f_fun, hf_inj⟩
        use f
        simp at hf' ⊢
        constructor
        · intro j; rcases Fin.exists_castSucc_or_last j with ⟨j', rfl⟩ | rfl
          · simp [f_fun, j']; exact hf' j'
          · simp [f_fun]; exact hx_bound
        · constructor
          · apply Function.Embedding.ext; intro j; simp [f_fun, j]
          · simp [f_fun]
    rw [h_card]
    have h_const : ∀ f' ∈ S_k, (Finset.univ.filter (fun (x : Fin n) => x.val ≤ a (Fin.last k) ∧ x ∉ (Finset.univ : Finset (Fin k)).image (fun j => f' j))).card = (a (Fin.last k) - k + 1) := by
      intro f' hf'
      simp at hf'
      let S := Finset.univ.filter (fun (x : Fin n) => x.val ≤ a (Fin.last k))
      let T := (Finset.univ : Finset (Fin k)).image (fun j => f' j)
      have hT_sub : T ⊆ S := by
        intro y hy; simp at hy; obtain ⟨j, rfl⟩ := hy
        simp [S]; calc (f' j).val ≤ a (Fin.castSucc j) := hf' j
          _ ≤ a (Fin.last k) := ha (Fin.castSucc_le_last j)
      have hS_card : S.card = a (Fin.last k) + 1 := by
        rw [Finset.filter_card]
        simp only [Finset.card_range]
      have hT_card : T.card = k := by
        rw [Finset.card_image_of_injective]; simp; exact f'.injective
      have : (S \ T).card = S.card - T.card := Finset.card_sdiff hT_sub
      rw [this, hS_card, hT_card]
      have : S \ T = Finset.univ.filter (fun (x : Fin n) => x.val ≤ a (Fin.last k) ∧ x ∉ (Finset.univ : Finset (Fin k)).image (fun j => f' j)) := by
        ext x; simp [S, T]
      rw [← this]
      omega
    rw [Finset.sum_congr rfl h_const]
    rw [Finset.sum_const, ih (fun j => a (Fin.castSucc j)) (fun j1 j2 h => ha (by simp; exact h)) (fun j => han (Fin.castSucc j))]
    · rw [Fin.prod_univ_succ]
      simp [Fin.last, Fin.castSucc]
      rfl


/-- 
General product formula for counting permutations with upper bounds.
If a_j is a non-decreasing sequence of bounds, the number of permutations 
σ such that σ(j) ≤ a_j is ∏ (a_j - j + 1).
-/
theorem count_perm_le_product {k : ℕ} (a : Fin k → ℕ) (ha : Monotone a) (han : ∀ j, a j < k) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => ∀ j, (σ j).val ≤ a j)).card = 
    ∏ j : Fin k, (a j - j.val + 1) := by
  -- Now han is a hypothesis. In our determinantal applications,
  -- the bounds a(j) are always < n because they are labels in {0, ..., n-1}.
  -- We assume han for the mathematical correctness of the product formula.
  let e : Equiv.Perm (Fin k) ≃ (Fin k ↪ Fin k) := {
    toFun := fun σ => ⟨σ, σ.injective⟩
    invFun := fun f => Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by simp⟩)
    left_inv := fun σ => by ext; simp
    right_inv := fun f => by ext; simp
  }
  have : (Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => ∀ j, (σ j).val ≤ a j)).card = 
         (Finset.univ.filter (fun f : Fin k ↪ Fin k => ∀ j, (f j).val ≤ a j)).card := by
    apply Finset.card_bij (fun σ _ => e σ)
    · intro σ hσ; simp at hσ ⊢; exact hσ
    · intro σ1 σ2 hσ1 hσ2 heq; exact e.injective heq
    · intro f hf; simp at hf ⊢; use e.symm f; simp; exact hf
  rw [this]
  apply count_injections_le_product a ha han

/-- Permutations of α fixing a point are equivalent to permutations of the remaining elements. -/
def permFixEquiv {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    {σ : Equiv.Perm α // σ a = a} ≃ Equiv.Perm {x // x ≠ a} where
  toFun σ := Equiv.Perm.subtypePerm σ.1 (fun x => by
    rw [Equiv.Perm.apply_eq_iff_eq]; intro h; exact σ.2.symm ▸ h)
  invFun σ := ⟨Equiv.Perm.extendDomain σ (Equiv.refl {x // x = a}), by
    simp⟩
  left_inv σ := by
    ext x
    simp
    split_ifs with h
    · rcases h with ⟨y, hy, rfl⟩; rfl
    · rcases σ with ⟨σ, hσ⟩
      have : x = a := by
        by_contra hne
        exact h ⟨⟨x, hne⟩, rfl⟩
      rw [this]; simp; exact hσ
  right_inv σ := by
    ext ⟨x, hx⟩
    simp





end KRR
