import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import KRR.Basic

/-!
# KRR Phase 2: Graceful Labeling

This module defines graceful labelings in two equivalent ways:
1. **Functional form** (primary): A relabeling `σ` of `f : Fin n → Fin n` is graceful
   if the induced absolute-difference edge labels are all distinct and cover `{0,...,n-1}`.
2. **SimpleGraph form** (final theorem statement): For bridging to Mathlib's `IsTree`.

The functional form is used throughout the proof. The SimpleGraph form is only
used in the final KRR theorem statement.

## Main definitions

* `KRR.IsGracefulRelabeling` — σfσ⁻¹ has n distinct edge labels
* `KRR.IsGracefulFunction` — some relabeling of f is graceful
* `KRR.starIsGraceful` — constant functions (stars) are graceful

## References

* [Gnang, *A proof of the Kotzig–Ringel–Rosa Conjecture*][arXiv:2202.03178]
-/

namespace KRR

variable {n : ℕ}

/-- The set of induced absolute subtractive edge labels for `f : Fin n → Fin n`.
This is `{|f(i) - i| : i ∈ ℤₙ}`, the set of absolute differences between
each vertex and its parent. -/
def edgeLabelSet (f : Fin n → Fin n) : Finset ℕ :=
  Finset.univ.image (fun i : Fin n => Int.natAbs ((f i).val - i.val))

/-- A function `f : Fin n → Fin n` is "already gracefully labeled" if the induced
absolute subtractive edge labels are all distinct, i.e. `|edgeLabelSet f| = n`. -/
def IsAlreadyGraceful (f : Fin n → Fin n) : Prop :=
  (edgeLabelSet f).card = n

/-- A relabeling `σ` of `f` produces `σ ∘ f ∘ σ⁻¹`, which is a conjugation by
a permutation. The functional digraph of `σfσ⁻¹` is isomorphic to that of `f`
but with relabeled vertices. -/
def conjugate (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n)) : Fin n → Fin n :=
  σ ∘ f ∘ σ.symm

/-- A function `f` is graceful if there exists a permutation `σ` such that
`σfσ⁻¹` has `n` distinct induced absolute subtractive edge labels.
This matches the paper's definition. -/
def IsGracefulFunction (f : Fin n → Fin n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), IsAlreadyGraceful (conjugate f σ)

/-- The complement map `φ(i) = (n-1) - i`. This captures the complementary
labeling symmetry from eq. (2.5) of the paper. -/
def complementMap (_hn : 0 < n) : Equiv.Perm (Fin n) where
  toFun i := ⟨n - 1 - i.val, by omega⟩
  invFun i := ⟨n - 1 - i.val, by omega⟩
  left_inv i := by ext; simp; omega
  right_inv i := by ext; simp; omega

/-! ### Star graphs (constant functions) are graceful

This is Example 3.1 from the paper. A "functional star" is the graph of
a constant function `f(i) = c` for all `i`. When `c = 0`, the function
is already gracefully labeled because the edge labels are `{0, 1, ..., n-1}`.
-/

/-- The constant-zero function on `Fin n`. -/
def constZero (hn : 0 < n) : Fin n → Fin n := fun _ => ⟨0, hn⟩

/-- The edge labels of the constant-zero function are `{0, 1, ..., n-1}`.
Specifically, `|f(i) - i| = |0 - i| = i` for each `i ∈ Fin n`. -/
theorem constZero_edgeLabelSet (hn : 0 < n) :
    edgeLabelSet (constZero hn) = Finset.univ.image (fun i : Fin n => i.val) := by
  simp [edgeLabelSet, constZero]

/-- Constant-zero function is already gracefully labeled. -/
theorem constZero_isAlreadyGraceful (hn : 0 < n) :
    IsAlreadyGraceful (constZero hn) := by
  simp only [IsAlreadyGraceful, edgeLabelSet, constZero]
  rw [Finset.card_image_of_injective]
  · exact Finset.card_fin n
  · intro a b hab
    simp only [Int.natAbs_neg, Int.natAbs_natCast] at hab
    exact Fin.ext (by omega)

/-- Any constant function is graceful (possibly after conjugation). -/
theorem const_isGraceful (hn : 0 < n) (c : Fin n) :
    IsGracefulFunction (fun _ => c) := by
  use Equiv.swap c ⟨0, hn⟩
  have hconj : conjugate (fun _ => c) (Equiv.swap c ⟨0, hn⟩) = constZero hn := by
    ext i
    simp [conjugate, constZero, Equiv.swap_apply_left]
  rw [hconj]
  exact constZero_isAlreadyGraceful hn

lemma natAbs_sub_comm (a b : ℕ) : 
    Int.natAbs ((a : ℤ) - b) = Int.natAbs ((b : ℤ) - a) := by
  rw [← Int.natAbs_neg, neg_sub]

/-- Graceful labeling of a `SimpleGraph`: an injective vertex labeling
`f : V → {0,...,m}` where `m = |E(G)|` such that the induced edge labels
`{|f(u) - f(v)| : {u,v} ∈ E(G)}` are distinct and cover `{1,...,m}`.
This is the classical statement used in the final KRR theorem. -/
def IsGraceful' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [inst : DecidableRel G.Adj] : Prop :=
  let m := G.edgeFinset.card
  ∃ f : V → ℕ,
    Function.Injective f ∧
    (∀ v, f v ≤ m) ∧
    G.edgeFinset.image (fun e =>
      e.lift ⟨fun u v => Int.natAbs ((f u : ℤ) - f v),
              fun u v => natAbs_sub_comm (f u) (f v)⟩) = Finset.Icc 1 m

instance (f : Fin n → Fin n) : DecidableRel (treeGraphOfFunction f).Adj :=
  fun u v => by unfold treeGraphOfFunction; infer_instance

/-- **Bridge Theorem**: A canonical tree function that is functionally graceful
induces a classically graceful labeling on its undirected graph. -/
theorem isGraceful_bridge (hn : 1 < n) (f : Fin n → Fin n)
    (hf_canon : IsCanonicalTreeFunction (by omega) f)
    (hf_grace : IsAlreadyGraceful f) :
    IsGraceful' (treeGraphOfFunction f) := by
  let G := treeGraphOfFunction f
  let m := n - 1
  -- 1. Prove edge count is n - 1
  have h_edge_card : G.edgeFinset.card = m := by
    let S := (Finset.univ.filter (fun i => i.val > 0)).image (fun i => Quot.mk (Sym2.Rel (Fin n)) (i, f i))
    have hS : G.edgeFinset = S := by
      ext e
      simp only [SimpleGraph.mem_edgeFinset, treeGraphOfFunction, Finset.mem_image, Finset.mem_univ, Finset.mem_filter, true_and]
      constructor
      · rintro ⟨u, v, hne, hf, rfl⟩
        rcases hf with h | h
        · use u; refine ⟨?_, ?_⟩
          · rcases Nat.eq_zero_or_pos u.val with hz | hp; swap; exact hp
            have : u = 0 := Fin.ext hz; rw [this, hf_canon.1] at h; exact (hne h.symm).elim
          · rw [h, Sym2.eq_swap]; rfl
        · use v; refine ⟨?_, ?_⟩
          · rcases Nat.eq_zero_or_pos v.val with hz | hp; swap; exact hp
            have : v = 0 := Fin.ext hz; rw [this, hf_canon.1] at h; exact (hne h.symm).elim
          · rw [h]; rfl
      · rintro ⟨i, hi, rfl⟩
        refine ⟨i, f i, ?_, Or.inl rfl, rfl⟩
        · intro heq; have hlt := hf_canon.2 i hi; rw [heq] at hlt; omega
    rw [hS, Finset.card_image_of_injective]
    · simp only [Finset.card_filter, Finset.card_univ]; omega
    · intro i j hi hj heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, _⟩ | ⟨h1, h2⟩
      · rfl
      · have hlti := hf_canon.2 i hi
        have hltj := hf_canon.2 j hj
        rw [h1] at hltj; rw [h2] at hlti; omega
  -- 2. Provide the labeling: id
  refine ⟨fun v => v.val, Fin.val_injective, ?_, ?_⟩
  · intro v; rw [h_edge_card]; exact v.isLt.le_sub_one
  -- 3. Show edge labels cover {1, ..., n-1}
  rw [h_edge_card]
  ext k
  simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset, treeGraphOfFunction, Finset.mem_Icc]
  constructor
  · rintro ⟨e, he, rfl⟩
    rw [Sym2.lift_mk]
    obtain ⟨u, v, hne, hf, rfl⟩ := he
    rcases hf with rfl | rfl
    · have hpos : u.val > 0 := by
        rcases Nat.eq_zero_or_pos u.val with hz | hp; swap; exact hp
        have : u = 0 := Fin.ext hz; rw [this, hf_canon.1] at hne; exact (hne rfl).elim
      have hlt := hf_canon.2 u hpos; omega
    · have hpos : v.val > 0 := by
        rcases Nat.eq_zero_or_pos v.val with hz | hp; swap; exact hp
        have : v = 0 := Fin.ext hz; rw [this, hf_canon.1] at hne; exact (hne rfl).elim
      have hlt := hf_canon.2 v hpos; omega
  · intro hk
    have : k ∈ (Finset.univ.image (fun i : Fin n => (↑(f i).val - ↑i.val : ℤ).natAbs)) := by
      let img := (Finset.univ.image (fun i : Fin n => (↑(f i).val - ↑i.val : ℤ).natAbs))
      have hsub : img ⊆ Finset.range n := by
        intro x hx; simp only [img, Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx; simp only [Finset.mem_range]
        have h1 := (f i).isLt
        have h2 := i.isLt
        omega
      have heq : img = Finset.range n := by
        apply Finset.eq_of_subset_of_card_le hsub
        rw [hf_grace, Finset.card_range]
      change k ∈ img; rw [heq]; simp only [Finset.mem_range]; omega
    obtain ⟨i, hi_k⟩ : ∃ i, (↑(f i).val - ↑i.val : ℤ).natAbs = k := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at this; exact this
    have hi : i.val > 0 := by
      rcases Nat.eq_zero_or_pos i.val with hz | hp; swap; exact hp
      exfalso; have : i = ⟨0, by omega⟩ := Fin.ext hz
      rw [this, hf_canon.1] at hi_k; simp only [Nat.cast_zero, sub_self, Int.natAbs_zero] at hi_k
      rw [← hi_k] at hk; omega
    refine ⟨Quot.mk _ (i, f i), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset]
      exact ⟨by intro heq; have hlt := hf_canon.2 i hi; rw [heq] at hlt; omega, Or.inl rfl⟩
    · rw [Sym2.lift_mk, ← Int.natAbs_neg (↑i.val - ↑(f i).val), neg_sub]
      exact hi_k

/--
Theorem 3.1 (Iterative Descent):
For any tree function f with diameter ≥ 3, if f² is graceful, then f is graceful.
-/
theorem theorem_3_1 (hn : 1 < n) (f : Fin n → Fin n) (h_tree : IsTreeFunction f)
    (h_diam : funcDiameter f ≥ 3) :
    IsGracefulFunction (f ∘ f) → IsGracefulFunction f := by
  -- Uses Phase 4 (Expansion) and Phase 6 (Composition Lemma)
  sorry

/--
This will be proved by the chain:
  Phase 3 (Functional Reformulation) → Phase 4 (Graceful Expansion) →
  Phase 5 (Polynomial Machinery) → Phase 6 (Composition Lemma) →
  Phase 7 (Main Theorem via iterated composition to constant function). -/
theorem KRR_Conjecture_functional (hn : 0 < n) (f : Fin n → Fin n) :
    IsTreeFunction f → IsGracefulFunction f := by
  intro h_tree
  -- Case: star tree
  by_cases h_star : ∀ i, i.val > 0 → f i = (⟨0, hn⟩ : Fin n)
  · use Equiv.refl (Fin n)
    simp [IsAlreadyGraceful, edgeLabelSet, conjugate]
    have hf0 : f ⟨0, hn⟩ = ⟨0, hn⟩ := by
      -- Since all i > 0 map to 0, if f 0 ≠ 0 then we have a cycle (0, f 0).
      -- In a tree function, iterateImage f (n-1) must be {fixed_point}.
      by_contra h_ne
      let v := f ⟨0, hn⟩
      have hf0_v : f ⟨0, hn⟩ = v := rfl
      have hv : v.val > 0 := by
        rcases Nat.eq_zero_or_pos v.val with hz | hp
        · exfalso; exact h_ne (Fin.ext hz)
        · exact hp
      have hf_v : f v = ⟨0, hn⟩ := h_star v hv
      have h_cycle : ∀ k, f^[k] ⟨0, hn⟩ ∈ ({⟨0, hn⟩, v} : Finset (Fin n)) := by
        intro k; induction k with
        | zero => simp
        | succ k ih => 
          rw [Function.iterate_succ_apply']
          simp at ih ⊢; rcases ih with h0 | hv
          · right; rw [h0]; rfl
          · left; rw [hv]; exact hf_v
      have h2 : f^[2] ⟨0, hn⟩ = ⟨0, hn⟩ := by
        rw [Function.iterate_two, hf0_v, hf_v]
      have h2v : f^[2] v = v := by
        rw [Function.iterate_two, hf_v, hf0_v]
      have h_cycle_prop : ∀ k, f^[2 * k] ⟨0, hn⟩ = ⟨0, hn⟩ ∧ f^[2 * k + 1] ⟨0, hn⟩ = v := by
        intro k; induction k with
        | zero => simp [hf0_v]
        | succ k ih =>
          constructor
          · rw [Nat.mul_succ, Function.iterate_add_apply, ih.1, h2]
          · rw [Nat.mul_succ, Function.iterate_add_apply, ih.2, h2v]
      have h_img : {⟨0, hn⟩, v} ⊆ iterateImage f (n - 1) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        unfold iterateImage; simp only [Finset.mem_image, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · -- Show 0 is in the image.
          rcases Nat.even_or_odd (n - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
          · use ⟨0, hn⟩; rw [hk]; induction k with | zero => simp | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, ih, h2]
          · use v; rw [hk, Nat.add_comm, Function.iterate_add_apply]; induction k with | zero => simp [hf_v] | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, ih, h2]
        · -- Show v is in the image.
          rcases Nat.even_or_odd (n - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
          · use v; rw [hk]; induction k with | zero => simp | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, ih, h2v]
          · use ⟨0, hn⟩; rw [hk]; induction k with | zero => simp [hf0_v] | succ k ih => rw [Nat.mul_succ, Function.iterate_add_apply, ih, h2]
      have : (iterateImage f (n-1)).card = 1 := h_tree
      have h_card2 : ({⟨0, hn⟩, v} : Finset (Fin n)).card = 2 := by
        apply Finset.card_pair
        intro h; exact h_ne (by rwa [← h] at hf0_v)
      have := Finset.card_le_card h_img
      rw [h_card2, h_tree] at this; omega

    have h0 : (fun i : Fin n => Int.natAbs (↑(f i).val - ↑i.val)) ⟨0, hn⟩ = 0 := by
      show Int.natAbs (↑(f ⟨0, hn⟩).val - ↑(0 : ℕ)) = 0
      rw [hf0]; simp
    have : (Finset.univ.image (fun i : Fin n => Int.natAbs (↑(f i).val - ↑i.val))) = 
           (Finset.range n) := by
      ext k
      simp
      constructor
      · rintro ⟨i, rfl⟩; exact i.isLt
      · intro hk; rcases Nat.eq_zero_or_pos k with rfl | hp
        · use ⟨0, hn⟩; exact h0
        · obtain ⟨i, hi, h_abs⟩ : ∃ (i : Fin n), i.val > 0 ∧ (Int.natAbs (↑(f i).val - ↑i.val)) = k := by
            let idx : Fin n := ⟨k, by omega⟩
            use idx; constructor; · omega
            have hf_idx : f idx = ⟨0, hn⟩ := h_star idx (by omega)
            rw [hf_idx]; simp [idx]; omega
          use i; exact h_abs
    rw [this]
    simp only [Equiv.refl_symm, Equiv.refl_apply, Function.comp_id, id_comp, Finset.card_range]



  · -- General case using Phase 3-6
    -- Every tree function can be transformed into a star tree.
    -- The Composition Lemma (Phase 6) ensures gracefulness is preserved.
    -- The Polynomial Indicator (Phase 5) ensures existence.
    sorry

end KRR
