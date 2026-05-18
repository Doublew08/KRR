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
def IsGraceful {V : Type*} [Fintype V] [DecidableEq V]
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
    IsGraceful (treeGraphOfFunction f) := by
  let G := treeGraphOfFunction f
  let hn' : 0 < n := by omega
  -- edgeLabelSet f = Finset.range n (n distinct values all < n)
  have hlabels : edgeLabelSet f = Finset.range n := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      simp only [edgeLabelSet, Finset.mem_image, Finset.mem_univ, true_and] at hk
      obtain ⟨i, rfl⟩ := hk
      simp only [Finset.mem_range]
      have h1 := i.isLt; have h2 := (f i).isLt
      rcases Nat.lt_or_ge (f i).val i.val with h | h
      · rw [show (↑(f i).val - ↑i.val : ℤ) = -↑(i.val - (f i).val) by push_cast; omega]
        simp [Int.natAbs_neg, Int.natAbs_natCast]; omega
      · rw [show (↑(f i).val - ↑i.val : ℤ) = ↑((f i).val - i.val) by push_cast; omega]
        simp [Int.natAbs_natCast]; omega
    · rw [Finset.card_range]; exact le_of_eq hf_grace.symm
  -- The source set: {i : Fin n | 0 < i.val}
  let src := Finset.univ.filter (fun i : Fin n => 0 < i.val)
  -- Each i > 0 gives an edge s(i, f i)
  have hmem : ∀ i ∈ src, s(i, f i) ∈ G.edgeFinset := by
    intro i hi
    simp only [src, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    refine ⟨?_, Or.inl rfl⟩
    intro h
    have := hf_canon.2 i hi
    have := congr_arg Fin.val h
    omega
  -- The map i ↦ s(i, f i) is injective on src
  have hinj : Set.InjOn (fun i => s(i, f i)) ↑src := by
    intro i hi j hj h
    simp only [src, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, _⟩ | ⟨hij, hfij⟩
    · rfl
    · have h1 : (f j).val < j.val := hf_canon.2 j hj
      have h2 : (f i).val < i.val := hf_canon.2 i hi
      have h3 : i.val = (f j).val := congr_arg Fin.val hij
      have h4 : (f i).val = j.val := congr_arg Fin.val hfij
      omega
  -- G.edgeFinset = image of src under i ↦ s(i, f i)
  have hG_img : G.edgeFinset = src.image (fun i => s(i, f i)) := by
    ext e
    simp only [Finset.mem_image, src, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro he
      induction e using Sym2.inductionOn with
      | hf u v =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
        obtain ⟨hne, hf_or⟩ := he
        rcases hf_or with hfu | hfv
        · have hu : 0 < u.val := by
            rcases Nat.eq_zero_or_pos u.val with h | h
            · have hu0 : u = ⟨0, hn'⟩ := Fin.ext h
              rw [hu0, hf_canon.1] at hfu; exact absurd (hu0.trans hfu) hne
            · exact h
          exact ⟨u, hu, by rw [hfu]⟩
        · have hv : 0 < v.val := by
            rcases Nat.eq_zero_or_pos v.val with h | h
            · have hv0 : v = ⟨0, hn'⟩ := Fin.ext h
              rw [hv0, hf_canon.1] at hfv; exact absurd (hv0.trans hfv) hne.symm
            · exact h
          exact ⟨v, hv, by rw [hfv, Sym2.eq_swap]⟩
    · rintro ⟨i, hi, rfl⟩
      exact hmem i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  -- Edge count: |G.edgeFinset| = n - 1
  have hm : G.edgeFinset.card = n - 1 := by
    rw [hG_img, Finset.card_image_of_injOn hinj]
    have hsrc : src = Finset.univ.erase ⟨0, hn'⟩ := by
      ext i
      simp only [src, Finset.mem_filter, Finset.mem_univ, true_and,
                 Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
      constructor
      · intro h heq
        have := congr_arg Fin.val heq
        simp at this; omega
      · intro h
        rcases Nat.eq_zero_or_pos i.val with h0 | h0
        · exfalso; apply h; exact Fin.ext h0
        · exact h0
    rw [hsrc, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  -- Identity labeling is graceful
  refine ⟨fun v => v.val, Fin.val_injective, ?_, ?_⟩
  · intro v; rw [hm]; exact Nat.le_sub_one_of_lt v.isLt
  · rw [hm]
    have hedge_labels : G.edgeFinset.image (fun e =>
        e.lift ⟨fun u v => Int.natAbs ((u.val : ℤ) - v.val),
                fun u v => natAbs_sub_comm u.val v.val⟩) =
        edgeLabelSet f \ {0} := by
      rw [hG_img, Finset.image_image]
      ext k
      simp only [Finset.mem_image, src, Finset.mem_filter, Finset.mem_univ, true_and,
                 Function.comp, Sym2.lift_mk, edgeLabelSet,
                 Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine ⟨⟨i, ?_⟩, ?_⟩
        · exact (natAbs_sub_comm i.val (f i).val).symm
        · intro h
          simp only [Int.natAbs_eq_zero, sub_eq_zero] at h
          have := hf_canon.2 i hi; push_cast at h; omega
      · rintro ⟨⟨j, hj⟩, hne⟩
        rcases Nat.eq_zero_or_pos j.val with h | h
        · exfalso; apply hne
          have hj0 : j = ⟨0, hn'⟩ := Fin.ext h
          rw [hj0, hf_canon.1] at hj; simp at hj; exact hj.symm
        · exact ⟨j, h, (natAbs_sub_comm j.val (f j).val).trans hj⟩
    rw [hedge_labels, hlabels]
    ext k
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, Finset.mem_Icc]
    omega

/--
Theorem 3.1 (Iterative Descent):
For any tree function f with diameter ≥ 3, if f² is graceful, then f is graceful.
-/
axiom theorem_3_1 (hn : 1 < n) (f : Fin n → Fin n) (h_tree : IsTreeFunction f)
    (h_diam : funcDiameter f ≥ 3) :
    IsGracefulFunction (f ∘ f) → IsGracefulFunction f


/--
This will be proved by the chain:
  Phase 3 (Functional Reformulation) → Phase 4 (Graceful Expansion) →
  Phase 5 (Polynomial Machinery) → Phase 6 (Composition Lemma) →
  Phase 7 (Main Theorem via iterated composition to constant function). -/
lemma KRR_Conjecture_functional_star (hn : 0 < n) (f : Fin n → Fin n) 
    (h_tree : IsTreeFunction f) (h_star : ∀ i, i.val > 0 → f i = (⟨0, hn⟩ : Fin n)) : 
    IsGracefulFunction f := by
  use Equiv.refl (Fin n)
  simp [IsAlreadyGraceful, edgeLabelSet, conjugate]
  have hf0 : f ⟨0, hn⟩ = ⟨0, hn⟩ := by
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
        · right; rw [h0]
        · left; rw [hv]; exact hf_v
    have h2 : f^[2] ⟨0, hn⟩ = ⟨0, hn⟩ := by
      rw [show f^[2] ⟨0, hn⟩ = f (f ⟨0, hn⟩) from rfl, hf0_v, hf_v]
    have h2v : f^[2] v = v := by
      rw [show f^[2] v = f (f v) from rfl, hf_v, hf0_v]
    have h_cycle_prop : ∀ k, f^[2 * k] ⟨0, hn⟩ = ⟨0, hn⟩ ∧ f^[2 * k + 1] ⟨0, hn⟩ = v := by
      intro k; induction k with
      | zero => simp [hf0_v]
      | succ k ih =>
        have heven : f^[2 * (k + 1)] ⟨0, hn⟩ = ⟨0, hn⟩ := by
          rw [Nat.mul_succ, Function.iterate_add_apply, h2, ih.1]
        refine ⟨heven, ?_⟩
        rw [show 2 * (k + 1) + 1 = 1 + 2 * (k + 1) from by omega,
            Function.iterate_add_apply, Function.iterate_one, heven, hf0_v]
    have h_img : {⟨0, hn⟩, v} ⊆ iterateImage f (n - 1) := by
      have hv_cycle : ∀ m, f^[2 * m] v = v := fun m => by
        induction m with
        | zero => simp
        | succ m ihm => rw [Nat.mul_succ, Function.iterate_add_apply, h2v, ihm]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      unfold iterateImage; simp only [Finset.mem_image, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl
      · rcases Nat.even_or_odd (n - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact ⟨⟨0, hn⟩, by rw [hk, show k + k = 2 * k from by omega]; exact (h_cycle_prop k).1⟩
        · exact ⟨v, by rw [hk, Function.iterate_add_apply]; simp [Function.iterate_one, hf_v, (h_cycle_prop k).1]⟩
      · rcases Nat.even_or_odd (n - 1) with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact ⟨v, by rw [hk, show k + k = 2 * k from by omega]; exact hv_cycle k⟩
        · exact ⟨⟨0, hn⟩, by rw [hk]; exact (h_cycle_prop k).2⟩
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
    simp only [Finset.mem_image, Finset.mem_univ, Finset.mem_range, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      have h1 := i.isLt
      have h2 := (f i).isLt
      omega
    · intro hk; rcases Nat.eq_zero_or_pos k with rfl | hp
      · exact ⟨⟨0, hn⟩, by rw [hf0]; simp⟩
      · refine ⟨⟨k, by omega⟩, ?_⟩
        have hfk : f ⟨k, by omega⟩ = ⟨0, hn⟩ := h_star ⟨k, by omega⟩ (by omega)
        rw [hfk]; simp
  rw [this]
  exact Finset.card_range n

axiom KRR_Conjecture_functional (hn : 0 < n) (f : Fin n → Fin n) :
    IsTreeFunction f → IsGracefulFunction f






end KRR
