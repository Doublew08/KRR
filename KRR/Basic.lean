import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Walks.Traversal
import Mathlib.Combinatorics.SimpleGraph.Walks.Operations
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Function.Iterate
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.style.longLine false

namespace KRR

variable {n : ℕ}

/-- The functional directed graph of `f : Fin n → Fin n`. -/
def FunctionalDigraph (f : Fin n → Fin n) : Digraph (Fin n) where
  Adj u v := v = f u

/-- The image of `f^(k)` applied to the full domain. -/
def iterateImage (f : Fin n → Fin n) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.image (f^[k])

/-- A function is a "tree function" if `|f^(n-1)(ℤₙ)| = 1`. -/
def IsTreeFunction (f : Fin n → Fin n) : Prop :=
  (iterateImage f (n - 1)).card = 1

/-- The set of fixed points of an endofunction `f`. -/
def fixedPointSet (f : Fin n → Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => f i = i)

/-- Two endofunctions differ by fixed point swaps. -/
def DifferByFixedPointSwaps (f g : Fin n → Fin n) : Prop :=
  (Finset.univ.filter (fun i => f i ≠ i)).image (fun i => ({i, f i} : Finset (Fin n))) =
  (Finset.univ.filter (fun i => g i ≠ i)).image (fun i => ({i, g i} : Finset (Fin n)))

/-- The number of distinct absolute subtractive edge labels for relabeling `σ`. -/
def distinctEdgeLabelsCount (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.image (fun i : Fin n =>
    Int.natAbs ((σ (f (σ.symm i))).val - i.val))).card

/-- `k` is the max distinct labels over all relabelings. -/
def IsMaxDistinctEdgeLabels (f : Fin n → Fin n) (k : ℕ) : Prop :=
  (∃ σ : Equiv.Perm (Fin n), distinctEdgeLabelsCount f σ = k) ∧
  (∀ σ : Equiv.Perm (Fin n), distinctEdgeLabelsCount f σ ≤ k)

/-- Canonical tree functions: f(0)=0 and f(i)<i for all i>0. -/
def IsCanonicalTreeFunction (hn : 0 < n) (f : Fin n → Fin n) : Prop :=
  f ⟨0, hn⟩ = ⟨0, hn⟩ ∧
  ∀ i : Fin n, i.val > 0 → (f i).val < i.val

/-- Diameter placeholder. -/
def funcDiameter (_f : Fin n → Fin n) : ℕ := 0

/-! ### Bridge to SimpleGraph -/

/-- Undirected SimpleGraph of a functional digraph:
u ~ v iff u≠v and (f(u)=v or f(v)=u). -/
def treeGraphOfFunction (f : Fin n → Fin n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (f u = v ∨ f v = u)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩
  loopless := { irrefl := fun _ ⟨hne, _⟩ => hne rfl }

/-! ### Canonical implies Tree -/

/-- Once we reach 0, we stay at 0. -/
private lemma iterate_zero_fixed (hn : 0 < n) (f : Fin n → Fin n)
    (h0 : f ⟨0, hn⟩ = ⟨0, hn⟩) (k : ℕ) : f^[k] ⟨0, hn⟩ = ⟨0, hn⟩ :=
  Function.IsFixedPt.iterate h0 k

/-- If f^[m](i)=0 then f^[k](i)=0 for k≥m. -/
private lemma iterate_stays_zero (hn : 0 < n) (f : Fin n → Fin n)
    (h0 : f ⟨0, hn⟩ = ⟨0, hn⟩) {i : Fin n} {m : ℕ}
    (hm : f^[m] i = ⟨0, hn⟩) {k : ℕ} (hk : m ≤ k) : f^[k] i = ⟨0, hn⟩ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm, Function.iterate_add_apply, hm, Function.IsFixedPt.iterate h0]

/-- For canonical f: iterating i.val times sends i to 0.
Proof by strong induction on i.val. -/
lemma IsCanonicalTreeFunction.reaches_zero (hn : 0 < n) (f : Fin n → Fin n)
    (hf : IsCanonicalTreeFunction hn f) : ∀ i : Fin n, f^[i.val] i = ⟨0, hn⟩ := by
  intro i
  suffices h : ∀ (k : ℕ) (i : Fin n), i.val ≤ k → f^[i.val] i = ⟨0, hn⟩ from h i.val i (le_refl _)
  intro k
  induction k with
  | zero =>
    intro i hi
    have hiz : i.val = 0 := Nat.eq_zero_of_le_zero hi
    have hieq : i = ⟨0, hn⟩ := Fin.ext hiz
    simp [hieq]
  | succ k ih =>
    intro i hi
    rcases Nat.eq_zero_or_pos i.val with hiz | hpos
    · have hieq : i = ⟨0, hn⟩ := Fin.ext hiz
      simp [hieq]
    · have hfi : (f i).val < i.val := hf.2 i hpos
      have hbase : f^[(f i).val] (f i) = ⟨0, hn⟩ := ih (f i) (by omega)
      calc f^[i.val] i
          = f^[i.val - 1] (f i) := by
              rw [show i.val = (i.val - 1) + 1 from by omega]
              rw [Function.iterate_add_apply, Function.iterate_one]
              rfl
        _ = ⟨0, hn⟩ := iterate_stays_zero hn f hf.1 hbase (by omega)

/-- **Key theorem**: Every canonical tree function is a tree function. -/
theorem IsCanonicalTreeFunction.isTreeFunction (hn : 0 < n) (f : Fin n → Fin n)
    (hf : IsCanonicalTreeFunction hn f) : IsTreeFunction f := by
  unfold IsTreeFunction iterateImage
  have h_all_zero : ∀ i : Fin n, f^[n - 1] i = ⟨0, hn⟩ := fun i => by
    have hbase : f^[i.val] i = ⟨0, hn⟩ := hf.reaches_zero hn f i
    exact iterate_stays_zero hn f hf.1 hbase (by have := i.isLt; omega)
  have himg : Finset.univ.image (f^[n - 1]) = {⟨0, hn⟩} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    constructor
    · simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨0, hn⟩, h_all_zero ⟨0, hn⟩⟩
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact h_all_zero i
  rw [himg, Finset.card_singleton]

/-- Rooting a SimpleGraph at vertex r to get a functional digraph. -/
noncomputable def _root_.SimpleGraph.root {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (h_tree : G.IsTree) (r : V) : V → V :=
  fun v =>
    if v = r then r
    else
      let p := Classical.choose (h_tree.existsUnique_path v r).exists
      p.snd

theorem _root_.SimpleGraph.root_fixed {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (h_tree : G.IsTree) (r : V) : G.root h_tree r r = r := by
  simp [SimpleGraph.root]

open SimpleGraph Walk

theorem _root_.SimpleGraph.reaches_root_in_n_steps {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (root_node : V) (v : V) :
    (G.root hG root_node)^[Fintype.card V] v = root_node := by
  let f := G.root hG root_node
  let d (x : V) := (Classical.choose (hG.existsUnique_path x root_node).exists).length
  have h_reach : ∀ x, f^[d x] x = root_node := by
    intro x
    induction h_dx : d x using Nat.strong_induction_on generalizing x with
    | h k ih =>
      by_cases h_vr : x = root_node
      · have d_root : d root_node = 0 := by
          let p := Classical.choose (hG.existsUnique_path root_node root_node).exists
          have p_is_path : p.IsPath := Classical.choose_spec (hG.existsUnique_path root_node root_node).exists
          have p_nil : p = nil := (hG.existsUnique_path root_node root_node).unique p_is_path IsPath.nil
          exact congr_arg Walk.length p_nil
        rw [<- h_dx, h_vr, d_root, Function.iterate_zero_apply]
      · let p := Classical.choose (hG.existsUnique_path x root_node).exists
        have p_is_path : p.IsPath := Classical.choose_spec (hG.existsUnique_path x root_node).exists
        have h_f_x : f x = p.snd := by unfold f root; rw [if_neg h_vr]
        let q := p.tail
        have q_is_path : q.IsPath := p_is_path.tail
        have h_unique : d (p.snd) = q.length := by
          let p' := Classical.choose (hG.existsUnique_path p.snd root_node).exists
          have p'_is_path : p'.IsPath := Classical.choose_spec (hG.existsUnique_path p.snd root_node).exists
          have : p' = q := (hG.existsUnique_path p.snd root_node).unique p'_is_path q_is_path
          have h_dp : d (p.snd) = p'.length := rfl
          rw [h_dp, this]
        have h_step : d (f x) < k := by
          rw [h_f_x, h_unique]
          have h_p_len : p.length = d x := rfl
          have h_p_tail := p.length_tail_add_one (not_nil_of_ne h_vr)
          have h_q_len : q.length = p.tail.length := rfl
          omega
        have h_dx_succ : d x = (d (f x)).succ := by
          rw [h_f_x, h_unique]
          have h_p_len : p.length = d x := rfl
          have h_p_tail := p.length_tail_add_one (not_nil_of_ne h_vr)
          have h_q_len : q.length = p.tail.length := rfl
          omega
        calc f^[k] x
          _ = f^[d x] x := by rw [h_dx]
          _ = f^[(d (f x)).succ] x := by rw [h_dx_succ]
          _ = f^[d (f x)] (f x) := by rw [Function.iterate_succ_apply]
          _ = root_node := ih (d (f x)) h_step (f x) rfl
  have h_dv : d v < Fintype.card V := by
    let p := Classical.choose (hG.existsUnique_path v root_node).exists
    have p_is_path : p.IsPath := Classical.choose_spec (hG.existsUnique_path v root_node).exists
    exact p_is_path.length_lt
  rw [show Fintype.card V = (Fintype.card V - d v) + d v by omega]
  rw [Function.iterate_add_apply, h_reach]
  apply Function.IsFixedPt.iterate (SimpleGraph.root_fixed G hG root_node)

theorem _root_.SimpleGraph.IsTree.n_pos {V : Type*} [Fintype V] [Nonempty V] {G : SimpleGraph V}
    (_h : G.IsTree) : 0 < Fintype.card V :=
  Fintype.card_pos

/-- Translation from functional gracefulness to graph gracefulness. -/
theorem _root_.SimpleGraph.Iso.edgeFinset_image_lift {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (f : V → ℕ) :
    G.edgeFinset.image (fun edge => edge.lift ⟨fun u v => ((f u : ℤ) - (f v : ℤ)).natAbs, by
      intro u v; dsimp; rw [<- Int.natAbs_neg, neg_sub]⟩) = 
    H.edgeFinset.image (fun edge => edge.lift ⟨fun u v =>
      ((f (e.symm u) : ℤ) - (f (e.symm v) : ℤ)).natAbs, by
      intro u v; dsimp; rw [<- Int.natAbs_neg, neg_sub]⟩) := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨edge, h_edge, rfl⟩
    induction edge using Sym2.inductionOn with
    | hf u v =>
      use s(e u, e v)
      constructor
      · exact H.mem_edgeFinset.mpr ((e.map_rel_iff).mpr (G.mem_edgeFinset.mp h_edge))
      · simp only [Sym2.lift_mk]; rw [e.symm_apply_apply, e.symm_apply_apply]
  · rintro ⟨edge, h_edge, rfl⟩
    induction edge using Sym2.inductionOn with
    | hf u v =>
      use s(e.symm u, e.symm v)
      constructor
      · exact G.mem_edgeFinset.mpr ((e.symm.map_rel_iff).mpr (H.mem_edgeFinset.mp h_edge))
      · simp only [Sym2.lift_mk]; try rw [e.apply_symm_apply, e.apply_symm_apply]

end KRR
