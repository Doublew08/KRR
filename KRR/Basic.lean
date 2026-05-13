/-
Copyright (c) 2026 Doublew08. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Doublew08, Antigravity
-/
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Function.Iterate
import Mathlib.GroupTheory.Perm.Basic

/-!
# KRR Foundations: Transformation Monoid and Functional Digraphs

## Main definitions

* `FunctionalDigraph` — digraph where vertex `i` has edge to `f(i)`
* `IsTreeFunction` — `|f^(n-1)(ℤₙ)| = 1`
* `IsCanonicalTreeFunction` — f(0)=0 and f(i)<i for i>0
* `treeGraphOfFunction` — SimpleGraph bridge
-/

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
  -- We induct on i.val; Lean 4 needs termination.
  -- Use a helper with Nat induction on a decreasing bound.
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
    · -- i = 0
      have hieq : i = ⟨0, hn⟩ := Fin.ext hiz
      simp [hieq]
    · -- i.val ≥ 1
      have hfi : (f i).val < i.val := hf.2 i hpos
      have hbase : f^[(f i).val] (f i) = ⟨0, hn⟩ := ih (f i) (by omega)
      -- f^[i.val](i) = f^[i.val - 1](f i), and i.val-1 ≥ (f i).val
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
  -- Every element maps to 0 under f^[n-1]
  have h_all_zero : ∀ i : Fin n, f^[n - 1] i = ⟨0, hn⟩ := fun i => by
    have hbase : f^[i.val] i = ⟨0, hn⟩ := hf.reaches_zero hn f i
    exact iterate_stays_zero hn f hf.1 hbase (by have := i.isLt; omega)
  -- The image is exactly {0}
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




end KRR
