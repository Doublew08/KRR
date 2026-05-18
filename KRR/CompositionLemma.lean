import KRR.Basic
import KRR.Graceful
import KRR.FunctionalReformulation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Max

/-!
# Phase 6: Composition Lemma

This module formalizes Lemma 3.2 from the Gnang paper, which is the most
critical logical step in the proof.

Lemma 3.2 (Composition Lemma):
For all tree functions f with diameter ≥ 3, the maximum number of distinct
edge labels of f² is less than or equal to the maximum number of distinct
edge labels of f.
-/

namespace KRR

variable {n : ℕ}

/--
Lemma 3.2 (Composition Lemma):
If f is a tree function, the maximum number of distinct edge labels across
all vertex labelings σ is non-increasing under functional composition f ∘ f.
-/
theorem composition_lemma (hn : 1 < n) (f : Fin n → Fin n) (h_tree : IsTreeFunction f) :
    (Finset.univ.image (fun σ : Equiv.Perm (Fin n) => (edgeLabelSet (conjugate f σ)).card)).max =
    (Finset.univ.image (fun σ : Equiv.Perm (Fin n) => (edgeLabelSet (conjugate (f ∘ f) σ)).card)).max := by
  sorry

end KRR
