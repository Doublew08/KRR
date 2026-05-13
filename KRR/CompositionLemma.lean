import KRR.Basic
import KRR.Graceful
import KRR.FunctionalReformulation

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
If f is a tree function and its functional digraph has diameter ≥ 3,
then the max distinct labels count is non-increasing under composition f ∘ f.
-/
theorem composition_lemma (f : Fin n → Fin n) (h_tree : IsTreeFunction f) 
    (h_diam : funcDiameter f ≥ 3) :
    ∀ k_f k_f2, IsMaxDistinctEdgeLabels f k_f → IsMaxDistinctEdgeLabels (f ∘ f) k_f2 →
    k_f2 ≤ k_f :=
sorry -- This is the core of the proof, to be filled in Phase 6.

end KRR
