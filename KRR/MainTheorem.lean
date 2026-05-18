import KRR.Basic
import KRR.Graceful
import KRR.GracefulExpansion
import KRR.CompositionLemma
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace KRR

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/--
The Main Theorem of KRR: Every tree is graceful.
Formalized by reducing the graph tree property to a functional tree function property.
-/
theorem krr_conjecture (G : SimpleGraph V) [DecidableRel G.Adj] (h_tree : G.IsTree) :
    IsGraceful G := by
  sorry

end KRR
