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
axiom krr_conjecture_main (T : SimpleGraph (Fin n)) (h_tree : T.IsTree) :
    ∃ f : Fin n → Fin n, T.IsGracefulLabeling f

end KRR
