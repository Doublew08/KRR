import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic

/-- 
A graceful labeling of a graph with `m` edges is an injective mapping `f` from its vertices 
to the set `{0, ..., m}` such that the induced mapping on edges `|f(u) - f(v)|` is a bijection 
to the set `{1, ..., m}`.
-/

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def IsGracefulLabeling (f : V → ℕ) : Prop :=
  let m := G.edgeFinset.card
  (∀ v, f v ≤ m) ∧ 
  Function.Injective f ∧ 
  (G.edgeFinset.image (fun e => Int.natAbs (f e.1 - f e.2)) = Finset.Icc 1 m)

def IsGraceful : Prop :=
  ∃ f : V → ℕ, IsGracefulLabeling G f

/-- The Kotzig-Ringel-Rosa (Graceful Tree) Conjecture states that every tree is graceful. -/
theorem KRR_Conjecture : ∀ (V : Type*) [Fintype V] [Nonempty V] (G : SimpleGraph V), 
  G.IsTree → IsGraceful G :=
sorry
