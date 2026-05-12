import KRR.Graceful
import Mathlib.Data.ZMod.Basic

/--
Section 2: Functional Reformulation
The paper reformulates the graceful labeling problem in terms of functions 
over the cyclic group Z_n.
-/

variable {n : ℕ} [Fact (0 < n)]

/--
A function f : Z_n → Z_n is τ-Zen if there exists a bijection σ : Z_n → Z_n 
such that the set {τ(σ(i), σ(f(i))) : i ∈ Z_n} = Z_n.
-/
def IsTauZen (τ : ZMod n → ZMod n → ZMod n) (f : ZMod n → ZMod n) : Prop :=
  ∃ σ : Equiv.Perm (ZMod n), 
    Finset.univ.image (fun i => τ (σ i) (σ (f i))) = Finset.univ

/--
The paper claims that if τ(i, j) = |j - i|, then τ-Zen graphs correspond to 
graceful graphs. Note: The paper uses a specific mapping for trees where 
the number of edges is n-1.
-/
def τ_graceful (i j : ZMod n) : ZMod n := j - i

-- Future work: Formalize Lemma 1 and Lemma 2 from the paper.
