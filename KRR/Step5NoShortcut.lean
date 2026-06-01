import KRR.Telescoping

/-!
# Step 5 cannot be closed by a contradiction *internal* to this framework

Gnang's Step 5 is a proof by contradiction: assume `f` ungraceful (`P_f ∈ I`) and `g`
graceful (`P_g ∉ I`), and derive a contradiction. His route is to show that the remainder
`R_{f,g} = P_g − P_f` has a vanishing canonical representative, i.e. `R_{f,g} ∈ I` (via the
`τ`-symmetry argument of lines 2066–2174).

The theorem below shows that goal is **logically equivalent to the conclusion** `P_g ∈ I`
(`g` ungraceful). So "find another contradiction inside this framework" is not a smaller task
than proving the lemma: any valid derivation of `R_{f,g} ∈ I` *is* a proof that `g` is
ungraceful. There is no algebraic shortcut — `R_{f,g}` agrees with `P_g` on the whole grid
(because `P_f` vanishes there), so it carries exactly the same information.

Combined with `remainder_not_in_ideal` (which proves `R_{f,g} ∉ I` under these very
assumptions), this says: under `f` ungraceful ∧ `g` graceful the framework is *consistent* —
`R_{f,g} ∉ I` is true and provable — so no internal contradiction exists to exploit. A
contradiction can only come from the external fact that the premises are jointly impossible,
which is precisely the Composition Lemma (hence, by Gnang's own reduction, KRR itself).
-/

namespace KRR

variable {n : ℕ}

/-- **No shortcut.** Given `f` ungraceful (`P_f ∈ I`), Step 5's target `R_{f,g} ∈ I` is
equivalent to the lemma's conclusion `P_g ∈ I`. -/
theorem remainder_in_ideal_iff_Pg_in_ideal [NeZero n] (f g : Fin n → Fin n)
    (h_Pf : fullDeterminantalPolynomial f ∈ gridIdeal n) :
    remainderPolynomial f g ∈ gridIdeal n
      ↔ fullDeterminantalPolynomial g ∈ gridIdeal n := by
  constructor
  · intro hR
    have hg : fullDeterminantalPolynomial g
        = remainderPolynomial f g + fullDeterminantalPolynomial f := by
      simp [remainderPolynomial]
    rw [hg]; exact Submodule.add_mem _ hR h_Pf
  · intro hPg
    exact Submodule.sub_mem _ hPg h_Pf

end KRR
