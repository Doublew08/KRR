import KRR.PartAInvariance
import KRR.Telescoping

set_option linter.style.longLine false

/-!
# Witness: the conclusion of Gnang's Step 5 "Part B" is false

In Gnang's proof of the Composition Lemma (arXiv:2202.03178 v3), Step 5 is a proof by
contradiction. Under the premise `f` ungraceful (`P_f ∈ I`) ∧ `g` graceful (`P_g ∉ I`) it
derives, for the prescribed transposition `τ = (f(n-1), v)` (`v` a sibling leaf of the deepest
leaf `n-1`):

* **Part A** (the transposition-invariance step): `τ` fixes the canonical representative of
  `R_{f,g}` — i.e. `τ ∈ Aut(canonical representative of P_g)`. Verified: `rename_fullDet_eq_of_aut`
  shows `rename τ P_g = P_g` *unconditionally*, since `τ` is a genuine graph automorphism of `G_g`
  (the slide turns `f(n-1)` and every sibling into leaf–children of `f²(n-1)`).

* **Part B** (the subsequent case analysis): concludes the *opposite*,
  `τ ∉ Aut(Canonical Representative of P_g)`, via a three–option argument whose Option 3
  (cross–summand "symmetry broadening" cancellations) is dismissed using the complementary
  labeling symmetry.

These two are contradictory **about the same object**: Gnang's own canonical representative is
the grid/Lagrange form `∑_h P_g(h) L_h(x)` (his Example following the Monomial Overlapping Lemma),
and there he states `Aut(polynomial) ⊆ Aut(canonical representative)`. Since `gridIdeal` is
permutation–stable, `rename τ P_g = P_g` descends to the canonical representative. So Part A forces
`τ ∈ Aut(canonical representative of P_g)`, refuting Part B.

This file makes the refutation machine-checked: under Step 5's premise (`g` graceful) `P_g` is a
**τ-invariant polynomial with a nonzero canonical representative**. Part B claims no such object
exists; here it is. The Step 5 contradiction is therefore *spurious*.

Combined with `remainder_in_ideal_iff_Pg_in_ideal` and `remainder_not_in_ideal`
(`Step5NoShortcut.lean`, `Telescoping.lean`): under the premise, `R_{f,g} ∉ I` is genuinely
*true* and provable, so no contradiction internal to the `τ`-symmetry / ideal framework exists.
A valid proof of the Composition Lemma is not recoverable from this route — it would have to
establish `P_g ∈ I` (`g` ungraceful) outright, which under the premise *is* the lemma.
-/

open MvPolynomial

namespace KRR

variable {n : ℕ}

/-- `g` graceful (some conjugate is already graceful) ⟹ `P_g ∉ gridIdeal`: the canonical
representative of `P_g` is nonzero. Evaluate at the graceful labelling point, which lies on the
grid; both the Vandermonde and edge–weight factors are nonzero there. -/
theorem fullDet_not_mem_gridIdeal_of_graceful [NeZero n] (g : Fin n → Fin n)
    (σ : Equiv.Perm (Fin n)) (hσ : IsAlreadyGraceful (conjugate g σ)) :
    fullDeterminantalPolynomial g ∉ gridIdeal n := by
  intro hmem
  rw [mem_gridIdeal_iff_eval_zero] at hmem
  have hx : ∀ i, ((σ i).val : ℤ) ∈ grid n := by
    intro i
    simp only [grid, Finset.mem_image, Finset.mem_range]
    exact ⟨(σ i).val, (σ i).isLt, rfl⟩
  have hzero := hmem (fun i => ((σ i).val : ℤ)) hx
  rw [fullDeterminantalPolynomial, map_mul] at hzero
  exact mul_ne_zero
    (eval_vandermonde_ne_zero_of_injective _
      (fun a b h => σ.injective (Fin.val_injective (by exact_mod_cast h))))
    (eval_edgeWeightsPolynomial_ne_zero_of_graceful g σ hσ) hzero

/-- **Part B's conclusion is false.** Under Step 5's premise (`g` graceful) and with Gnang's
prescribed transposition `τ` — a graph automorphism of `G_g` (`∀ i, g (τ i) = τ (g i)`) —
the determinantal polynomial `P_g` is simultaneously:

* fixed by `τ`  (`rename τ P_g = P_g`), hence `τ` fixes its canonical representative, and
* outside `gridIdeal`, i.e. its canonical representative is **nonzero**.

So `τ ∈ Aut(canonical representative of P_g)` with that representative nonvanishing — exactly the
configuration Gnang's Part B rules out. The Step 5 contradiction does not hold. -/
theorem partB_conclusion_false [NeZero n] (g : Fin n → Fin n) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ i, g (τ i) = τ (g i))
    (σ : Equiv.Perm (Fin n)) (hσ : IsAlreadyGraceful (conjugate g σ)) :
    rename τ (fullDeterminantalPolynomial g) = fullDeterminantalPolynomial g
      ∧ fullDeterminantalPolynomial g ∉ gridIdeal n :=
  ⟨rename_fullDet_eq_of_aut g τ hτ, fullDet_not_mem_gridIdeal_of_graceful g σ hσ⟩

/-! ### Closing the interpretive escapes: the descent to the canonical representative is rigorous

A possible objection to the refutation above is that Part A's invariance is at the *polynomial*
level (`rename τ P_g = P_g`) whereas Part B speaks of the *canonical representative*
— and perhaps `rename τ` does not descend to it. It does. The grid ideal is permutation–stable,
so `rename τ` acts on the quotient `MvPolynomial / gridIdeal` (= the space of canonical
representatives) and Part A's invariance descends verbatim. We make this fully machine-checked,
so the refutation no longer depends on any reading of Gnang's prose. -/

/-- `gridIdeal` is stable under variable permutation: a permutation of indices maps a grid point
to a grid point, so vanishing on the grid is preserved. -/
theorem rename_mem_gridIdeal [NeZero n] (τ : Equiv.Perm (Fin n)) (P : MvPolynomial (Fin n) ℤ)
    (hP : P ∈ gridIdeal n) : rename τ P ∈ gridIdeal n := by
  rw [mem_gridIdeal_iff_eval_zero] at hP ⊢
  intro x hx
  rw [MvPolynomial.eval_rename]
  exact hP (x ∘ τ) (fun i => hx (τ i))

/-- Hence `rename τ` is a *bijection* on `gridIdeal` — it descends to an automorphism of the
quotient `MvPolynomial / gridIdeal`, i.e. of the space of canonical representatives. -/
theorem rename_mem_gridIdeal_iff [NeZero n] (τ : Equiv.Perm (Fin n)) (P : MvPolynomial (Fin n) ℤ) :
    rename τ P ∈ gridIdeal n ↔ P ∈ gridIdeal n := by
  refine ⟨fun h => ?_, rename_mem_gridIdeal τ P⟩
  have h2 := rename_mem_gridIdeal τ.symm _ h
  rwa [MvPolynomial.rename_rename, Equiv.symm_comp_self, MvPolynomial.rename_id,
    AlgHom.id_apply] at h2

/-- **Aut(polynomial) ⊆ Aut(canonical representative)** for the relevant case: if `τ` fixes `P`
as a polynomial, it fixes the canonical representative of `P` (their difference lies in
`gridIdeal`, i.e. they agree on the grid). This is the inclusion Gnang states in his Example
following the Monomial Overlapping Lemma; the descent is along the permutation–stable ideal. -/
theorem aut_fixes_canonicalRep_of_aut (τ : Equiv.Perm (Fin n)) (P : MvPolynomial (Fin n) ℤ)
    (h : rename τ P = P) : rename τ P - P ∈ gridIdeal n := by
  rw [h, sub_self]; exact Submodule.zero_mem _

/-- **Part B's conclusion is false — at the level of the canonical representative.** Under Step 5's
premise (`g` graceful) with Gnang's prescribed graph automorphism `τ`, the canonical
representative of `P_g` is `τ`-invariant (`rename τ P_g - P_g ∈ gridIdeal`) **and** nonzero
(`P_g ∉ gridIdeal`). That is exactly `τ ∈ Aut(canonical representative of P_g)` with the
representative nonvanishing — the configuration Part B declares impossible. This statement is
phrased entirely in Gnang's own canonical-representative language, so it refutes Part B under
*any* reading of its prose. -/
theorem partB_conclusion_false_canonical [NeZero n] (g : Fin n → Fin n) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ i, g (τ i) = τ (g i))
    (σ : Equiv.Perm (Fin n)) (hσ : IsAlreadyGraceful (conjugate g σ)) :
    rename τ (fullDeterminantalPolynomial g) - fullDeterminantalPolynomial g ∈ gridIdeal n
      ∧ fullDeterminantalPolynomial g ∉ gridIdeal n :=
  ⟨aut_fixes_canonicalRep_of_aut τ _ (rename_fullDet_eq_of_aut g τ hτ),
   fullDet_not_mem_gridIdeal_of_graceful g σ hσ⟩

end KRR
