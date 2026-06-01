import KRR.DeterminantalPolynomial

set_option linter.style.longLine false

/-!
# Faithfulness: our `fullDeterminantalPolynomial` is exactly Gnang's gracefulness polynomial

A referee's first attack on a formalization-based refutation is *"is your formal object actually the
paper's object?"* This file closes that gap for the polynomial at the heart of Step 5, mapping our
`fullDeterminantalPolynomial f = vandermonde · edgeWeights` to the two forms Gnang writes.

* **Gnang's `F_f` (arXiv:2202.03178 v3, eq. at line 1006)** — the polynomial whose non-membership in
  the grid ideal *characterizes gracefulness* (line 1011, `G_f` graceful ⟺ `F_f ≢ 0 mod {(x_k)ⁿ}`):
  `F_f = ∏_{i<j} (x_j − x_i)·((x_{f j} − x_j)² − (x_{f i} − x_i)²)`.
  `fullDet_eq_Gnang_Ff` proves `fullDeterminantalPolynomial f = F_f`.

* **Gnang's binomial / "telescoping" form (the `P_f`, `P_g` of lines 1692, 1710)** — every squared
  difference is written as a `t ∈ {0,1}` product of binomials
  `∏_{t∈{0,1}} (x_{h v} − x_v + (−1)ᵗ (x_{h u} − x_u))`.
  `edgeWeights_eq_binomial_tproduct` proves this binomial form equals our `edgeWeights`, for *any* `h`.

Together these show the object Step 5 manipulates (`P_g`, in the binomial form, after the slide
`h = g`) is exactly `fullDeterminantalPolynomial g`. Gnang's three index–blocks (lines 1712–1726)
are then a partition of the pair set `{(u,v) : u < v}` into `v ≤ f(n−1)` / `v` a sibling with
`u ≤ f(n−1)` / `v` a sibling with `f(n−1) < u < v`; on each block the slide `g` agrees with `f`
resp. `f²`, so the blocks reassemble into the single product `∏_{u<v}` over all pairs. The algebraic
content of that reassembly — binomial pair `↦` squared difference — is exactly the lemma below; the
remaining step is the (labelling–dependent) bookkeeping that the three blocks tile all pairs.
-/

open MvPolynomial

namespace KRR

variable {n : ℕ}

/-- The `t ∈ {0,1}` binomial product is a difference of squares: Gnang's telescoping pair
`(a + (+1)b)(a + (−1)b) = a² − b²`. This is the elementary identity underlying every binomial
factor in Gnang's `P_f`/`P_g`. -/
lemma prod_range_two_sign (a b : MvPolynomial (Fin n) ℤ) :
    ∏ t ∈ Finset.range 2, (a + (-1 : MvPolynomial (Fin n) ℤ) ^ t * b) = a ^ 2 - b ^ 2 := by
  rw [Finset.prod_range_succ, Finset.prod_range_one]
  ring

/-- **Binomial form = edge-weight form.** Gnang's binomial-pair product (the form in which `P_f` and
`P_g` are written, lines 1692/1710) equals our `edgeWeightsPolynomial`, for any `h : Fin n → Fin n`.
Specialised to `h = g = slide f L` this is the `P_g` of Step 5. -/
theorem edgeWeights_eq_binomial_tproduct (h : Fin n → Fin n) :
    edgeWeightsPolynomial h
      = ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          ∏ t ∈ Finset.range 2,
            ((MvPolynomial.X (h j) - MvPolynomial.X j)
              + (-1 : MvPolynomial (Fin n) ℤ) ^ t * (MvPolynomial.X (h i) - MvPolynomial.X i)) := by
  rw [edgeWeightsPolynomial]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
  exact (prod_range_two_sign _ _).symm

/-- **`fullDeterminantalPolynomial f` = Gnang's `F_f` (eq. line 1006).** The single product form
whose non-membership in `gridIdeal` is Gnang's gracefulness criterion (line 1011). -/
theorem fullDet_eq_Gnang_Ff (f : Fin n → Fin n) :
    fullDeterminantalPolynomial f
      = ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          ((MvPolynomial.X j - MvPolynomial.X i)
            * ((MvPolynomial.X (f j) - MvPolynomial.X j) ^ 2
              - (MvPolynomial.X (f i) - MvPolynomial.X i) ^ 2)) := by
  rw [fullDeterminantalPolynomial, vandermonde, edgeWeightsPolynomial, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_mul_distrib]

end KRR
