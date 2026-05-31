import KRR.DeterminantalPolynomial
import KRR.Telescoping
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Polynomial Evaluation for f3

For `f3 = ![0, 0, 1] : Fin 3 → Fin 3`, we compute that the remainder polynomial
`R_{f3, f3²} = P_{f3²} - P_{f3}` evaluates to 24 at the grid point `x3 = [0, 1, 2]`.

Since elements of `gridIdeal 3` vanish on all grid points, this shows `R_{f3, f3²} ∉ gridIdeal 3`.

Note: both `f3` and `f3² = const 0` are graceful tree functions. Gnang's sibling symmetry
argument (Section 3 of arXiv:2202.03178) is invoked only when `f²` is NOT graceful, so
this example is outside the scope of that argument.
-/

namespace KRR

-- The specific tree function and evaluation point
def f3 : Fin 3 → Fin 3 := ![0, 0, 1]
def x3 : Fin 3 → ℤ  := ![0, 1, 2]

-- Filter lemmas for Fin 3 (proved by decide)
private lemma filter_gt_0 :
    (Finset.univ : Finset (Fin 3)).filter (fun j => (0 : Fin 3).val < j.val) = {1, 2} := by decide
private lemma filter_gt_1 :
    (Finset.univ : Finset (Fin 3)).filter (fun j => (1 : Fin 3).val < j.val) = {2} := by decide
private lemma filter_gt_2 :
    (Finset.univ : Finset (Fin 3)).filter (fun j => (2 : Fin 3).val < j.val) = ∅ := by decide

private lemma f3_comp_f3 : f3 ∘ f3 = fun _ => (0 : Fin 3) := by
  ext i; fin_cases i <;> decide

/-- `R_{f3, f3²}` evaluates to 24 at the grid point `x3 = [0,1,2]`.
The key vanishing: the W_{f3} factor at `(i=1, j=2)` is `(x₁-x₂)²-(x₀-x₁)² = 1-1 = 0`,
so `P_{f3}(x3) = 0`. Meanwhile `P_{f3²}(x3) = V(x3) · W_{f3²}(x3) = 2 · 12 = 24`. -/
theorem remainder_eval_f3_ne_zero :
    MvPolynomial.eval x3 (remainderPolynomial f3 (f3 ∘ f3)) = 24 := by
  have hx3_0 : x3 0 = (0 : ℤ) := by decide
  have hx3_1 : x3 1 = (1 : ℤ) := by decide
  have hx3_2 : x3 2 = (2 : ℤ) := by decide
  have hf3_1 : f3 1 = (0 : Fin 3) := by decide
  have hf3_2 : f3 2 = (1 : Fin 3) := by decide
  have hWf3 : MvPolynomial.eval x3 (edgeWeightsPolynomial f3) = 0 := by
    simp only [edgeWeightsPolynomial, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : Fin 3))
    apply Finset.prod_eq_zero
      (show (2 : Fin 3) ∈ Finset.univ.filter (fun j : Fin 3 => (1 : Fin 3).val < j.val)
        from by decide)
    rw [hf3_2, hf3_1, hx3_0, hx3_1, hx3_2]; norm_num
  simp only [remainderPolynomial, fullDeterminantalPolynomial, map_sub, map_mul,
             hWf3, mul_zero, sub_zero, f3_comp_f3]
  simp only [vandermonde, edgeWeightsPolynomial, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
  simp only [Fin.prod_univ_three]
  simp only [filter_gt_0, filter_gt_1, filter_gt_2]
  simp only [Finset.prod_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))),
             Finset.prod_singleton, Finset.prod_empty, mul_one]
  simp only [hx3_0, hx3_1, hx3_2]
  norm_num

/-- Corollary: `R_{f3, f3²} ∉ gridIdeal 3`. -/
theorem remainder_not_in_gridIdeal : ¬ remainderPolynomial f3 (f3 ∘ f3) ∈ gridIdeal 3 := by
  intro h
  have hx3_in_grid : ∀ i : Fin 3, x3 i ∈ grid 3 := by
    intro i; fin_cases i <;> simp [x3, grid, Finset.mem_image, Finset.mem_range] <;> decide
  have := eval_eq_zero_of_mem_gridIdeal _ h x3 hx3_in_grid
  rw [remainder_eval_f3_ne_zero] at this
  norm_num at this

end KRR
