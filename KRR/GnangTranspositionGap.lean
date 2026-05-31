import KRR.AlgebraicNullstellensatz
import KRR.DeterminantalPolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Formal Disproof of Gnang's Transposition Invariance

Gnang claims (Lines 2066–2079) that his chosen transposition `τ` fixes the
canonical representative of the polynomial `R = P_g - P_f`. He implicitly assumes
that swapping the labels of the vertices permutes the graceful labelings and
flips the sign of `W_g` identically to the Vandermonde determinant, resulting
in a symmetric product.

However, Gnang defines his transposition as swapping the root `f(n-1)` with one of
its children `v ∈ f⁻¹({f(n-1)})`. Because the root is a parent (not a leaf),
swapping its label with a child completely alters the structure of the edge lengths
for any other edges connected to the root.

We provide a direct, mathematically verified counterexample to this.
Let `g = f² = [2, 3, 3, 3]`, where `3` is the root and `2` is a child of `3`.
Gnang's transposition is `τ = (2, 3)`, which swaps the root and its child.
Let `p` be the graceful labeling `[1, 3, 2, 0]`.
Then `τ(p) = [1, 3, 0, 2]`.
We prove that `P_g(p) = 51840`, while `P_g(τ(p)) = 0`.
Since `51840 ≠ 0`, `P_g` is NOT invariant under `τ`.
Thus, the canonical representative is NOT invariant, formally breaking Gnang's
core symmetry claim before the Monomial Support Lemma is even invoked.
-/

namespace KRR

/-- 
We use the tree `g = f^2`, where `f = [1, 2, 3, 3]` is a path graph.
Thus `g(0)=2, g(1)=3, g(2)=3, g(3)=3`. `3` is the root, `2` is its child. 
-/
def g4_sq : Fin 4 → Fin 4 := ![2, 3, 3, 3]

/-- The graceful labeling `p = [1, 3, 2, 0]`. -/
def p_label_sq : Fin 4 → ℤ := ![1, 3, 2, 0]

/-- Gnang's transposition `τ = (2, 3)`, swapping the root and its child. -/
def tau4_root : Equiv.Perm (Fin 4) := Equiv.swap 2 3

/-- `τ(p) = [1, 3, 0, 2]`. -/
def tau_p_label_sq : Fin 4 → ℤ := fun i => p_label_sq (tau4_root i)

private lemma filter_gt_0 :
    (Finset.univ : Finset (Fin 4)).filter (fun j => (0 : Fin 4).val < j.val) = {1, 2, 3} := by decide
private lemma filter_gt_1 :
    (Finset.univ : Finset (Fin 4)).filter (fun j => (1 : Fin 4).val < j.val) = {2, 3} := by decide
private lemma filter_gt_2 :
    (Finset.univ : Finset (Fin 4)).filter (fun j => (2 : Fin 4).val < j.val) = {3} := by decide
private lemma filter_gt_3 :
    (Finset.univ : Finset (Fin 4)).filter (fun j => (3 : Fin 4).val < j.val) = ∅ := by decide

private lemma prod_123 (f : Fin 4 → ℤ) : ∏ x ∈ ({1, 2, 3} : Finset (Fin 4)), f x = f 1 * f 2 * f 3 := by
  have h : ({1, 2, 3} : Finset (Fin 4)) = insert (1 : Fin 4) (insert (2 : Fin 4) {(3 : Fin 4)}) := by rfl
  rw [h, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

private lemma prod_23 (f : Fin 4 → ℤ) : ∏ x ∈ ({2, 3} : Finset (Fin 4)), f x = f 2 * f 3 := by
  have h : ({2, 3} : Finset (Fin 4)) = insert (2 : Fin 4) {(3 : Fin 4)} := by rfl
  rw [h, Finset.prod_insert (by decide), Finset.prod_singleton]

/-- `P_g(p) = 51840` -/
theorem Pg_eval_p_sq :
    MvPolynomial.eval p_label_sq (fullDeterminantalPolynomial g4_sq) = 51840 := by
  have hp0 : p_label_sq 0 = 1 := by rfl
  have hp1 : p_label_sq 1 = 3 := by rfl
  have hp2 : p_label_sq 2 = 2 := by rfl
  have hp3 : p_label_sq 3 = 0 := by rfl
  simp only [fullDeterminantalPolynomial, g4_sq, edgeWeightsPolynomial, vandermonde,
             map_mul, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
  simp only [Fin.prod_univ_four, filter_gt_0, filter_gt_1, filter_gt_2, filter_gt_3]
  simp only [prod_123, prod_23, Finset.prod_singleton, Finset.prod_empty, mul_one,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num [hp0, hp1, hp2, hp3]

/-- `P_g(τ(p)) = 0` -/
theorem Pg_eval_tau_p_sq :
    MvPolynomial.eval tau_p_label_sq (fullDeterminantalPolynomial g4_sq) = 0 := by
  have ht0 : tau_p_label_sq 0 = 1 := by rfl
  have ht1 : tau_p_label_sq 1 = 3 := by rfl
  have ht2 : tau_p_label_sq 2 = 0 := by rfl
  have ht3 : tau_p_label_sq 3 = 2 := by rfl
  simp only [fullDeterminantalPolynomial, g4_sq, edgeWeightsPolynomial, vandermonde,
             map_mul, map_prod, map_sub, map_pow, MvPolynomial.eval_X]
  simp only [Fin.prod_univ_four, filter_gt_0, filter_gt_1, filter_gt_2, filter_gt_3]
  simp only [prod_123, prod_23, Finset.prod_singleton, Finset.prod_empty, mul_one,
             Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num [ht0, ht1, ht2, ht3]

/-- 
Because `P_g` evaluates differently on `p` and `τ(p)`, it is impossible for `τ(P_g)` 
to be equivalent to `P_g` modulo the grid ideal.
-/
theorem tau_Pg_not_equiv_Pg_sq :
    ¬ (MvPolynomial.rename tau4_root (fullDeterminantalPolynomial g4_sq) - 
       fullDeterminantalPolynomial g4_sq ∈ gridIdeal 4) := by
  intro h
  have hp_grid : ∀ i, p_label_sq i ∈ grid 4 := by
    intro i
    fin_cases i <;> simp [p_label_sq, grid, Finset.mem_image, Finset.mem_range] <;> decide
  have heval := eval_eq_zero_of_mem_gridIdeal _ h p_label_sq hp_grid
  have h_rename : MvPolynomial.eval p_label_sq (MvPolynomial.rename tau4_root (fullDeterminantalPolynomial g4_sq)) = 0 := by
    rw [MvPolynomial.eval_rename]
    exact Pg_eval_tau_p_sq
  simp [h_rename, Pg_eval_p_sq] at heval

/--
The automorphism condition `g ∘ τ = τ ∘ g` fails for `τ = (2, 3)` on `g = [2, 3, 3, 3]`.
Specifically at vertex `0`: `g(τ(0)) = g(0) = 2` but `τ(g(0)) = τ(2) = 3 ≠ 2`.
This is the theoretical root cause of the failure: τ is not a graph automorphism of g,
so it has no obligation to preserve the graceful edge-difference structure.
Gnang provides no proof that τ IS an automorphism — the permutation of Φ(g) is assumed.
-/
theorem tau_not_automorphism_g4_sq :
    ¬ ∀ i : Fin 4, g4_sq (tau4_root i) = tau4_root (g4_sq i) := by decide

/--
**Formal disproof of Gnang's core symmetry claim** (arXiv:2202.03178, Lines 2066–2079).

Gnang asserts that his chosen transposition τ fixes the canonical representative of P_g
modulo the grid ideal I_grid. More precisely, his proof requires:

  ∀ g τ,  rename τ P_g − P_g ∈ I_grid

We refute this with the witness g = [2,3,3,3] and τ = (2,3) — Gnang's own example.
`tau_Pg_not_equiv_Pg_sq` proves the negation for this specific pair, so the universal
claim is false. Combined with `tau_not_automorphism_g4_sq`, which shows τ is not even a
graph automorphism of g, we have the root cause: Gnang's proof assumes a symmetry of P_g
that τ has no obligation to satisfy.
-/
theorem gnang_core_symmetry_false :
    ¬ ∀ (g : Fin 4 → Fin 4) (τ : Equiv.Perm (Fin 4)),
        MvPolynomial.rename τ (fullDeterminantalPolynomial g) -
        fullDeterminantalPolynomial g ∈ gridIdeal 4 :=
  fun h => tau_Pg_not_equiv_Pg_sq (h g4_sq tau4_root)

end KRR
