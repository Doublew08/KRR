import KRR.Basic
import KRR.Graceful
import KRR.Polynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BigOperators
open KRR
open Finset

variable {n : ℕ}

theorem eval_det_poly (hn : 1 < n) (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.eval (fun i => ((σ i).val : ℤ)) (determinantalPolynomial f) =
    ∏ i : {i : Fin n // i.val > 0}, (((σ i.1).val : ℤ) - ((σ (f i.1)).val : ℤ)) := by
  dsimp [determinantalPolynomial]
  rw [map_prod]
  apply prod_congr rfl
  intro i _
  rw [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_X]

lemma natAbs_prod {α : Type*} (s : Finset α) (g : α → ℤ) :
    Int.natAbs (∏ x ∈ s, g x) = ∏ x ∈ s, Int.natAbs (g x) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [prod_cons, prod_cons, Int.natAbs_mul, ih]

theorem graceful_evaluation_proof (hn : 1 < n) (f : Fin n → Fin n) (σ : Equiv.Perm (Fin n))
    (h_tree : IsTreeFunction f) (hf_canon : IsCanonicalTreeFunction (by omega) f)
    (h_grace : IsAlreadyGraceful (conjugate f σ)) :
    Int.natAbs (MvPolynomial.eval (fun i => ((σ i).val : ℤ)) (determinantalPolynomial f)) =
    (n - 1).factorial := by
  sorry
