import KRR.DeterminantalPolynomial
import Mathlib.Algebra.MvPolynomial.Rename

set_option linter.style.longLine false

/-!
# Part A of Gnang's Step 5 is a theorem: graph automorphisms fix `P_g`

Gnang's "transposition invariance" (arXiv:2202.03178 v3) is, correctly
read, the claim that a graph automorphism `τ` of `G_g` fixes the determinantal polynomial
`P_g = fullDeterminantalPolynomial g`. We prove this in full generality.

Gnang's prescribed `τ = (f(n-1), v)` (v a sibling of the deepest leaf `n-1`) is parent↔child
in `G_f`, but the slide construction makes `f(n-1)` and `n-1` *sibling leaves* of `G_g`, so
`τ ∈ Aut(G_g)` and this lemma applies.

Key idea: `P_g = ∏_{i<j} (X_j - X_i)(e_j - e_i)` with `e_k = (X_{g k} - X_k)^2`.
Under any permutation the two sign flips cancel *pairwise*; `τ ∈ Aut(G_g)` gives
`rename τ e_k = e_{τ k}`.
-/

open Finset

namespace KRR

variable {n : ℕ}

/-- The product over ordered pairs `i < j` of `(a j - a i)(b j - b i)` is invariant under
any permutation `τ` of the index set: the two sign flips cancel pairwise. -/
theorem D_perm_invariant {R : Type*} [CommRing R] (a b : Fin n → R) (τ : Equiv.Perm (Fin n)) :
    ∏ p ∈ univ.filter (fun p : Fin n × Fin n => p.1.val < p.2.val),
        (a (τ p.2) - a (τ p.1)) * (b (τ p.2) - b (τ p.1))
    = ∏ p ∈ univ.filter (fun p : Fin n × Fin n => p.1.val < p.2.val),
        (a p.2 - a p.1) * (b p.2 - b p.1) := by
  apply Finset.prod_nbij'
    (i := fun p => if τ p.1 < τ p.2 then (τ p.1, τ p.2) else (τ p.2, τ p.1))
    (j := fun q => if τ.symm q.1 < τ.symm q.2 then (τ.symm q.1, τ.symm q.2) else (τ.symm q.2, τ.symm q.1))
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, ← Fin.lt_def] at hp ⊢
    have hne : τ p.1 ≠ τ p.2 := fun he => (ne_of_lt hp) (τ.injective he)
    split_ifs with h
    · exact h
    · dsimp only; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
  · intro q hq
    simp only [mem_filter, mem_univ, true_and, ← Fin.lt_def] at hq ⊢
    have hne : τ.symm q.1 ≠ τ.symm q.2 := fun he => (ne_of_lt hq) (τ.symm.injective he)
    split_ifs with h
    · exact h
    · dsimp only; exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
  · intro p hp
    simp only [mem_filter, mem_univ, true_and, ← Fin.lt_def] at hp
    by_cases h : τ p.1 < τ p.2
    · rw [if_pos h]; simp only [Equiv.symm_apply_apply]; rw [if_pos hp]
    · rw [if_neg h]; simp only [Equiv.symm_apply_apply]; rw [if_neg (not_lt.mpr hp.le)]
  · intro q hq
    simp only [mem_filter, mem_univ, true_and, ← Fin.lt_def] at hq
    by_cases h : τ.symm q.1 < τ.symm q.2
    · rw [if_pos h]; simp only [Equiv.apply_symm_apply]; rw [if_pos hq]
    · rw [if_neg h]; simp only [Equiv.apply_symm_apply]; rw [if_neg (not_lt.mpr hq.le)]
  · intro p hp
    by_cases h : τ p.1 < τ p.2
    · rw [if_pos h]; try ring
    · rw [if_neg h]; try ring

/-- Convert a nested `∏ i, ∏ j>i` into a single product over ordered pairs. -/
theorem nested_eq_pairs {R : Type*} [CommRing R] (t : Fin n → Fin n → R) :
    (∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i.val < j.val), t i j)
    = ∏ p ∈ univ.filter (fun p : Fin n × Fin n => p.1.val < p.2.val), t p.1 p.2 := by
  classical
  conv_rhs => rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product]
  exact Finset.prod_congr rfl (fun i _ => Finset.prod_filter _ _)

/-- **Part A, general form.** If `τ` is a graph automorphism of `G_g` (i.e. `g ∘ τ = τ ∘ g`),
then renaming variables by `τ` fixes the determinantal polynomial `P_g`. -/
theorem rename_fullDet_eq_of_aut (g : Fin n → Fin n) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ i, g (τ i) = τ (g i)) :
    MvPolynomial.rename τ (fullDeterminantalPolynomial g) = fullDeterminantalPolynomial g := by
  set e : Fin n → MvPolynomial (Fin n) ℤ := fun k => (MvPolynomial.X (g k) - MvPolynomial.X k) ^ 2 with he
  have hvan : vandermonde n = ∏ p ∈ univ.filter (fun p : Fin n × Fin n => p.1.val < p.2.val),
      (MvPolynomial.X p.2 - MvPolynomial.X p.1) := by
    rw [vandermonde, nested_eq_pairs]
  have hedge : edgeWeightsPolynomial g
      = ∏ p ∈ univ.filter (fun p : Fin n × Fin n => p.1.val < p.2.val), (e p.2 - e p.1) := by
    rw [edgeWeightsPolynomial, nested_eq_pairs]
  -- rename of e_k is e_{τ k}, using the automorphism hypothesis
  have hren_e : ∀ k, MvPolynomial.rename τ (e k) = e (τ k) := by
    intro k
    simp only [he, map_pow, map_sub, MvPolynomial.rename_X]
    rw [hτ k]
  rw [fullDeterminantalPolynomial, map_mul, hvan, hedge,
      map_prod, map_prod]
  simp only [map_sub, MvPolynomial.rename_X, hren_e]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact D_perm_invariant (fun k => MvPolynomial.X k) e τ

/-! ### Gnang's slide construction makes the transposition an automorphism

`g` is obtained from `f` by sliding the sibling group `f⁻¹({f L})` of the deepest leaf `L`
one edge toward the root: `g i = f² i` on that group, else `f i`. Equivalently
`slide f L i = if f i = f L then f (f i) else f i`. We prove that Gnang's prescribed
transposition `τ = (f L, L)` is a graph automorphism of `G_g`, hence (by
`rename_fullDet_eq_of_aut`) fixes `P_g`. -/

/-- Gnang's slide of `f` at the deepest leaf `L`. -/
def slide (f : Fin n → Fin n) (L : Fin n) : Fin n → Fin n :=
  fun i => if f i = f L then f (f i) else f i

/-- Gnang's transposition `τ = (f L, L)` is a graph automorphism of `G_{slide f L}`.
Needs only: `f L` is not a fixed point (`f (f L) ≠ f L`, from diameter ≥3) and `L` is a
leaf (`∀ i, f i ≠ L`). -/
theorem slide_swap_aut (f : Fin n → Fin n) (L : Fin n)
    (h0 : f (f L) ≠ f L) (hleaf : ∀ i, f i ≠ L) :
    ∀ i, slide f L (Equiv.swap (f L) L i) = Equiv.swap (f L) L (slide f L i) := by
  have hSL : slide f L L = f (f L) := by simp [slide]
  have hSa : slide f L (f L) = f (f L) := by simp only [slide]; rw [if_neg h0]
  have hτc : Equiv.swap (f L) L (f (f L)) = f (f L) :=
    Equiv.swap_apply_of_ne_of_ne h0 (hleaf (f L))
  intro i
  by_cases hia : i = f L
  · subst hia; rw [Equiv.swap_apply_left, hSL, hSa, hτc]
  · by_cases hib : i = L
    · subst hib; rw [Equiv.swap_apply_right, hSa, hSL, hτc]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      by_cases hf : f i = f L
      · have hs : slide f L i = f (f L) := by simp only [slide]; rw [if_pos hf, hf]
        rw [hs, hτc]
      · have hs : slide f L i = f i := by simp only [slide]; rw [if_neg hf]
        rw [hs]; exact (Equiv.swap_apply_of_ne_of_ne hf (hleaf i)).symm

/-- **Part A, for Gnang's prescribed transposition, all `n`.** Under the slide construction,
renaming by `τ = (f L, L)` fixes `P_g`. -/
theorem rename_fullDet_slide (f : Fin n → Fin n) (L : Fin n)
    (h0 : f (f L) ≠ f L) (hleaf : ∀ i, f i ≠ L) :
    MvPolynomial.rename (Equiv.swap (f L) L) (fullDeterminantalPolynomial (slide f L))
      = fullDeterminantalPolynomial (slide f L) :=
  rename_fullDet_eq_of_aut _ _ (slide_swap_aut f L h0 hleaf)

/-! ### Concrete instance

For the slide `g = [0,0,1,1]` (root 0, claw centred at 1), Gnang's transposition `τ = (2,3)`
swaps the two sibling *leaves* `2,3` of `G_g` — a genuine graph automorphism. So
`rename τ P_g = P_g` *exactly*. -/

/-- `τ = (2,3)` is a graph automorphism of the slide `g = [0,0,1,1]`. -/
theorem swap23_aut_g0011 :
    ∀ i : Fin 4, (![0,0,1,1] : Fin 4 → Fin 4) (Equiv.swap 2 3 i)
      = Equiv.swap 2 3 ((![0,0,1,1] : Fin 4 → Fin 4) i) := by decide

/-- Hence `P_g` is invariant under Gnang's transposition — `rename τ P_g = P_g`. -/
theorem rename_Pg_eq_g0011 :
    MvPolynomial.rename (Equiv.swap (2 : Fin 4) 3)
        (fullDeterminantalPolynomial (![0,0,1,1] : Fin 4 → Fin 4))
      = fullDeterminantalPolynomial (![0,0,1,1] : Fin 4 → Fin 4) :=
  rename_fullDet_eq_of_aut _ _ swap23_aut_g0011

end KRR
