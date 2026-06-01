import KRR.GnangPolynomialIdentity
import KRR.PartAInvariance

set_option linter.style.longLine false

/-!
# Source correspondence, final piece: Gnang's three index–blocks reassemble into `P_g`

This file removes the last hand-checked step in matching our objects to the source: that Gnang's
three-block expression for `P_g` (arXiv:2202.03178 v3) equals `fullDeterminantalPolynomial`
of the slide. We prove that `edgeWeightsPolynomial (slide f L)` decomposes as the product of three
blocks indexed by the pair set `{(i,j) : i < j}`, partitioned by sibling membership of the larger
and smaller index, with the slide replaced by `f` resp. `f²` exactly as Gnang writes it:

* **Block 1** `f p.2 ≠ f L` (`j` not a sibling): images `f p.2`, `f p.1`.
* **Block 2** `f p.2 = f L`, `f p.1 ≠ f L` (`j` sibling, `i` not): images `f² p.2`, `f p.1`.
* **Block 3** `f p.2 = f L`, `f p.1 = f L` (both siblings): images `f² p.2`, `f² p.1`.

The only hypothesis is Gnang's WLOG labelling `hlab`: the siblings carry the largest labels, i.e.
if `i` is a sibling and `i < j` then `j` is a sibling. This is exactly what makes the fourth case
(`i` sibling, `j` not) empty, so three blocks suffice — matching Gnang's labeling convention.

Multiplying by the Vandermonde factor turns this into the literal identity `P_g (3-block) = V·W_g`.
-/

open MvPolynomial Finset

namespace KRR

variable {n : ℕ}

/-- The ordered-pair index set `{(i,j) : i < j}`. -/
def pairSet (n : ℕ) : Finset (Fin n × Fin n) :=
  univ.filter (fun p : Fin n × Fin n => p.1.val < p.2.val)

/-- Gnang's binomial pair factor `∏_{t∈{0,1}} (x_{aj} − x_j + (−1)ᵗ (x_{ai} − x_i))`, with `aj`, `ai`
the images of the larger and smaller index. -/
noncomputable def blockFactor (aj ai j i : Fin n) : MvPolynomial (Fin n) ℤ :=
  ∏ t ∈ Finset.range 2,
    ((X aj - X j) + (-1 : MvPolynomial (Fin n) ℤ) ^ t * (X ai - X i))

lemma slide_eq_of_ne {f : Fin n → Fin n} {L i : Fin n} (h : f i ≠ f L) :
    slide f L i = f i := by
  simp only [slide]; rw [if_neg h]

lemma slide_eq_of_eq {f : Fin n → Fin n} {L i : Fin n} (h : f i = f L) :
    slide f L i = f (f i) := by
  simp only [slide]; rw [if_pos h]

/-- `edgeWeightsPolynomial` in single-product-over-pairs form, with each squared difference written
as Gnang's binomial `blockFactor`. -/
lemma edgeWeights_eq_pairs (h : Fin n → Fin n) :
    edgeWeightsPolynomial h = ∏ p ∈ pairSet n, blockFactor (h p.2) (h p.1) p.2 p.1 := by
  have step : edgeWeightsPolynomial h
      = ∏ i : Fin n, ∏ j ∈ univ.filter (fun j : Fin n => i.val < j.val),
          blockFactor (h j) (h i) j i := by
    rw [edgeWeightsPolynomial]
    refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
    rw [blockFactor]; exact (prod_range_two_sign _ _).symm
  rw [step, pairSet]
  exact nested_eq_pairs (fun i j => blockFactor (h j) (h i) j i)

lemma mem_pairSet_order {p : Fin n × Fin n} (hp : p ∈ pairSet n) : p.1.val < p.2.val := by
  simpa [pairSet, Finset.mem_filter] using hp

/-- **Gnang's three-block decomposition of `P_g`.** Under the WLOG labelling `hlab` (siblings carry
the largest labels), `edgeWeightsPolynomial (slide f L)` equals the product of Gnang's three blocks
Times the Vandermonde factor this is the literal `P_g (3-block) = V·W_g`. -/
theorem edgeWeights_slide_three_blocks (f : Fin n → Fin n) (L : Fin n)
    (hlab : ∀ i j : Fin n, f i = f L → i.val < j.val → f j = f L) :
    edgeWeightsPolynomial (slide f L)
      = (∏ p ∈ pairSet n |>.filter (fun p => f p.2 ≠ f L),
            blockFactor (f p.2) (f p.1) p.2 p.1)
        * (∏ p ∈ pairSet n |>.filter (fun p => f p.2 = f L ∧ f p.1 ≠ f L),
            blockFactor (f (f p.2)) (f p.1) p.2 p.1)
        * (∏ p ∈ pairSet n |>.filter (fun p => f p.2 = f L ∧ f p.1 = f L),
            blockFactor (f (f p.2)) (f (f p.1)) p.2 p.1) := by
  set H : Fin n × Fin n → MvPolynomial (Fin n) ℤ :=
    fun p => blockFactor (slide f L p.2) (slide f L p.1) p.2 p.1 with hH
  -- Block 1 : j not a sibling (hence, by hlab, i not a sibling either).
  have hB1 : (∏ p ∈ pairSet n |>.filter (fun p => ¬ (f p.2 = f L)), H p)
      = ∏ p ∈ pairSet n |>.filter (fun p => f p.2 ≠ f L),
          blockFactor (f p.2) (f p.1) p.2 p.1 := by
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    have hord := mem_pairSet_order hp.1
    have h2 : f p.2 ≠ f L := hp.2
    have h1 : f p.1 ≠ f L := fun hh => h2 (hlab p.1 p.2 hh hord)
    rw [hH]; dsimp only; rw [slide_eq_of_ne h2, slide_eq_of_ne h1]
  -- Block 2 : j sibling, i not.
  have hB2 : (∏ p ∈ (pairSet n |>.filter (fun p => f p.2 = f L)).filter (fun p => ¬ (f p.1 = f L)), H p)
      = ∏ p ∈ pairSet n |>.filter (fun p => f p.2 = f L ∧ f p.1 ≠ f L),
          blockFactor (f (f p.2)) (f p.1) p.2 p.1 := by
    rw [Finset.filter_filter]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    obtain ⟨-, h2, h1⟩ := hp
    rw [hH]; dsimp only; rw [slide_eq_of_eq h2, slide_eq_of_ne h1]
  -- Block 3 : both siblings.
  have hB3 : (∏ p ∈ (pairSet n |>.filter (fun p => f p.2 = f L)).filter (fun p => f p.1 = f L), H p)
      = ∏ p ∈ pairSet n |>.filter (fun p => f p.2 = f L ∧ f p.1 = f L),
          blockFactor (f (f p.2)) (f (f p.1)) p.2 p.1 := by
    rw [Finset.filter_filter]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    obtain ⟨-, h2, h1⟩ := hp
    rw [hH]; dsimp only; rw [slide_eq_of_eq h2, slide_eq_of_eq h1]
  -- Assemble: split the pair product twice and rewrite each block.
  rw [edgeWeights_eq_pairs (slide f L), ← hH]
  rw [← Finset.prod_filter_mul_prod_filter_not (pairSet n) (fun p => f p.2 = f L) H]
  rw [← Finset.prod_filter_mul_prod_filter_not (pairSet n |>.filter (fun p => f p.2 = f L))
        (fun p => f p.1 = f L) H]
  rw [hB1, hB2, hB3]
  ring

/-- **`P_g (3-block) = V · W_g`.** The full determinantal polynomial of the slide equals the
Vandermonde factor times Gnang's three-block product — the literal identity behind Step 5's `P_g`. -/
theorem fullDet_slide_three_blocks (f : Fin n → Fin n) (L : Fin n)
    (hlab : ∀ i j : Fin n, f i = f L → i.val < j.val → f j = f L) :
    fullDeterminantalPolynomial (slide f L)
      = vandermonde n
        * ((∏ p ∈ pairSet n |>.filter (fun p => f p.2 ≠ f L),
              blockFactor (f p.2) (f p.1) p.2 p.1)
          * (∏ p ∈ pairSet n |>.filter (fun p => f p.2 = f L ∧ f p.1 ≠ f L),
              blockFactor (f (f p.2)) (f p.1) p.2 p.1)
          * (∏ p ∈ pairSet n |>.filter (fun p => f p.2 = f L ∧ f p.1 = f L),
              blockFactor (f (f p.2)) (f (f p.1)) p.2 p.1)) := by
  rw [fullDeterminantalPolynomial, edgeWeights_slide_three_blocks f L hlab]

end KRR
