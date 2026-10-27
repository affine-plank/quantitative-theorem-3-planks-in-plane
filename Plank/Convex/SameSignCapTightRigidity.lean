/- Equality and quantitative rigidity for three positive contact budgets.
The algebra is independent of the ambient geometry; the cycle-gap hypothesis
must be supplied separately (for example by the planar contact theorem). -/
module
public import Plank.Convex.SameSignCapProduct
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Plank.Convex.SameSignCapAlgebra Plank.Convex.SameSignCapTransfer
open Plank.Convex.SameSignCapProduct
namespace Plank.Convex.SameSignCapTightRigidity

/-- Budgets at least one bound their product excess by the total width slack. -/
theorem excess_le_width_slack (w d : Point) (hw : ∀ i, 0 ≤ w i)
    (hd : ∀ i, 1 ≤ d i) :
    (∑ i, w i * d (next i) * d (prev i)) - (∏ i, d i) ≤
      ((∑ i, w i) - 1) * (∏ i, d i) := by
  have hp (i : Fin 3) : d (next i) * d (prev i) ≤ ∏ j, d j := by
    have hm := mul_le_mul_of_nonneg_right (hd i)
      (mul_nonneg (zero_le_one.trans (hd (next i))) (zero_le_one.trans (hd (prev i))))
    have he : d i * (d (next i) * d (prev i)) = ∏ j, d j := by
      fin_cases i <;> simp [next, prev, Fin.prod_univ_three] <;> ring
    simpa only [one_mul, he] using hm
  have hs : (∑ i, w i * d (next i) * d (prev i)) ≤
      (∑ i, w i) * (∏ i, d i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hp i) (hw i)
  nlinarith only [hs]

/-- The positive weight of an opposite transfer pair in the budget identity. -/
def pairWeight (w f r : Point) (i : Fin 3) : ℝ :=
  f (prev i) * (w i) ^ 2 * w (next i) +
    r (prev i) * w i * (w (next i)) ^ 2

/-- Each nonnegative pair term is controlled by the excess of total width over one. -/
theorem pair_slack_bound (w f r : Point)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (next i) ≤ 1)
    (hcycle : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hbudget : ∀ i, 1 ≤ budget w f r i) (i : Fin 3) :
    (1 - f i * r (next i)) * pairWeight w f r i ≤
      ((∑ j, w j) - 1) * (∏ j, budget w f r j) := by
  have ht (j : Fin 3) : 0 ≤ (1 - f j * r (next j)) * pairWeight w f r j := by
    apply mul_nonneg (sub_nonneg.mpr (hpair j))
    exact add_nonneg
      (mul_nonneg (mul_nonneg (hf _) (sq_nonneg _)) (hw _))
      (mul_nonneg (mul_nonneg (hr _) (hw _)) (sq_nonneg _))
  have hc : 0 ≤ (2 - (∏ j, f j) - (∏ j, r j)) * (∏ j, w j) :=
    mul_nonneg (by linarith only [hcycle]) (Finset.prod_nonneg fun j _ => hw j)
  have hi := Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)
  have he := budget_identity w f r
  change _ = (∑ j, (1 - f j * r (next j)) * pairWeight w f r j) + _ at he
  have hs := excess_le_width_slack w (budget w f r) hw hbudget
  linarith only [hi, hc, he, hs]

/-- Positive widths at equality force every opposite pair of transfers to be reciprocal. -/
theorem pair_eq_one_of_tight (w f r : Point)
    (hw : ∀ i, 0 < w i) (hf : ∀ i, 0 < f i) (hr : ∀ i, 0 ≤ r i)
    (hpair : ∀ i, f i * r (next i) ≤ 1)
    (hcycle : (∏ i, f i) + (∏ i, r i) ≤ 2)
    (hbudget : ∀ i, 1 ≤ budget w f r i) (htight : (∑ i, w i) = 1)
    (i : Fin 3) : f i * r (next i) = 1 := by
  have hs := pair_slack_bound w f r (fun j => (hw j).le) (fun j => (hf j).le)
    hr hpair hcycle hbudget i
  rw [htight, sub_self, zero_mul] at hs
  have hq : 0 < pairWeight w f r i :=
    add_pos_of_pos_of_nonneg
      (mul_pos (mul_pos (hf _) (sq_pos_of_pos (hw i))) (hw _))
      (mul_nonneg (mul_nonneg (hr _) (hw _).le) (sq_nonneg _))
  nlinarith only [hs, hq, hpair i]

def pairDen (a b : Point) (i : Fin 3) : ℝ :=
  lowerDen a b i * upperDen a b i * lowerDen a b (next i) * upperDen a b (next i)

theorem pairDen_pos (a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 3) : 0 < pairDen a b i :=
  mul_pos (mul_pos (mul_pos (lowerDen_pos a b ha hb i) (upperDen_pos a b ha hb i))
    (lowerDen_pos a b ha hb _)) (upperDen_pos a b ha hb _)

/-- Every opposite pair has the same squared slope-product defect, with a positive denominator. -/
theorem transfer_pair_gap (a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 3) :
    1 - forward a b i * reverse a b (next i) =
      (slopeProduct a b - 1) ^ 2 / pairDen a b i := by
  have hg := pair_gap (b i) (a i) (a (next i) * b (prev i))
    (b (next i) * a (prev i)) (hb i) (ha i)
    (mul_pos (ha _) (hb _)) (mul_pos (hb _) (ha _))
  convert hg using 1 <;>
    simp only [forward, reverse, lowerDen, upperDen, pairDen, slopeProduct,
      next_next, prev_next, Fin.prod_univ_three]
  · ring
  · fin_cases i <;> simp [next, prev] <;> ring

/-- Under the nonnegative cycle-gap criterion, width slack controls squared slope imbalance. -/
theorem slope_square_slack_bound (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (hw : ∀ i, lo i ≤ hi i)
    (hgap : 0 ≤ cycleGap a b) (i : Fin 3) :
    ((slopeProduct a b - 1) ^ 2 / pairDen a b i) *
        pairWeight (fun j => hi j - lo j) (forward a b) (reverse a b) i ≤
      ((∑ j, (hi j - lo j)) - 1) *
        (∏ j, budget (fun k => hi k - lo k) (forward a b) (reverse a b) j) := by
  have hf (i : Fin 3) : 0 < forward a b i :=
    add_pos (div_pos (hb i) (lowerDen_pos a b ha hb i))
      (div_pos (ha i) (upperDen_pos a b ha hb i))
  have hr (i : Fin 3) : 0 ≤ reverse a b i :=
    add_nonneg
      (div_nonneg (mul_pos (hb i) (ha _)).le (lowerDen_pos a b ha hb i).le)
      (div_nonneg (mul_pos (ha i) (hb _)).le (upperDen_pos a b ha hb i).le)
  have hc : (∏ i, forward a b i) + (∏ i, reverse a b i) ≤ 2 := by
    have hn : 0 ≤ 2 - (∏ i, forward a b i) - (∏ i, reverse a b i) := by
      rw [cycle_product_gap a b ha hb]
      exact div_nonneg (mul_nonneg (sq_nonneg _) hgap) (denProduct_pos a b ha hb).le
    linarith only [hn]
  have hs := pair_slack_bound (fun j => hi j - lo j) (forward a b) (reverse a b)
    (fun j => sub_nonneg.mpr (hw j)) (fun j => (hf j).le) hr
    (pair_le_one a b ha hb) hc (transfer_bound lo hi a b ha hb hrows) i
  rwa [transfer_pair_gap a b ha hb i] at hs

/-- Tight positive-width contact data with nonnegative cycle gap have balanced slope product. -/
theorem slopeProduct_eq_one_of_tight (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (hw : ∀ i, lo i < hi i)
    (hgap : 0 ≤ cycleGap a b) (htight : (∑ i, (hi i - lo i)) = 1) :
    slopeProduct a b = 1 := by
  have hf (i : Fin 3) : 0 < forward a b i :=
    add_pos (div_pos (hb i) (lowerDen_pos a b ha hb i))
      (div_pos (ha i) (upperDen_pos a b ha hb i))
  have hr (i : Fin 3) : 0 ≤ reverse a b i :=
    add_nonneg
      (div_nonneg (mul_pos (hb i) (ha _)).le (lowerDen_pos a b ha hb i).le)
      (div_nonneg (mul_pos (ha i) (hb _)).le (upperDen_pos a b ha hb i).le)
  have hc : (∏ i, forward a b i) + (∏ i, reverse a b i) ≤ 2 := by
    have hn : 0 ≤ 2 - (∏ i, forward a b i) - (∏ i, reverse a b i) := by
      rw [cycle_product_gap a b ha hb]
      exact div_nonneg (mul_nonneg (sq_nonneg _) hgap) (denProduct_pos a b ha hb).le
    linarith only [hn]
  have hp := pair_eq_one_of_tight (fun i => hi i - lo i) (forward a b) (reverse a b)
    (fun i => sub_pos.mpr (hw i)) hf hr (pair_le_one a b ha hb) hc
    (transfer_bound lo hi a b ha hb hrows) htight 0
  have hg := transfer_pair_gap a b ha hb 0
  rw [hp, sub_self] at hg
  have hz := (div_eq_zero_iff).mp hg.symm
  have hs := hz.resolve_right (pairDen_pos a b ha hb 0).ne'
  nlinarith only [hs]

end Plank.Convex.SameSignCapTightRigidity
/-- info: 'Plank.Convex.SameSignCapTightRigidity.excess_le_width_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTightRigidity.excess_le_width_slack

/-- info: 'Plank.Convex.SameSignCapTightRigidity.pair_slack_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTightRigidity.pair_slack_bound

/-- info: 'Plank.Convex.SameSignCapTightRigidity.pair_eq_one_of_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTightRigidity.pair_eq_one_of_tight

/-- info: 'Plank.Convex.SameSignCapTightRigidity.transfer_pair_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTightRigidity.transfer_pair_gap

/-- info: 'Plank.Convex.SameSignCapTightRigidity.slope_square_slack_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTightRigidity.slope_square_slack_bound

/-- info: 'Plank.Convex.SameSignCapTightRigidity.slopeProduct_eq_one_of_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTightRigidity.slopeProduct_eq_one_of_tight
