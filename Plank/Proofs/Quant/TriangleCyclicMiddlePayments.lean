/- Middle containment permits both surviving refund payments simultaneously. -/
module
public import Plank.Proofs.Quant.TriangleCyclicCalibrations
public import Plank.Proofs.Quant.CyclicCevianFamily

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicMiddlePayments
open CyclicThresholdCaps CyclicWeightedThresholdGeometry CyclicPairAreas
open CyclicGapCancellation CyclicVertexDescent CyclicAnchorAlgebra
open CyclicAnchorRemainder CyclicAnchorMinimum CyclicEqualityObstruction
open CyclicGapMinimizer

theorem remainder_eq_mixed (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlo : ∀ i, 0 ≤ l i) (hhi : ∀ i, h i ≤ 1)
    (hm : ∀ i, l i ≤ direction a b c i ∧ direction a b c i ≤ h i) :
    remainder a b c l h = ∑ i, (positiveBeta a b c l h i+negativeAlpha a b c l h i) := by
  have hvL (i : Fin 3) : lowerVertex a b c l i=0 := by
    simp only [lowerVertex,max_eq_left (sub_nonpos.mpr (hm i).1),mul_zero,zero_div]
  have hvH (i : Fin 3) : upperVertex a b c h i=0 := by
    simp only [upperVertex,max_eq_left (sub_nonpos.mpr (hm i).2),mul_zero,zero_div]
  have h0 (i : Fin 3) : max 0 (refundArgument a b c l h i 0)=0 :=
    max_eq_left ((CyclicEulerPayments.refund_zero_le_upper_vertex a b c l h
      ha hb hc i (hlo i)).trans (sub_nonpos.mpr (hm (i+1)).2))
  have h2 (i : Fin 3) : max 0 (refundArgument a b c l h i 2)=0 :=
    max_eq_left ((CyclicEulerPayments.refund_two_le_lower_vertex a b c l h
      ha hb hc i (hhi (i+1))).trans (sub_nonpos.mpr (hm i).1))
  simp only [remainder,positiveBeta,negativeAlpha,lowRefund,highRefund,hvL,hvH,h0,h2,
    zero_add,add_zero,mul_zero,Fin.sum_univ_three]
  simp only [show (1 : Fin 3)+1=2 from rfl,show (2 : Fin 3)+1=0 from rfl]
  ring

private theorem positive_part_strict {w d x y : ℝ} (_hw : 0 < w) (hd : 0 < d)
    (h : w*x < d*y) (hy : 0 < y) : w*max 0 x < d*max 0 y := by
  rw [max_eq_right hy.le]
  by_cases hx : x ≤ 0
  · rw [max_eq_left hx,mul_zero]
    exact mul_pos hd hy
  · simpa only [max_eq_right (le_of_not_ge hx)] using h

theorem positiveBeta_pos (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3)
    (hloss : 0 < weight a b c (i+1)*windowWidth l h (i+1)+thresholdSlack a b c h) :
    0 < positiveBeta a b c l h i := by
  have hi := weight_pos ha hb hc i
  have hj := weight_pos ha hb hc (i+1)
  have hk := weight_pos ha hb hc (i+2)
  have hd := (direction_bounds ha hb hc (i+1)).1
  have hR := anchorWidth_pos ha hb hc i
  have hh := positive_part_strict hi hd
    (CyclicEulerPayments.refund_weighted_bounds a b c l h ha hb hc hlh hend i).2.1 hloss
  have hn := div_pos (mul_pos hR (sub_pos.mpr hh)) (mul_pos hi hk)
  have hmod : i+1+2=i := by fin_cases i <;> rfl
  dsimp only [positiveBeta,betaTerm,betaCost]
  rw [hmod,← CyclicEulerPayments.weight_cyclic_product a b c i]
  convert hn using 1 <;> first | rfl | field_simp [hi.ne',hj.ne',hk.ne',hd.ne']

theorem negativeAlpha_pos (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3)
    (hloss : 0 < weight a b c i*windowWidth l h i-thresholdSlack a b c l) :
    0 < negativeAlpha a b c l h i := by
  have hi := weight_pos ha hb hc i
  have hj := weight_pos ha hb hc (i+1)
  have hk := weight_pos ha hb hc (i+2)
  have hd := sub_pos.mpr (direction_bounds ha hb hc i).2
  have hR := anchorWidth_pos ha hb hc (i+1)
  have hh := positive_part_strict hj hd
    (CyclicEulerPayments.refund_weighted_bounds a b c l h ha hb hc hlh hend i).2.2.2 hloss
  have hn := div_pos (mul_pos hR (sub_pos.mpr hh)) (mul_pos hj hk)
  dsimp only [negativeAlpha,alphaTerm,alphaCost]
  rw [← CyclicEulerPayments.weight_cyclic_product a b c i]
  convert hn using 1 <;> first | rfl | field_simp [hi.ne',hj.ne',hk.ne',hd.ne']

/-- In the separated region, middle containment alone replaces the former
coherent-refund premise. Equality forces every weighted threshold loss to vanish. -/
theorem weighted_of_separated_equality {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (p : Levels) (H : StrictRegion a b c p)
    (hm : ∀ i, p.1 i ≤ direction a b c i ∧ direction a b c i ≤ p.2 i)
    (he : actualMargin a b c p=0) :
    ∀ i, weight a b c i*windowWidth p.1 p.2 i ≤ thresholdSlack a b c p.1 ∧
      weight a b c i*windowWidth p.1 p.2 i ≤ -thresholdSlack a b c p.2 := by
  have horder := fun i => (H.physical i).2.1.le
  have hB (i : Fin 3) := positiveBeta_nonneg a b c p.1 p.2 ha hb hc
    horder H.compatible_endpoints i
  have hA (i : Fin 3) := negativeAlpha_nonneg a b c p.1 p.2 ha hb hc
    horder H.compatible_endpoints i
  have hr := remainder_eq_mixed a b c p.1 p.2 ha hb hc
    (fun i => (H.physical i).1.le) (fun i => (H.physical i).2.2.le) hm
  have hn : 0 ≤ remainder a b c p.1 p.2 := by
    rw [hr]
    exact Finset.sum_nonneg (fun i _ => add_nonneg (hB i) (hA i))
  have hmin := scalar_isLocalMin_of_equality ha hb hc p H he
  have hid := localMin_margin_eq ha hb hc p.1 p.2 hmin
  have hactual := actualMargin_eq_scalar ha hb hc p H
  change actualMargin a b c p=margin a b c p.1 p.2 at hactual
  have hz : remainder a b c p.1 p.2=0 := by
    have hI := mul_nonneg H.deficit_pos.le (SixTriangleAlgebra.imbalance_nonneg ha hb hc)
    linarith only [hn,hid,hactual,he,hI]
  rw [hr] at hz
  have hsum (i : Fin 3) : positiveBeta a b c p.1 p.2 i+negativeAlpha a b c p.1 p.2 i ≤ 0 := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      add_nonneg (hB j) (hA j)) (Finset.mem_univ i)
    rwa [hz] at hi
  intro i
  constructor
  · by_contra hh
    have hp := negativeAlpha_pos a b c p.1 p.2 ha hb hc horder
      H.compatible_endpoints i (sub_pos.mpr (lt_of_not_ge hh))
    linarith only [hsum i,hB i,hp]
  · by_contra hh
    have hmod : i+2+1=i := by fin_cases i <;> rfl
    have hloss : 0 < weight a b c (i+2+1)*windowWidth p.1 p.2 (i+2+1)+thresholdSlack a b c p.2 := by
      rw [hmod]
      linarith only [lt_of_not_ge hh]
    have hp := positiveBeta_pos a b c p.1 p.2 ha hb hc horder
      H.compatible_endpoints (i+2) hloss
    linarith only [hsum (i+2),hA (i+2),hp]

theorem noClipping_of_separated_equality {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (p : Levels) (H : StrictRegion a b c p)
    (hm : ∀ i, p.1 i ≤ direction a b c i ∧ direction a b c i ≤ p.2 i)
    (he : actualMargin a b c p=0) : CyclicUnclippedEquality.NoClippingRegion a b c p.1 p.2 :=
  ⟨fun i => (H.physical i).1.le,fun i => (H.physical i).2.1,
    fun i => (H.physical i).2.2.le,fun i => (H.compatible_endpoints i).le,hm,
    weighted_of_separated_equality ha hb hc p H hm he⟩

end Quant.TriangleCyclicMiddlePayments

/-- info: 'Quant.TriangleCyclicMiddlePayments.noClipping_of_separated_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicMiddlePayments.noClipping_of_separated_equality
