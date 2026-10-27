module
/- Nonnegative values at coherent, compatible cyclic local minima. -/
public import Plank.Proofs.Quant.CyclicAnchorRemainder
public import Plank.Proofs.Quant.CyclicEulerPayments

@[expose] public section
noncomputable section

namespace Quant.CyclicAnchorMinimum

open CyclicGapCancellation CyclicVertexDescent CyclicThresholdCaps
  CyclicWeightedThresholdGeometry CyclicPairAreas CyclicAnchorAlgebra CyclicAnchorRemainder

def positiveBeta (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  betaTerm a b c l h (i+1)-direction a b c (i+1)*anchorWidth a b c i*
    max 0 (refundArgument a b c l h i 1)/(direction a b c (i+1)*weight a b c (i+2))

def positiveVertex (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  lowerVertex a b c l i+alphaTerm a b c l h (i+1)-anchorWidth a b c i*
    max 0 (refundArgument a b c l h i 2)/((1-direction a b c i)*weight a b c (i+2))

def negativeAlpha (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  alphaTerm a b c l h i-(1-direction a b c i)*anchorWidth a b c (i+1)*
    max 0 (refundArgument a b c l h i 3)/((1-direction a b c i)*weight a b c (i+2))

def negativeVertex (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  upperVertex a b c h (i+1)+betaTerm a b c l h i-anchorWidth a b c (i+1)*
    max 0 (refundArgument a b c l h i 0)/(direction a b c (i+1)*weight a b c (i+2))

theorem positiveBeta_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) :
    0 ≤ positiveBeta a b c l h i := by
  have hmod : i+1+2 = i := by fin_cases i <;> rfl
  simpa only [positiveBeta,betaTerm,betaCost,hmod] using
    CyclicEulerPayments.positive_beta_payment_nonneg a b c l h ha hb hc hlh hend i
      (anchorWidth a b c i) (anchorWidth_pos ha hb hc i).le

theorem positiveVertex_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i) (hhi : ∀ i, h i ≤ 1)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) :
    0 ≤ positiveVertex a b c l h i :=
  CyclicEulerPayments.positive_vertex_payment_nonneg a b c l h ha hb hc hlh hend i (hhi (i+1))
    (direction a b c i-lowerAnchor a b c i) (alphaCost a b c (i+1)) (anchorWidth a b c i)
    (sub_nonneg.mpr (anchor_bounds ha hb hc i).2.1.le) (alphaCost_pos ha hb hc (i+1)).le
    (sub_pos.mp (positive_vertex_payment_gap_pos ha hb hc i)).le

theorem negativeAlpha_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) :
    0 ≤ negativeAlpha a b c l h i :=
  CyclicEulerPayments.negative_alpha_payment_nonneg a b c l h ha hb hc hlh hend i
    (anchorWidth a b c (i+1)) (anchorWidth_pos ha hb hc (i+1)).le

theorem negativeVertex_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i) (hlo : ∀ i, 0 ≤ l i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) :
    0 ≤ negativeVertex a b c l h i :=
  CyclicEulerPayments.negative_vertex_payment_nonneg a b c l h ha hb hc hlh hend i (hlo i)
    (upperAnchor a b c (i+1)-direction a b c (i+1)) (betaCost a b c i)
    (anchorWidth a b c (i+1)) (sub_nonneg.mpr (anchor_bounds ha hb hc (i+1)).2.2.1.le)
    (betaCost_pos ha hb hc i).le (sub_pos.mp (negative_vertex_payment_gap_pos ha hb hc i)).le

theorem remainder_eq_positive (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hcoh : ∀ i, refundArgument a b c l h i 0 ≤ 0 ∧ refundArgument a b c l h i 3 ≤ 0) :
    remainder a b c l h = (∑ i, upperVertex a b c h i)+
      ∑ i, (positiveBeta a b c l h i+positiveVertex a b c l h i) := by
  have h0 (i : Fin 3) : max 0 (refundArgument a b c l h i 0) = 0 := max_eq_left (hcoh i).1
  have h3 (i : Fin 3) : max 0 (refundArgument a b c l h i 3) = 0 := max_eq_left (hcoh i).2
  simp only [remainder,positiveBeta,positiveVertex,lowRefund,highRefund,h0,h3,
    mul_zero,zero_add,add_zero,Fin.sum_univ_three]
  simp only [show (1 : Fin 3)+1 = 2 from rfl,
    show (2 : Fin 3)+1 = 0 from rfl,
    show (1 : Fin 3)+2 = 0 from rfl,show (2 : Fin 3)+2 = 1 from rfl]
  ring

theorem remainder_eq_negative (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hcoh : ∀ i, refundArgument a b c l h i 1 ≤ 0 ∧ refundArgument a b c l h i 2 ≤ 0) :
    remainder a b c l h = (∑ i, lowerVertex a b c l i)+
      ∑ i, (negativeAlpha a b c l h i+negativeVertex a b c l h i) := by
  have h1 (i : Fin 3) : max 0 (refundArgument a b c l h i 1) = 0 := max_eq_left (hcoh i).1
  have h2 (i : Fin 3) : max 0 (refundArgument a b c l h i 2) = 0 := max_eq_left (hcoh i).2
  simp only [remainder,negativeAlpha,negativeVertex,lowRefund,highRefund,h1,h2,
    mul_zero,zero_add,add_zero,Fin.sum_univ_three]
  simp only [show (1 : Fin 3)+1 = 2 from rfl,
    show (2 : Fin 3)+1 = 0 from rfl,
    show (1 : Fin 3)+2 = 0 from rfl,show (2 : Fin 3)+2 = 1 from rfl]
  ring

theorem remainder_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i) (hlo : ∀ i, 0 ≤ l i) (hhi : ∀ i, h i ≤ 1)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1))
    (hcoh : (∀ i, refundArgument a b c l h i 0 ≤ 0 ∧ refundArgument a b c l h i 3 ≤ 0) ∨
      (∀ i, refundArgument a b c l h i 1 ≤ 0 ∧ refundArgument a b c l h i 2 ≤ 0)) :
    0 ≤ remainder a b c l h := by
  rcases hcoh with hp | hn
  · rw [remainder_eq_positive a b c l h hp]
    apply add_nonneg
    · exact Finset.sum_nonneg (fun i _ => upperVertex_nonneg ha hb hc h i)
    · exact Finset.sum_nonneg (fun i _ => add_nonneg
        (positiveBeta_nonneg a b c l h ha hb hc hlh hend i)
        (positiveVertex_nonneg a b c l h ha hb hc hlh hhi hend i))
  · rw [remainder_eq_negative a b c l h hn]
    apply add_nonneg
    · exact Finset.sum_nonneg (fun i _ => lowerVertex_nonneg ha hb hc l i)
    · exact Finset.sum_nonneg (fun i _ => add_nonneg
        (negativeAlpha_nonneg a b c l h ha hb hc hlh hend i)
        (negativeVertex_nonneg a b c l h ha hb hc hlh hlo hend i))

/-- The full scalar margin has no negative ambient local minimum in either
coherent, physically bounded, strictly compatible box with nonnegative deficit. -/
theorem nonneg_at_localMin (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i) (hlo : ∀ i, 0 ≤ l i) (hhi : ∀ i, h i ≤ 1)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1))
    (hcoh : (∀ i, refundArgument a b c l h i 0 ≤ 0 ∧ refundArgument a b c l h i 3 ≤ 0) ∨
      (∀ i, refundArgument a b c l h i 1 ≤ 0 ∧ refundArgument a b c l h i 2 ≤ 0))
    (hδ : 0 ≤ SixTriangleResidual.deficit l h)
    (hmin : IsLocalMin (CyclicDescentSymmetry.jointMargin a b c) (l,h)) :
    0 ≤ margin a b c l h := by
  rw [localMin_margin_eq ha hb hc l h hmin]
  exact add_nonneg (remainder_nonneg a b c l h ha hb hc hlh hlo hhi hend hcoh)
    (mul_nonneg hδ (SixTriangleAlgebra.imbalance_nonneg ha hb hc))

end Quant.CyclicAnchorMinimum
