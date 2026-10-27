module
/-
# The exact clipping budget for the sharp triangle bound

The threshold loss minus cap refunds is twice the total area of the six
clipped correction cells. The desired scalar lower bound is equivalent to
paying that area and the vertex penalties from the six-term surplus.
The budget inequality itself is not assumed to be proved here.
-/
public import Plank.Proofs.Quant.CyclicSixTermCompensation
public import Plank.Proofs.Quant.SixTriangleResidual

@[expose] public section

noncomputable section

namespace Quant.CyclicClippingBudget

open MeasureTheory CyclicWeightedThresholdGeometry CyclicThresholdCaps
  CyclicPairAreas CyclicBadThresholds CyclicExactGap CyclicGapCancellation
  CyclicSixTermCompensation SixTriangleResidual

def clippedLoss (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  thresholdLoss a b c l h-capRefund a b c l h

def surplus (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  2*deficit l h*SixTriangleAlgebra.imbalance a b c+
    (deficit l h)^2*(SixTriangleAlgebra.imbalance a b c)^2+
    sixResidual a b c l h (deficit l h)

theorem normalizedExpression_eq_budget (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    normalizedExpression a b c l h = (deficit l h)^2+surplus a b c l h-
      vertexPenalty a b c l h-clippedLoss a b c l h := by
  rw [normalizedExpression_decomposition, sixArea_eq_baseline_add_residual ha hb hc]
  dsimp [surplus,clippedLoss]
  ring

theorem square_bound_iff_budget (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    (deficit l h)^2 ≤ normalizedExpression a b c l h ↔
      vertexPenalty a b c l h+clippedLoss a b c l h ≤ surplus a b c l h := by
  rw [normalizedExpression_eq_budget a b c l h ha hb hc]
  constructor <;> intro hs <;> linarith only [hs]

theorem surplus_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hδ : 0 ≤ deficit l h) : 0 ≤ surplus a b c l h := by
  have hI := SixTriangleAlgebra.imbalance_nonneg ha hb hc
  have hR := sixResidual_nonneg ha hb hc l h hδ
  dsimp [surplus]
  positivity

theorem raw_pair_sum_eq (a b c : ℝ) (l h : Fin 3 → ℝ) :
    2*((∑ i, lowPairArea a b c l i)+(∑ i, highPairArea a b c h i)) =
      SixTriangleAlgebra.sixArea a b c l h-vertexPenalty a b c l h := by
  simp only [lowPairArea, highPairArea, SixTriangleAlgebra.sixArea,
    vertexPenalty, Fin.sum_univ_three]
  dsimp [squarePos,capSize,lowerCapSize,direction,weight,
    SixTriangleAlgebra.lowCut,SixTriangleAlgebra.highCut,
    SixTriangleAlgebra.lowDenom,SixTriangleAlgebra.highDenom,SixTriangleAlgebra.dets,
    k0,k1,k2]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring_nf

/-- The cap refunds belong to the correction cells; they are not free extra area. -/
theorem clippedLoss_eq_thresholdAreas (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hl : ∀ i, lowerCapSize a b c l i ≤ 0)
    (hh : ∀ i, capSize a b c h i ≤ 0) :
    clippedLoss a b c l h = 2*((∑ i, lowerThresholdArea a b c
      (CyclicExteriorAssembly.lowerCorrectionLevels l h i))+
      ∑ i, upperThresholdArea a b c (CyclicExteriorAssembly.upperCorrectionLevels l h i)) := by
  have he := gapExpression_cancellation a b c l h hl hh
  rw [normalizedExpression_decomposition] at he
  have hp := raw_pair_sum_eq a b c l h
  dsimp [gapExpression] at he
  dsimp [clippedLoss]
  linarith only [he,hp]

theorem clippedLoss_eq_volume (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i) (hlo : ∀ i, 0 ≤ l i) (hhi : ∀ i, h i ≤ 1)
    (hwindow : ∀ t : Fin 3 → ℝ, (∀ i, l i ≤ t i ∧ t i ≤ h i) → compatible a b c t)
    (hql : 0 ≤ thresholdSlack a b c l) (hqh : thresholdSlack a b c h ≤ 0) :
    clippedLoss a b c l h = 2*((∑ i, (volume (lowerCell a b c
      (CyclicExteriorAssembly.lowerCorrectionLevels l h i))).toReal)+
      ∑ i, (volume (upperCell a b c
        (CyclicExteriorAssembly.upperCorrectionLevels l h i))).toReal) := by
  have hl := hwindow l (fun i => ⟨le_rfl,hlh i⟩)
  have hh := hwindow h (fun i => ⟨hlh i,le_rfl⟩)
  rw [clippedLoss_eq_thresholdAreas a b c l h
    (lowerCapSize_nonpos_of_slack_nonneg a b c l ha hb hc hl hql)
    (capSize_nonpos_of_slack_nonpos a b c h ha hb hc hh hqh)]
  have hcorlo (i : Fin 3) : (volume (lowerCell a b c
      (CyclicExteriorAssembly.lowerCorrectionLevels l h i))).toReal =
      lowerThresholdArea a b c (CyclicExteriorAssembly.lowerCorrectionLevels l h i) := by
    have ht := lowerCorrectionLevels_between l h hlh i
    exact volume_lowerCell_toReal a b c _ ha hb hc (fun j => (ht j).2.trans (hhi j))
      (hwindow _ ht)
  have hcorhi (i : Fin 3) : (volume (upperCell a b c
      (CyclicExteriorAssembly.upperCorrectionLevels l h i))).toReal =
      upperThresholdArea a b c (CyclicExteriorAssembly.upperCorrectionLevels l h i) := by
    have ht := upperCorrectionLevels_between l h hlh i
    exact volume_upperCell_toReal a b c _ ha hb hc (fun j => (hlo j).trans (ht j).1)
      (hwindow _ ht)
  simp_rw [hcorlo,hcorhi]

theorem clippedLoss_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i) (hlo : ∀ i, 0 ≤ l i) (hhi : ∀ i, h i ≤ 1)
    (hwindow : ∀ t : Fin 3 → ℝ, (∀ i, l i ≤ t i ∧ t i ≤ h i) → compatible a b c t)
    (hql : 0 ≤ thresholdSlack a b c l) (hqh : thresholdSlack a b c h ≤ 0) :
    0 ≤ clippedLoss a b c l h := by
  rw [clippedLoss_eq_volume a b c l h ha hb hc hlh hlo hhi hwindow hql hqh]
  positivity

theorem capRefund_eq_zero_of_thresholdLoss_eq_zero (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i) (hlo : ∀ i, 0 ≤ l i) (hhi : ∀ i, h i ≤ 1)
    (hwindow : ∀ t : Fin 3 → ℝ, (∀ i, l i ≤ t i ∧ t i ≤ h i) → compatible a b c t)
    (hql : 0 ≤ thresholdSlack a b c l) (hqh : thresholdSlack a b c h ≤ 0)
    (hzero : thresholdLoss a b c l h = 0) : capRefund a b c l h = 0 := by
  have hclip := clippedLoss_nonneg a b c l h ha hb hc hlh hlo hhi hwindow hql hqh
  have hr := capRefund_nonneg a b c l h ha hb hc
  dsimp [clippedLoss] at hclip
  linarith only [hclip,hr,hzero]

/-- The remaining exact inequality, without geometric side conditions beyond Bad. -/
theorem sqPos_iff_obstructed_budget (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) :
    Quant.SqPos C ↔ ∀ z ∈ RowDeletion.triangle C.deficit,
      z ∈ CyclicArea.badSeeds C b a c →
      vertexPenalty (1-a) b c (lowerLevels C c) (upperLevels C c)+
        clippedLoss (1-a) b c (lowerLevels C c) (upperLevels C c) ≤
        surplus (1-a) b c (lowerLevels C c) (upperLevels C c) := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := by constructor <;> linarith [ha.1,ha.2]
  have hδ := deficit_eq_window_deficit C hb ha hc hu₀ hu₁ hu₂
  change C.deficit = deficit (lowerLevels C c) (upperLevels C c) at hδ
  rw [sqPos_iff_obstructed_scalar C hb ha hc hu₀ hu₁ hu₂]
  apply forall_congr'
  intro z
  apply forall_congr'
  intro hz
  have hz' : 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1+z.2 ≤ C.deficit := hz
  have hd : 0 ≤ C.deficit := by linarith only [hz'.1,hz'.2.1,hz'.2.2]
  dsimp only [squarePos]
  rw [max_eq_right hd,hδ,square_bound_iff_budget (1-a) b c _ _ ha' hb hc]

end Quant.CyclicClippingBudget
