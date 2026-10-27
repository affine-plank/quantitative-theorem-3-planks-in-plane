/- An exhaustive actual-area equality criterion in the cyclic region without
vertex or threshold clipping. Extending this to all triangle windows remains
a separate obligation. Every regional hypothesis is an explicit inequality. -/
module

public import Plank.Proofs.Quant.CyclicClippingBudget
public import Plank.Proofs.Quant.SixTriangleEquality
public import Plank.Proofs.Quant.TriangleEqualityReductions

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CyclicUnclippedEquality

open MeasureTheory CyclicWeightedThresholdGeometry CyclicThresholdCaps
  CyclicPairAreas CyclicExactGap CyclicGapCancellation CyclicSixTermCompensation
  CyclicClippingBudget SixTriangleResidual SixTriangleEquality CyclicBadThresholds

/-- A finite list of inequalities specifying the cyclic region in which
neither the outer vertices nor the pure-cell thresholds cause an area loss. -/
structure NoClippingRegion (a b c : ℝ) (l h : Fin 3 → ℝ) : Prop where
  lower_nonneg : ∀ i, 0 ≤ l i
  ordered : ∀ i, l i < h i
  upper_le_one : ∀ i, h i ≤ 1
  compatible_endpoints : ∀ i,
    0 ≤ (1-direction a b c (i+1))*l i - direction a b c i*h (i+1) +
      direction a b c i*direction a b c (i+1)
  middle : ∀ i, l i ≤ direction a b c i ∧ direction a b c i ≤ h i
  weighted : ∀ i,
    weight a b c i*windowWidth l h i ≤ thresholdSlack a b c l ∧
    weight a b c i*windowWidth l h i ≤ -thresholdSlack a b c h

theorem compatible_between {a b c : ℝ} {l h : Fin 3 → ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (H : NoClippingRegion a b c l h) (t : Fin 3 → ℝ)
    (ht : ∀ i, l i ≤ t i ∧ t i ≤ h i) : compatible a b c t := by
  intro i
  have hL := mul_le_mul_of_nonneg_left (ht i).1
    (sub_nonneg.mpr (direction_bounds ha hb hc (i+1)).2.le)
  have hH := mul_le_mul_of_nonneg_left (ht (i+1)).2
    (direction_bounds ha hb hc i).1.le
  linarith only [H.compatible_endpoints i,hL,hH]

theorem separated_thresholds {a b c : ℝ} {l h : Fin 3 → ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (H : NoClippingRegion a b c l h) :
    0 < thresholdSlack a b c l ∧ thresholdSlack a b c h < 0 := by
  have hp : 0 < weight a b c 0*windowWidth l h 0 :=
    mul_pos (weight_pos ha hb hc 0) (sub_pos.mpr (H.ordered 0))
  exact ⟨hp.trans_le (H.weighted 0).1, by linarith only [hp,(H.weighted 0).2]⟩

/-- Exact geometric identification: twice the actual uncovered area is the
six-term expression throughout this region. No Bad seed is assumed. -/
theorem twice_gap_eq_sixArea {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) (H : NoClippingRegion a b c l h) :
    2*(volume (CyclicExteriorAssembly.uncovered a b c l h)).toReal =
      SixTriangleAlgebra.sixArea a b c l h := by
  have hcompat := compatible_between ha hb hc H
  have hl := hcompat l (fun i => ⟨le_rfl,(H.ordered i).le⟩)
  have hh := hcompat h (fun i => ⟨(H.ordered i).le,le_rfl⟩)
  have hq := separated_thresholds ha hb hc H
  have hthreshold := thresholdLoss_eq_zero a b c l h H.weighted
  have hrefund := capRefund_eq_zero_of_thresholdLoss_eq_zero a b c l h ha hb hc
    (fun i => (H.ordered i).le) H.lower_nonneg H.upper_le_one hcompat hq.1.le hq.2.le hthreshold
  calc
    _ = 2*gapExpression a b c l h := by
      rw [uncovered_area_eq_expression a b c l h ha hb hc H.ordered
        H.lower_nonneg H.upper_le_one hcompat hq.1 hq.2]
    _ = normalizedExpression a b c l h :=
      gapExpression_cancellation a b c l h
        (lowerCapSize_nonpos_of_slack_nonneg a b c l ha hb hc hl hq.1.le)
        (capSize_nonpos_of_slack_nonpos a b c h ha hb hc hh hq.2.le)
    _ = _ := by
      rw [normalizedExpression_decomposition,hrefund,
        vertexPenalty_eq_zero a b c l h H.middle,hthreshold]
      ring

/-- Both directions of the geometric equality classification in the
specified region. The right side has one cubic direction equation and six
linear endpoint equations, and contains no area predicate. -/
theorem area_equality_iff {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) (H : NoClippingRegion a b c l h) (hδ : 0 < deficit l h) :
    (volume (CyclicExteriorAssembly.uncovered a b c l h)).toReal = (deficit l h)^2/2 ↔
      CutCalibration a b c l h := by
  have hg := twice_gap_eq_sixArea ha hb hc l h H
  rw [← sixArea_eq_square_iff ha hb hc l h hδ]
  constructor <;> intro he <;> linarith only [hg,he]

/-- The same exhaustive regional criterion for the project's original
three-plank configuration, using its actual relative-width deficit. -/
theorem config_equality_iff (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1))
    (H : NoClippingRegion (1-a) b c (lowerLevels C c) (upperLevels C c))
    (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔
      CutCalibration (1-a) b c (lowerLevels C c) (upperLevels C c) := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hd := deficit_eq_window_deficit C hb ha hc hu₀ hu₁ hu₂
  change C.deficit = deficit (lowerLevels C c) (upperLevels C c) at hd
  have hg : C.gapArea =
      (volume (CyclicExteriorAssembly.uncovered (1-a) b c
        (lowerLevels C c) (upperLevels C c))).toReal := by
    rw [Config.gapArea,CyclicExteriorAssembly.configuration_uncovered C hu₀ hu₁ hu₂]
  rw [TriangleEqualityReductions.Equality,max_eq_right hδ.le,hg,hd]
  have hr := area_equality_iff ha' hb hc (lowerLevels C c) (upperLevels C c) H (hd ▸ hδ)
  simpa only [div_eq_mul_inv,one_mul] using hr

end Quant.CyclicUnclippedEquality

/-- info: 'Quant.CyclicUnclippedEquality.area_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicUnclippedEquality.area_equality_iff
/-- info: 'Quant.CyclicUnclippedEquality.config_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicUnclippedEquality.config_equality_iff
