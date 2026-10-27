module
/-
# Separating the exact cyclic gap into six edge terms and corrections

The known six-term scalar inequality supplies the sharp area bound whenever
the outer-vertex penalties and threshold losses vanish. Directions, widths
and window positions are independent; the remaining general problem is to
pay these losses with the edge-term surplus and cap refunds.
-/
public import Plank.Proofs.Quant.CyclicGapCancellation
public import Plank.Proofs.Quant.SixTriangleAlgebra

@[expose] public section

noncomputable section

namespace Quant.CyclicSixTermCompensation

open CyclicWeightedThresholdGeometry CyclicThresholdCaps CyclicGapCancellation
  CyclicPairAreas CyclicBadThresholds

def vertexPenalty (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  ∑ i, (squarePos (l i-direction a b c i)+squarePos (direction a b c i-h i)) /
    (direction a b c i*(1-direction a b c i))

def capRefund (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  (∑ i, (squarePos (-lowPairSlack a b c l i-windowWidth l h (i+1)) +
    squarePos (-lowPairSlack a b c l i-direction a b c (i+1)*windowWidth l h i)) /
      (direction a b c (i+1)*weight a b c (i+2))) +
  (∑ i, (squarePos (-highPairSlack a b c h i-windowWidth l h i) +
    squarePos (-highPairSlack a b c h i-(1-direction a b c i)*windowWidth l h (i+1))) /
      ((1-direction a b c i)*weight a b c (i+2)))

theorem normalizedExpression_decomposition (a b c : ℝ) (l h : Fin 3 → ℝ) :
    normalizedExpression a b c l h = SixTriangleAlgebra.sixArea a b c l h +
      capRefund a b c l h-vertexPenalty a b c l h-thresholdLoss a b c l h := by
  simp only [normalizedExpression, SixTriangleAlgebra.sixArea, capRefund,
    vertexPenalty, Fin.sum_univ_three]
  dsimp [squarePos, lowPairSlack, highPairSlack, capSize, lowerCapSize,
    direction, weight, SixTriangleAlgebra.lowCut, SixTriangleAlgebra.highCut,
    SixTriangleAlgebra.lowDenom, SixTriangleAlgebra.highDenom, SixTriangleAlgebra.dets,
    k0, k1, k2]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring_nf

theorem capRefund_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    0 ≤ capRefund a b c l h := by
  apply add_nonneg <;> apply Finset.sum_nonneg <;> intro i _
  · exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_pos (direction_bounds ha hb hc (i+1)).1 (weight_pos ha hb hc (i+2))).le
  · exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_pos (sub_pos.mpr (direction_bounds ha hb hc i).2) (weight_pos ha hb hc (i+2))).le

theorem vertexPenalty_eq_zero (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hwindow : ∀ i, l i ≤ direction a b c i ∧ direction a b c i ≤ h i) :
    vertexPenalty a b c l h = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [squarePos,max_eq_left (sub_nonpos.mpr (hwindow i).1),
    max_eq_left (sub_nonpos.mpr (hwindow i).2),zero_pow (by decide : 2 ≠ 0),
    zero_add,zero_div]

theorem thresholdLoss_eq_zero (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hweighted : ∀ i, weight a b c i*windowWidth l h i ≤ thresholdSlack a b c l ∧
      weight a b c i*windowWidth l h i ≤ -thresholdSlack a b c h) :
    thresholdLoss a b c l h = 0 := by
  have he (i : Fin 3) : squarePos (weight a b c i*windowWidth l h i-thresholdSlack a b c l) +
      squarePos (weight a b c i*windowWidth l h i+thresholdSlack a b c h) = 0 := by
    have hh : weight a b c i*windowWidth l h i+thresholdSlack a b c h ≤ 0 := by
      linarith [(hweighted i).2]
    simp only [squarePos,max_eq_left (sub_nonpos.mpr (hweighted i).1),max_eq_left hh,
      zero_pow (by decide : 2 ≠ 0),zero_add]
  simp only [thresholdLoss,he,Finset.sum_const_zero,zero_div]

/-- A general loss budget: the six-term lower bound keeps all cap refunds. -/
theorem positive_part_with_losses (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    (max 0 (1-((h 0-l 0)+(h 1-l 1)+(h 2-l 2))))^2 + capRefund a b c l h ≤
      normalizedExpression a b c l h+vertexPenalty a b c l h+thresholdLoss a b c l h := by
  have hs := SixTriangleAlgebra.positive_part_bound ha hb hc l h
  rw [normalizedExpression_decomposition]
  linarith only [hs]

/-- The full scalar bound on the chamber with no outer-vertex or threshold losses. -/
theorem positive_part_of_no_losses (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hwindow : ∀ i, l i ≤ direction a b c i ∧ direction a b c i ≤ h i)
    (hweighted : ∀ i, weight a b c i*windowWidth l h i ≤ thresholdSlack a b c l ∧
      weight a b c i*windowWidth l h i ≤ -thresholdSlack a b c h) :
    (max 0 (1-((h 0-l 0)+(h 1-l 1)+(h 2-l 2))))^2 ≤ normalizedExpression a b c l h := by
  have hs := positive_part_with_losses a b c l h ha hb hc
  rw [vertexPenalty_eq_zero a b c l h hwindow, thresholdLoss_eq_zero a b c l h hweighted,
    add_zero,add_zero] at hs
  linarith only [hs,capRefund_nonneg a b c l h ha hb hc]

theorem deficit_eq_window_deficit (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) :
    C.deficit = 1-((upperLevels C c 0-lowerLevels C c 0)+
      (upperLevels C c 1-lowerLevels C c 1)+(upperLevels C c 2-lowerLevels C c 2)) := by
  rw [CyclicArea.deficit_eq C hb ha hc hu₀ hu₁ hu₂]
  dsimp [OrdinalArea.widths,lowerLevels,upperLevels]
  ring

/-- A sharp actual-area theorem with independent directions, widths and positions.
Every plank contains its middle vertex level and the six threshold losses vanish. -/
theorem sqPos_of_no_losses (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1))
    (hwindow : ∀ i, lowerLevels C c i ≤ direction (1-a) b c i ∧
      direction (1-a) b c i ≤ upperLevels C c i)
    (hweighted : ∀ i,
      weight (1-a) b c i*windowWidth (lowerLevels C c) (upperLevels C c) i ≤
        thresholdSlack (1-a) b c (lowerLevels C c) ∧
      weight (1-a) b c i*windowWidth (lowerLevels C c) (upperLevels C c) i ≤
        -thresholdSlack (1-a) b c (upperLevels C c)) : Quant.SqPos C := by
  apply (sqPos_iff_obstructed_scalar C hb ha hc hu₀ hu₁ hu₂).mpr
  intro z _ _
  have ha' : 0 < 1-a ∧ 1-a < 1 := by constructor <;> linarith [ha.1,ha.2]
  dsimp [squarePos]
  rw [deficit_eq_window_deficit C hb ha hc hu₀ hu₁ hu₂]
  exact positive_part_of_no_losses (1-a) b c _ _ ha' hb hc hwindow hweighted

end Quant.CyclicSixTermCompensation
