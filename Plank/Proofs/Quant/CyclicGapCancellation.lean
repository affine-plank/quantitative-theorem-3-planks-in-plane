module
/-
# Cancellation of the exact clipped cyclic gap expression

The double sums of cap refunds reduce to six three-term positive-part
expressions, three vertex penalties and one weighted threshold loss.
This is an exact scalar identity; no sharp lower bound is asserted.
-/
public import Plank.Proofs.Quant.CyclicExactGap

@[expose] public section

noncomputable section

namespace Quant.CyclicGapCancellation

open CyclicWeightedThresholdGeometry CyclicThresholdCaps CyclicPairAreas
  CyclicExactGap CyclicExteriorAssembly

def squarePos (x : ℝ) : ℝ := (max 0 x)^2
def windowWidth (l h : Fin 3 → ℝ) (i : Fin 3) : ℝ := h i-l i
def lowPairSlack (a b c : ℝ) (l : Fin 3 → ℝ) (i : Fin 3) : ℝ := -capSize a b c l i
def highPairSlack (a b c : ℝ) (h : Fin 3 → ℝ) (i : Fin 3) : ℝ := -lowerCapSize a b c h i

def thresholdLoss (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  (∑ i, (squarePos (weight a b c i*windowWidth l h i-thresholdSlack a b c l) +
    squarePos (weight a b c i*windowWidth l h i+thresholdSlack a b c h))) /
      (k0 b c*k1 a c*k2 a b)

/-- Twice the actual area, expressed without nested cap-refund sums. -/
def normalizedExpression (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  (∑ i, (squarePos (lowPairSlack a b c l i) +
    squarePos (-lowPairSlack a b c l i-windowWidth l h (i+1)) +
    squarePos (-lowPairSlack a b c l i-direction a b c (i+1)*windowWidth l h i)) /
      (direction a b c (i+1)*weight a b c (i+2))) +
  (∑ i, (squarePos (highPairSlack a b c h i) +
    squarePos (-highPairSlack a b c h i-windowWidth l h i) +
    squarePos (-highPairSlack a b c h i-(1-direction a b c i)*windowWidth l h (i+1))) /
      ((1-direction a b c i)*weight a b c (i+2))) -
  (∑ i, (squarePos (l i-direction a b c i)+squarePos (direction a b c i-h i)) /
      (direction a b c i*(1-direction a b c i))) - thresholdLoss a b c l h

theorem thresholdSlack_lowerCorrection (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    thresholdSlack a b c (lowerCorrectionLevels l h i) =
      thresholdSlack a b c l-weight a b c (i+2)*windowWidth l h (i+2) := by
  fin_cases i <;>
    dsimp [thresholdSlack,lowerCorrectionLevels,weight,windowWidth] <;> ring

theorem thresholdSlack_upperCorrection (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    thresholdSlack a b c (upperCorrectionLevels l h i) =
      thresholdSlack a b c h+weight a b c (i+2)*windowWidth l h (i+2) := by
  fin_cases i <;>
    dsimp [thresholdSlack,upperCorrectionLevels,weight,windowWidth] <;> ring

theorem gapExpression_cancellation (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hl : ∀ i, lowerCapSize a b c l i ≤ 0)
    (hh : ∀ i, capSize a b c h i ≤ 0) :
    2*gapExpression a b c l h = normalizedExpression a b c l h := by
  have hl0 := max_eq_left (hl 0)
  have hl1 := max_eq_left (hl 1)
  have hl2 := max_eq_left (hl 2)
  have hh0 := max_eq_left (hh 0)
  have hh1 := max_eq_left (hh 1)
  have hh2 := max_eq_left (hh 2)
  dsimp [lowerCapSize,capSize,direction] at hl0 hl1 hl2 hh0 hh1 hh2
  simp only [gapExpression, normalizedExpression, lowPairArea, highPairArea,
    lowerThresholdArea, upperThresholdArea, thresholdLoss, Fin.sum_univ_three]
  dsimp [lowPairSlack,highPairSlack,capSize,lowerCapSize,lowerCorrectionLevels,
    upperCorrectionLevels,direction,weight,windowWidth,squarePos,thresholdSlack]
  rw [hl0,hl1,hl2,hh0,hh1,hh2]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring_nf

open CyclicBadThresholds in
/-- Exact identification with twice the original gap in every obstructed configuration. -/
theorem twice_gapArea_eq_normalized_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ CyclicArea.badSeeds C b a c) :
    2*C.gapArea = normalizedExpression (1-a) b c (lowerLevels C c) (upperLevels C c) := by
  obtain ⟨_,_,hp⟩ := pair_conditions_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad
  rw [gapArea_eq_expression_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad]
  exact gapExpression_cancellation (1-a) b c _ _ (fun i => (hp i).1) (fun i => (hp i).2)

open CyclicBadThresholds in
/-- A precise scalar reformulation of the nondegenerate ABC sharp-area target.
The case with no obstructed deficit seed is already covered by translations. -/
theorem sqPos_iff_obstructed_scalar (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) :
    Quant.SqPos C ↔ ∀ z ∈ RowDeletion.triangle C.deficit,
      z ∈ CyclicArea.badSeeds C b a c → squarePos C.deficit ≤
        normalizedExpression (1-a) b c (lowerLevels C c) (upperLevels C c) := by
  constructor
  · intro h z hz hzbad
    have he := twice_gapArea_eq_normalized_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad
    dsimp [Quant.SqPos] at h
    dsimp [squarePos]
    linarith only [h,he]
  · intro h
    by_cases hex : ∃ z, z ∈ RowDeletion.triangle C.deficit ∧ z ∈ CyclicArea.badSeeds C b a c
    · obtain ⟨z,hz,hzbad⟩ := hex
      have he := twice_gapArea_eq_normalized_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad
      have hs := h z hz hzbad
      dsimp [squarePos] at hs
      dsimp [Quant.SqPos]
      linarith only [hs,he]
    · exact CyclicArea.sqPos_of_no_bad_seed C hb ha hc hu₀ hu₁ hu₂
        (fun z hz hzbad => hex ⟨z,hz,hzbad⟩)

end Quant.CyclicGapCancellation
