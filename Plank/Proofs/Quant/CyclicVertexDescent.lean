module
/-
# Midpoint descent of the actual scalar gap margin

Vary lower levels while fixing upper levels, hence allow widths to vary.
The vertex penalty can dominate the low-cut curvature. Threshold losses
only improve that descent; possible positive cap-refund curvature is kept
as an explicit premise, rather than silently discarded.
-/
public import Plank.Proofs.Quant.CyclicClippingBudget
public import Plank.Proofs.Quant.SixTriangleVertexDirection

@[expose] public section
noncomputable section

namespace Quant.CyclicVertexDescent

open CyclicGapCancellation CyclicSixTermCompensation
  CyclicWeightedThresholdGeometry CyclicThresholdCaps CyclicPairAreas

def shift (l v : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ := fun i => l i+t*v i

def lowerSlope (a b c : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![b*v 0+v 1,c*v 1+v 2,v 0+a*v 2]

def energy (a b c : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i, (lowerSlope a b c v i)^2/SixTriangleAlgebra.lowDenom a b c i

def vertexDirection (a b c : ℝ) : Fin 3 → ℝ :=
  ![SixTriangleVertexDirection.v0 a b c,
    SixTriangleVertexDirection.v1 a b c,SixTriangleVertexDirection.v2 a b c]

def margin (a b c : ℝ) (l h : Fin 3 → ℝ) : ℝ :=
  normalizedExpression a b c l h-(SixTriangleResidual.deficit l h)^2

theorem lowCut_shift (a b c : ℝ) (l v : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    SixTriangleAlgebra.lowCut a b c (shift l v t) i =
      SixTriangleAlgebra.lowCut a b c l i+t*lowerSlope a b c v i := by
  fin_cases i <;> dsimp [SixTriangleAlgebra.lowCut,shift,lowerSlope] <;> ring

theorem energy_vertexDirection (a b c : ℝ) :
    energy a b c (vertexDirection a b c) = SixTriangleVertexDirection.lowEnergy a b c := by
  simp only [energy,Fin.sum_univ_three]
  dsimp [lowerSlope,vertexDirection,SixTriangleAlgebra.lowDenom,
    SixTriangleAlgebra.dets,SixTriangleVertexDirection.lowEnergy,
    SixTriangleVertexDirection.k0,SixTriangleVertexDirection.k1,
    SixTriangleVertexDirection.k2]
  ring

theorem sixArea_midpoint_upper (a b c : ℝ) (l h v : Fin 3 → ℝ) (t : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    SixTriangleAlgebra.sixArea a b c (shift l v t) h+
      SixTriangleAlgebra.sixArea a b c (shift l v (-t)) h ≤
      2*SixTriangleAlgebra.sixArea a b c l h+2*t^2*energy a b c v := by
  have hi (i : Fin 3) :
      (max 0 (SixTriangleAlgebra.lowCut a b c (shift l v t) i))^2/
          SixTriangleAlgebra.lowDenom a b c i+
        (max 0 (SixTriangleAlgebra.lowCut a b c (shift l v (-t)) i))^2/
          SixTriangleAlgebra.lowDenom a b c i ≤
      2*((max 0 (SixTriangleAlgebra.lowCut a b c l i))^2/
        SixTriangleAlgebra.lowDenom a b c i)+
      2*t^2*((lowerSlope a b c v i)^2/SixTriangleAlgebra.lowDenom a b c i) := by
    have hh := (SixTriangleVertexDirection.positive_square_midpoint_bounds
      (SixTriangleAlgebra.lowCut a b c l i) (t*lowerSlope a b c v i)).2
    have hd := (SixTriangleAlgebra.denoms_pos ha hb hc i).1.le
    have he : SixTriangleAlgebra.lowCut a b c l i+ -t*lowerSlope a b c v i =
        SixTriangleAlgebra.lowCut a b c l i-t*lowerSlope a b c v i := by ring
    rw [lowCut_shift,lowCut_shift,he,← add_div]
    calc
      _ ≤ (2*(max 0 (SixTriangleAlgebra.lowCut a b c l i))^2+
          2*(t*lowerSlope a b c v i)^2)/SixTriangleAlgebra.lowDenom a b c i :=
        div_le_div_of_nonneg_right hh hd
      _ = _ := by ring
  have hs := add_le_add (add_le_add (hi 0) (hi 1)) (hi 2)
  simp only [SixTriangleAlgebra.sixArea,energy,Fin.sum_univ_three]
  linarith only [hs]

theorem vertexTerm_midpoint_lower (d x h s : ℝ) (hd : 0 < d ∧ d < 1) :
    2*((squarePos (x-d)+squarePos (d-h))/(d*(1-d))) ≤
      (squarePos (x+s-d)+squarePos (d-h))/(d*(1-d))+
      (squarePos (x-s-d)+squarePos (d-h))/(d*(1-d)) := by
  have he1 : x+s-d = (x-d)+s := by ring
  have he2 : x-s-d = (x-d)-s := by ring
  have hs := (SixTriangleVertexDirection.positive_square_midpoint_bounds (x-d) s).1
  change 2*squarePos (x-d) ≤ squarePos ((x-d)+s)+squarePos ((x-d)-s) at hs
  rw [he1,he2]
  have ht := div_le_div_of_nonneg_right hs (mul_pos hd.1 (sub_pos.mpr hd.2)).le
  simp only [div_eq_mul_inv] at ht ⊢
  nlinarith only [ht]

theorem vertexTerm_midpoint_active (d x h s : ℝ)
    (hx : d ≤ x) (hp : d ≤ x+s) (hm : d ≤ x-s) :
    (squarePos (x+s-d)+squarePos (d-h))/(d*(1-d))+
      (squarePos (x-s-d)+squarePos (d-h))/(d*(1-d)) =
      2*((squarePos (x-d)+squarePos (d-h))/(d*(1-d)))+2*s^2/(d*(1-d)) := by
  dsimp only [squarePos]
  rw [max_eq_right (sub_nonneg.mpr hp),max_eq_right (sub_nonneg.mpr hm),
    max_eq_right (sub_nonneg.mpr hx)]
  ring

theorem vertexPenalty_midpoint_lower (a b c : ℝ) (l h v : Fin 3 → ℝ) (t : ℝ)
    (_ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hl : a ≤ l 0) (hp : a ≤ l 0+t*v 0) (hm : a ≤ l 0-t*v 0) :
    2*vertexPenalty a b c l h+2*t^2*(v 0)^2/(a*(1-a)) ≤
      vertexPenalty a b c (shift l v t) h+vertexPenalty a b c (shift l v (-t)) h := by
  have h0 := vertexTerm_midpoint_active a (l 0) (h 0) (t*v 0) hl hp hm
  have h1 := vertexTerm_midpoint_lower b (l 1) (h 1) (t*v 1) hb
  have h2 := vertexTerm_midpoint_lower c (l 2) (h 2) (t*v 2) hc
  simp only [vertexPenalty,Fin.sum_univ_three]
  dsimp [direction,shift]
  simp only [neg_mul,← sub_eq_add_neg]
  simp only [div_eq_mul_inv] at h0 h1 h2 ⊢
  nlinarith only [h0,h1,h2]

def weightedSlope (a b c : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  weight a b c 0*v 0+weight a b c 1*v 1+weight a b c 2*v 2

theorem thresholdSlack_shift (a b c : ℝ) (l v : Fin 3 → ℝ) (t : ℝ) :
    thresholdSlack a b c (shift l v t) =
      thresholdSlack a b c l-t*weightedSlope a b c v := by
  dsimp [thresholdSlack,shift,weightedSlope,weight]
  ring

theorem windowWidth_shift (l h v : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    windowWidth (shift l v t) h i = windowWidth l h i-t*v i := by
  dsimp [windowWidth,shift]
  ring

theorem lowLossArgument_shift (a b c : ℝ) (l h v : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    weight a b c i*windowWidth (shift l v t) h i-thresholdSlack a b c (shift l v t) =
      weight a b c i*windowWidth l h i-thresholdSlack a b c l+
        t*(weightedSlope a b c v-weight a b c i*v i) := by
  rw [windowWidth_shift,thresholdSlack_shift]
  ring

theorem highLossArgument_shift (a b c : ℝ) (l h v : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    weight a b c i*windowWidth (shift l v t) h i+thresholdSlack a b c h =
      weight a b c i*windowWidth l h i+thresholdSlack a b c h+
        t*(-weight a b c i*v i) := by
  rw [windowWidth_shift]
  ring

theorem squarePos_affine_midpoint (x t s : ℝ) :
    2*squarePos x ≤ squarePos (x+t*s)+squarePos (x+(-t)*s) := by
  simpa only [squarePos,neg_mul,sub_eq_add_neg] using
    (SixTriangleVertexDirection.positive_square_midpoint_bounds x (t*s)).1

theorem thresholdLoss_midpoint_lower (a b c : ℝ) (l h v : Fin 3 → ℝ) (t : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    2*thresholdLoss a b c l h ≤
      thresholdLoss a b c (shift l v t) h+thresholdLoss a b c (shift l v (-t)) h := by
  have hi (i : Fin 3) :
      2*(squarePos (weight a b c i*windowWidth l h i-thresholdSlack a b c l)+
          squarePos (weight a b c i*windowWidth l h i+thresholdSlack a b c h)) ≤
        (squarePos (weight a b c i*windowWidth (shift l v t) h i-
            thresholdSlack a b c (shift l v t))+
          squarePos (weight a b c i*windowWidth (shift l v t) h i+thresholdSlack a b c h))+
        (squarePos (weight a b c i*windowWidth (shift l v (-t)) h i-
            thresholdSlack a b c (shift l v (-t)))+
          squarePos (weight a b c i*windowWidth (shift l v (-t)) h i+thresholdSlack a b c h)) := by
    simp only [lowLossArgument_shift,highLossArgument_shift]
    have hl := squarePos_affine_midpoint
      (weight a b c i*windowWidth l h i-thresholdSlack a b c l) t
      (weightedSlope a b c v-weight a b c i*v i)
    have hh := squarePos_affine_midpoint
      (weight a b c i*windowWidth l h i+thresholdSlack a b c h) t
      (-weight a b c i*v i)
    linarith only [hl,hh]
  obtain ⟨h0,h1,h2⟩ := weights_pos ha hb hc
  have hs := div_le_div_of_nonneg_right
    (add_le_add (add_le_add (hi 0) (hi 1)) (hi 2)) (mul_pos (mul_pos h0 h1) h2).le
  simp only [thresholdLoss,Fin.sum_univ_three,div_eq_mul_inv] at hs ⊢
  nlinarith only [hs]

theorem deficit_midpoint_lower (l h v : Fin 3 → ℝ) (t : ℝ) :
    2*(SixTriangleResidual.deficit l h)^2 ≤
      (SixTriangleResidual.deficit (shift l v t) h)^2+
      (SixTriangleResidual.deficit (shift l v (-t)) h)^2 := by
  have he : (SixTriangleResidual.deficit (shift l v t) h)^2+
      (SixTriangleResidual.deficit (shift l v (-t)) h)^2 =
      2*(SixTriangleResidual.deficit l h)^2+2*(t*(v 0+v 1+v 2))^2 := by
    dsimp [SixTriangleResidual.deficit,shift]
    ring
  rw [he]
  nlinarith only [sq_nonneg (t*(v 0+v 1+v 2))]

/-- The exact scalar margin descends if the vertex penalty dominates the low-cut
energy and cap refunds have no positive midpoint curvature on the chosen segment.
Threshold losses may be active or become active anywhere on this segment. -/
theorem margin_midpoint_lt (a b c : ℝ) (l h v : Fin 3 → ℝ) (t : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : t ≠ 0) (hl : a ≤ l 0) (hp : a ≤ l 0+t*v 0) (hm : a ≤ l 0-t*v 0)
    (henergy : energy a b c v < (v 0)^2/(a*(1-a)))
    (hrefund : capRefund a b c (shift l v t) h+capRefund a b c (shift l v (-t)) h ≤
      2*capRefund a b c l h) :
    margin a b c (shift l v t) h+margin a b c (shift l v (-t)) h <
      2*margin a b c l h := by
  have hs := sixArea_midpoint_upper a b c l h v t ha hb hc
  have hv := vertexPenalty_midpoint_lower a b c l h v t ha hb hc hl hp hm
  have hthreshold := thresholdLoss_midpoint_lower a b c l h v t ha hb hc
  have hdeficit := deficit_midpoint_lower l h v t
  have hstrict := mul_lt_mul_of_pos_left henergy (mul_pos (by norm_num : (0:ℝ)<2)
    (sq_pos_of_ne_zero ht))
  simp only [margin,normalizedExpression_decomposition]
  simp only [div_eq_mul_inv] at hv hstrict
  nlinarith only [hs,hv,hthreshold,hdeficit,hrefund,hstrict]

theorem vertexDirection_margin_midpoint_lt (a b c : ℝ) (l h : Fin 3 → ℝ) (t : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : t ≠ 0) (hl : a ≤ l 0)
    (hp : a ≤ l 0+t*vertexDirection a b c 0)
    (hm : a ≤ l 0-t*vertexDirection a b c 0)
    (hrefund : capRefund a b c (shift l (vertexDirection a b c) t) h+
        capRefund a b c (shift l (vertexDirection a b c) (-t)) h ≤
      2*capRefund a b c l h) :
    margin a b c (shift l (vertexDirection a b c) t) h+
        margin a b c (shift l (vertexDirection a b c) (-t)) h <
      2*margin a b c l h := by
  apply margin_midpoint_lt a b c l h _ t ha hb hc ht hl hp hm _ hrefund
  rw [energy_vertexDirection]
  have hs := SixTriangleVertexDirection.selected_cap_strictly_dominates ha hb hc
  change SixTriangleVertexDirection.lowEnergy a b c <
    (SixTriangleVertexDirection.v0 a b c)^2/(a*(1-a))
  linarith only [hs]

def refundArgument (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) : Fin 4 → ℝ :=
  ![-lowPairSlack a b c l i-windowWidth l h (i+1),
    -lowPairSlack a b c l i-direction a b c (i+1)*windowWidth l h i,
    -highPairSlack a b c h i-windowWidth l h i,
    -highPairSlack a b c h i-(1-direction a b c i)*windowWidth l h (i+1)]

def strictCompatible (a b c : ℝ) (t : Fin 3 → ℝ) : Prop :=
  ∀ i, 0 < (1-direction a b c (i+1))*t i-direction a b c i*t (i+1)+
    direction a b c i*direction a b c (i+1)

theorem strictCompatible_of_endpoint_bounds (a b c : ℝ) (l h t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1))
    (ht : ∀ i, l i ≤ t i ∧ t i ≤ h i) : strictCompatible a b c t := by
  intro i
  have hlo := mul_le_mul_of_nonneg_left (ht i).1
    (sub_nonneg.mpr (direction_bounds ha hb hc (i+1)).2.le)
  have hhi := mul_le_mul_of_nonneg_left (ht (i+1)).2
    (direction_bounds ha hb hc i).1.le
  linarith only [hend i,hlo,hhi]

open CyclicBadThresholds in
theorem strictCompatible_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ CyclicArea.badSeeds C b a c)
    (t : Fin 3 → ℝ)
    (ht : ∀ i, lowerLevels C c i ≤ t i ∧ t i ≤ upperLevels C c i) :
    strictCompatible (1-a) b c t := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  exact strictCompatible_of_endpoint_bounds (1-a) b c _ _ t ha' hb hc
    (endpoint_compatible_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad) ht

theorem capSize_neg_of_strictCompatible (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : strictCompatible a b c t) (hq : thresholdSlack a b c t ≤ 0) (i : Fin 3) :
    capSize a b c t i < 0 := by
  have hj := ht (i+1)
  have hmod : i+1+1 = i+2 := by fin_cases i <;> rfl
  rw [hmod] at hj
  have hm := mul_pos (weight_pos ha hb hc (i+2)) hj
  have hq' := mul_nonpos_of_nonneg_of_nonpos (direction_bounds ha hb hc (i+1)).1.le hq
  have hid := capSize_weighted_identity a b c t i
  have hw := weight_pos ha hb hc i
  by_contra hn
  have hn' : 0 ≤ capSize a b c t i := le_of_not_gt hn
  have hp := mul_nonneg hw.le hn'
  linarith only [hm,hq',hid,hp]

theorem lowerCapSize_neg_of_strictCompatible (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : strictCompatible a b c t) (hq : 0 ≤ thresholdSlack a b c t) (i : Fin 3) :
    lowerCapSize a b c t i < 0 := by
  have hj := ht (i+2)
  have hmod : i+2+1 = i := by fin_cases i <;> rfl
  rw [hmod] at hj
  have hm := mul_pos (weight_pos ha hb hc (i+2)) hj
  have hq' := mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sub_nonneg.mpr (direction_bounds ha hb hc i).2.le)) hq
  have hid := lowerCapSize_weighted_identity a b c t i
  have hw := weight_pos ha hb hc (i+1)
  by_contra hn
  have hn' : 0 ≤ lowerCapSize a b c t i := le_of_not_gt hn
  have hp := mul_nonneg hw.le hn'
  linarith only [hm,hq',hid,hp]

open CyclicExteriorAssembly in
theorem refundArguments_neg_of_weighted_bounds (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hwindow : ∀ t : Fin 3 → ℝ, (∀ i, l i ≤ t i ∧ t i ≤ h i) → strictCompatible a b c t)
    (hlh : ∀ i, l i ≤ h i)
    (hweighted : ∀ i, weight a b c i*windowWidth l h i ≤ thresholdSlack a b c l ∧
      weight a b c i*windowWidth l h i ≤ -thresholdSlack a b c h) :
    ∀ i j, refundArgument a b c l h i j < 0 := by
  have hlo (i : Fin 3) : strictCompatible a b c (lowerCorrectionLevels l h i) := by
    apply hwindow
    intro j
    dsimp [lowerCorrectionLevels]
    split_ifs <;> exact ⟨by first | exact le_rfl | exact hlh j,
      by first | exact le_rfl | exact hlh j⟩
  have hhi (i : Fin 3) : strictCompatible a b c (upperCorrectionLevels l h i) := by
    apply hwindow
    intro j
    dsimp [upperCorrectionLevels]
    split_ifs <;> exact ⟨by first | exact le_rfl | exact hlh j,
      by first | exact le_rfl | exact hlh j⟩
  have hcap (i j : Fin 3) : capSize a b c (upperCorrectionLevels l h i) j < 0 := by
    apply capSize_neg_of_strictCompatible a b c _ ha hb hc (hhi i)
    rw [thresholdSlack_upperCorrection]
    linarith only [(hweighted (i+2)).2]
  have hlcap (i j : Fin 3) : lowerCapSize a b c (lowerCorrectionLevels l h i) j < 0 := by
    apply lowerCapSize_neg_of_strictCompatible a b c _ ha hb hc (hlo i)
    rw [thresholdSlack_lowerCorrection]
    linarith only [(hweighted (i+2)).1]
  intro i j
  have he0 : refundArgument a b c l h i 0 = capSize a b c (upperCorrectionLevels l h (i+1)) i := by
    fin_cases i <;> dsimp [refundArgument,lowPairSlack,capSize,windowWidth,
      upperCorrectionLevels,direction] <;> ring
  have he1 : refundArgument a b c l h i 1 = capSize a b c (upperCorrectionLevels l h (i+2)) i := by
    fin_cases i <;> dsimp [refundArgument,lowPairSlack,capSize,windowWidth,
      upperCorrectionLevels,direction] <;> ring
  have he2 : refundArgument a b c l h i 2 = lowerCapSize a b c (lowerCorrectionLevels l h (i+2)) i := by
    fin_cases i <;> dsimp [refundArgument,highPairSlack,lowerCapSize,windowWidth,
      lowerCorrectionLevels,direction] <;> ring
  have he3 : refundArgument a b c l h i 3 = lowerCapSize a b c (lowerCorrectionLevels l h (i+1)) i := by
    fin_cases i <;> dsimp [refundArgument,highPairSlack,lowerCapSize,windowWidth,
      lowerCorrectionLevels,direction] <;> ring
  fin_cases j
  · change refundArgument a b c l h i 0 < 0
    rw [he0]; exact hcap (i+1) i
  · change refundArgument a b c l h i 1 < 0
    rw [he1]; exact hcap (i+2) i
  · change refundArgument a b c l h i 2 < 0
    rw [he2]; exact hlcap (i+2) i
  · change refundArgument a b c l h i 3 < 0
    rw [he3]; exact hlcap (i+1) i

theorem capRefund_eq_zero_of_arguments (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hargs : ∀ i j, refundArgument a b c l h i j ≤ 0) :
    capRefund a b c l h = 0 := by
  have hz (i : Fin 3) (j : Fin 4) : squarePos (refundArgument a b c l h i j) = 0 := by
    simp only [squarePos,max_eq_left (hargs i j),zero_pow (by decide : 2 ≠ 0)]
  have h0 (i : Fin 3) := hz i 0
  have h1 (i : Fin 3) := hz i 1
  have h2 (i : Fin 3) := hz i 2
  have h3 (i : Fin 3) := hz i 3
  dsimp only [refundArgument,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,Matrix.cons_val] at h0 h1 h2 h3
  simp only [capRefund,h0,h1,h2,h3,zero_add,zero_div,Finset.sum_const_zero]

theorem continuous_refundArgument_shift (a b c : ℝ) (l h v : Fin 3 → ℝ)
    (i : Fin 3) (j : Fin 4) :
    Continuous (fun t : ℝ => refundArgument a b c (shift l v t) h i j) := by
  fin_cases i <;> fin_cases j <;>
    dsimp [refundArgument,lowPairSlack,highPairSlack,capSize,lowerCapSize,
      windowWidth,shift,direction] <;> fun_prop

open Filter in
open scoped Topology in
/-- With a strictly active selected vertex penalty and strictly inactive refund
hinges, there are arbitrarily small lower-level perturbations improving the full
margin. In particular, threshold-loss activation faces do not stop this descent.
No assertion is made here that an external feasible set contains the perturbations. -/
theorem exists_small_descent (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hl : a < l 0) (hargs : ∀ i j, refundArgument a b c l h i j < 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      (margin a b c (shift l (vertexDirection a b c) t) h < margin a b c l h ∨
       margin a b c (shift l (vertexDirection a b c) (-t)) h < margin a b c l h) := by
  let v := vertexDirection a b c
  have hzero : shift l v 0 = l := by ext i; simp [shift]
  have hi (i : Fin 3) (j : Fin 4) :
      ∀ᶠ t : ℝ in 𝓝 0, refundArgument a b c (shift l v t) h i j < 0 := by
    have hh : refundArgument a b c (shift l v 0) h i j < 0 := by
      simpa only [hzero] using hargs i j
    exact (continuous_refundArgument_shift a b c l h v i j).continuousAt.eventually
      (gt_mem_nhds hh)
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i j, refundArgument a b c (shift l v t) h i j < 0 := by
    simpa only [eventually_all] using hi
  have hv : ∀ᶠ t : ℝ in 𝓝 0, a < shift l v t 0 := by
    have hh : a < shift l v 0 0 := by simpa only [hzero] using hl
    have hcont : Continuous (fun t : ℝ => shift l v t 0) := by dsimp [shift]; fun_prop
    exact hcont.continuousAt.eventually (lt_mem_nhds hh)
  have hgood : ∀ᶠ t : ℝ in 𝓝 0,
      capRefund a b c (shift l v t) h = 0 ∧ a < shift l v t 0 := by
    filter_upwards [hall,hv] with t ht hvt
    exact ⟨capRefund_eq_zero_of_arguments a b c _ h (fun i j => (ht i j).le),hvt⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let t : ℝ := min r ε/2
  have ht : 0 < t := half_pos (lt_min hr hε)
  have htr : t < r := (half_lt_self (lt_min hr hε)).trans_le (min_le_left r ε)
  have htε : t < ε := (half_lt_self (lt_min hr hε)).trans_le (min_le_right r ε)
  have hpt : t ∈ Metric.ball (0:ℝ) r := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using htr
  have hmt : -t ∈ Metric.ball (0:ℝ) r := by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_neg,abs_of_pos ht] using htr
  have hp := hball hpt
  have hm := hball hmt
  have hc0 := capRefund_eq_zero_of_arguments a b c l h (fun i j => (hargs i j).le)
  have hrefund : capRefund a b c (shift l v t) h+capRefund a b c (shift l v (-t)) h ≤
      2*capRefund a b c l h := by rw [hp.1,hm.1,hc0]; norm_num
  have hpm : a ≤ l 0-t*v 0 := by
    have hh := hm.2.le
    dsimp only [shift] at hh
    nlinarith only [hh]
  have hlt := vertexDirection_margin_midpoint_lt a b c l h t ha hb hc ht.ne' hl.le
    hp.2.le hpm hrefund
  refine ⟨t,ht,htε,?_⟩
  by_contra hn
  push Not at hn
  linarith only [hlt,hn.1,hn.2]

/-- The no-threshold-loss inequalities permit equality: descent crosses their
activation faces in the full scalar objective. Feasible-set boundary estimates
are still required for a global minimization argument. -/
theorem exists_small_descent_of_weighted_bounds (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hl : a < l 0) (hlh : ∀ i, l i ≤ h i)
    (hwindow : ∀ t : Fin 3 → ℝ, (∀ i, l i ≤ t i ∧ t i ≤ h i) → strictCompatible a b c t)
    (hweighted : ∀ i, weight a b c i*windowWidth l h i ≤ thresholdSlack a b c l ∧
      weight a b c i*windowWidth l h i ≤ -thresholdSlack a b c h)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧
      (margin a b c (shift l (vertexDirection a b c) t) h < margin a b c l h ∨
       margin a b c (shift l (vertexDirection a b c) (-t)) h < margin a b c l h) :=
  exists_small_descent a b c l h ha hb hc hl
    (refundArguments_neg_of_weighted_bounds a b c l h ha hb hc hwindow hlh hweighted) ε hε

end Quant.CyclicVertexDescent
