/- Explicit parametrization of the cyclic equality equations. -/
module

public import Plank.Proofs.Quant.CyclicUnclippedEquality
public import Plank.Proofs.Quant.CyclicAnchorAlgebra

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CyclicEqualityFamily

open MeasureTheory CyclicWeightedThresholdGeometry CyclicThresholdCaps
  CyclicPairAreas CyclicGapCancellation CyclicAnchorAlgebra
  SixTriangleAlgebra SixTriangleResidual SixTriangleEquality CyclicUnclippedEquality

/-- At total width s, interpolate each endpoint between its middle vertex
level and its endpoint in the zero-cut hexagonal cover. -/
def lower (a b c s : ℝ) (i : Fin 3) : ℝ :=
  (1-s)*direction a b c i+s*lowerAnchor a b c i

def upper (a b c s : ℝ) (i : Fin 3) : ℝ :=
  (1-s)*direction a b c i+s*upperAnchor a b c i

theorem p_eq_q {a b c : ℝ} (hbal : a*b*c = (1-a)*(1-b)*(1-c)) :
    p a b c = q a b c := by dsimp [p,q]; linarith only [hbal]

theorem lowCut_direction {a b c : ℝ} (hp : p a b c ≠ 0)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (i : Fin 3) :
    lowCut a b c (direction a b c) i = lowWeight a b c i*lowDenom a b c i := by
  fin_cases i
  · dsimp [lowCut,direction,lowWeight,lowDenom,dets]
    field_simp [hp]
    dsimp [p]
    linear_combination b*hbal
  · dsimp [lowCut,direction,lowWeight,lowDenom,dets]
    field_simp [hp]
    dsimp [p]
    linear_combination c*hbal
  · dsimp [lowCut,direction,lowWeight,lowDenom,dets]
    field_simp [hp]
    dsimp [p]
    linear_combination a*hbal

theorem highCut_direction {a b c : ℝ} (hq : q a b c ≠ 0)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (i : Fin 3) :
    highCut a b c (direction a b c) i = highWeight a b c i*highDenom a b c i := by
  fin_cases i
  · dsimp [highCut,direction,highWeight,highDenom,dets]
    field_simp [hq]
    dsimp [q]
    linear_combination -(1-a)*hbal
  · dsimp [highCut,direction,highWeight,highDenom,dets]
    field_simp [hq]
    dsimp [q]
    linear_combination -(1-b)*hbal
  · dsimp [highCut,direction,highWeight,highDenom,dets]
    field_simp [hq]
    dsimp [q]
    linear_combination -(1-c)*hbal

theorem lowCut_lower {a b c : ℝ} (hp : p a b c ≠ 0)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (s : ℝ) (i : Fin 3) :
    lowCut a b c (lower a b c s) i = (1-s)*lowWeight a b c i*lowDenom a b c i := by
  have he : lowCut a b c (lower a b c s) i =
      (1-s)*lowCut a b c (direction a b c) i+s*lowCut a b c (lowerAnchor a b c) i := by
    fin_cases i <;> dsimp [lowCut,lower] <;> ring
  rw [he,lowCut_direction hp hbal,lowCut_lowerAnchor hp]
  ring

theorem highCut_upper {a b c : ℝ} (hq : q a b c ≠ 0)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (s : ℝ) (i : Fin 3) :
    highCut a b c (upper a b c s) i = (1-s)*highWeight a b c i*highDenom a b c i := by
  have he : highCut a b c (upper a b c s) i =
      (1-s)*highCut a b c (direction a b c) i+s*highCut a b c (upperAnchor a b c) i := by
    fin_cases i <;> dsimp [highCut,upper] <;> ring
  rw [he,highCut_direction hq hbal,highCut_upperAnchor hq]
  ring

theorem deficit_family {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (s : ℝ) :
    deficit (lower a b c s) (upper a b c s) = 1-s := by
  have hd := deficit_anchor (p_pos ha.1 hb.1 hc.1).ne' (q_pos ha.2 hb.2 hc.2).ne'
  rw [(imbalance_eq_zero_iff ha hb hc).mpr hbal,neg_zero] at hd
  have he : deficit (lower a b c s) (upper a b c s) =
      1-s+s*deficit (lowerAnchor a b c) (upperAnchor a b c) := by
    dsimp [deficit,lower,upper]
    ring
  rw [he,hd]
  ring

theorem lowCut_injective {a b c : ℝ} (hp : p a b c ≠ 0) :
    Function.Injective (lowCut a b c) := by
  intro l k he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  dsimp [lowCut] at h0 h1 h2
  have hz : p a b c*(l 0-k 0) = 0 := by
    dsimp [p]
    linear_combination h2-a*h1+a*c*h0
  have e0 : l 0 = k 0 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hp)
  have e1 : l 1 = k 1 := by rw [e0] at h0; linarith only [h0]
  have e2 : l 2 = k 2 := by rw [e1] at h1; linarith only [h1]
  funext i
  fin_cases i <;> assumption

theorem highCut_injective {a b c : ℝ} (hq : q a b c ≠ 0) :
    Function.Injective (highCut a b c) := by
  intro l k he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  dsimp [highCut] at h0 h1 h2
  have hz : q a b c*(l 0-k 0) = 0 := by
    dsimp [q]
    linear_combination -h0+(1-a)*h1-(1-a)*(1-b)*h2
  have e0 : l 0 = k 0 := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hq)
  have e2 : l 2 = k 2 := by rw [e0] at h2; linarith only [h2]
  have e1 : l 1 = k 1 := by rw [e2] at h1; linarith only [h1]
  funext i
  fin_cases i <;> assumption

/-- For fixed directions and total width, the cyclic calibration has at
most one pair of endpoint triples, given by the explicit interpolation. -/
theorem cutCalibration_iff_family {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) :
    CutCalibration a b c l h ↔
      a*b*c = (1-a)*(1-b)*(1-c) ∧
      l = lower a b c (1-deficit l h) ∧ h = upper a b c (1-deficit l h) := by
  have hp := (p_pos ha.1 hb.1 hc.1).ne'
  have hq := (q_pos ha.2 hb.2 hc.2).ne'
  constructor
  · rintro ⟨hbal,hcut⟩
    refine ⟨hbal,lowCut_injective hp ?_,highCut_injective hq ?_⟩
    · funext i
      rw [(hcut i).1,lowCut_lower hp hbal]
      ring
    · funext i
      rw [(hcut i).2,highCut_upper hq hbal]
      ring
  · rintro ⟨hbal,hl,hh⟩
    refine ⟨hbal,fun i => ⟨?_,?_⟩⟩
    · conv_lhs => rw [hl]
      rw [lowCut_lower hp hbal]
      ring
    · conv_lhs => rw [hh]
      rw [highCut_upper hq hbal]
      ring

theorem thresholdSlack_direction {a b c : ℝ}
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) :
    thresholdSlack a b c (direction a b c) = 0 := by
  dsimp [thresholdSlack,direction,k0,k1,k2]
  linear_combination -hbal

theorem anchor_compatible_pos {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (i : Fin 3) :
    0 < (1-direction a b c (i+1))*lowerAnchor a b c i -
      direction a b c i*upperAnchor a b c (i+1) +
      direction a b c i*direction a b c (i+1) := by
  have hp := (p_pos ha.1 hb.1 hc.1).ne'
  have hpq := p_eq_q hbal
  have he : (1-direction a b c (i+1))*lowerAnchor a b c i -
      direction a b c i*upperAnchor a b c (i+1) +
      direction a b c i*direction a b c (i+1) =
      a*b*c*weight a b c (i+2)/p a b c := by
    fin_cases i <;>
      norm_num [lowerAnchor,upperAnchor,direction,weight,Fin.add_def] <;>
      rw [← hpq] <;> field_simp [hp] <;> dsimp [k0,k1,k2,p] <;> ring
  rw [he]
  exact div_pos (mul_pos (mul_pos (mul_pos ha.1 hb.1) hc.1)
    (weight_pos ha hb hc (i+2))) (p_pos ha.1 hb.1 hc.1)

theorem lower_weighted_argument {a b c : ℝ}
    (hp : p a b c ≠ 0) (hq : q a b c ≠ 0)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (s : ℝ) (i : Fin 3) :
    weight a b c i*windowWidth (lower a b c s) (upper a b c s) i -
      thresholdSlack a b c (lower a b c s) = -s*alphaCost a b c i := by
  have he : weight a b c i*windowWidth (lower a b c s) (upper a b c s) i -
      thresholdSlack a b c (lower a b c s) =
      s*(weight a b c i*windowWidth (lowerAnchor a b c) (upperAnchor a b c) i -
        thresholdSlack a b c (lowerAnchor a b c)) -
        (1-s)*thresholdSlack a b c (direction a b c) := by
    dsimp [lower,upper,windowWidth,thresholdSlack]
    ring
  rw [he,alphaArgument_anchor hp hq,thresholdSlack_direction hbal]
  ring

theorem upper_weighted_argument {a b c : ℝ}
    (hp : p a b c ≠ 0) (hq : q a b c ≠ 0)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (s : ℝ) (i : Fin 3) :
    weight a b c i*windowWidth (lower a b c s) (upper a b c s) i +
      thresholdSlack a b c (upper a b c s) = -s*betaCost a b c i := by
  have he : weight a b c i*windowWidth (lower a b c s) (upper a b c s) i +
      thresholdSlack a b c (upper a b c s) =
      s*(weight a b c i*windowWidth (lowerAnchor a b c) (upperAnchor a b c) i +
        thresholdSlack a b c (upperAnchor a b c)) +
        (1-s)*thresholdSlack a b c (direction a b c) := by
    dsimp [lower,upper,windowWidth,thresholdSlack]
    ring
  rw [he,betaArgument_anchor hp hq,thresholdSlack_direction hbal]
  ring

/-- Every member of the balanced interpolation is geometrically admissible
and has no clipping losses. Thus attainment below is unconditional within
the displayed open direction and width ranges. -/
theorem noClippingRegion_family {a b c s : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (hs : 0 < s) (hs1 : s ≤ 1) :
    NoClippingRegion a b c (lower a b c s) (upper a b c s) := by
  have hs' : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hp := (p_pos ha.1 hb.1 hc.1).ne'
  have hq := (q_pos ha.2 hb.2 hc.2).ne'
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact add_nonneg (mul_nonneg hs' (direction_bounds ha hb hc i).1.le)
      (mul_nonneg hs.le (anchor_bounds ha hb hc i).1.le)
  · intro i
    have hgap := mul_pos hs (anchorWidth_pos ha hb hc i)
    dsimp [lower,upper,anchorWidth] at *
    nlinarith only [hgap]
  · intro i
    have h0 := mul_nonneg hs' (sub_nonneg.mpr (direction_bounds ha hb hc i).2.le)
    have h1 := mul_nonneg hs.le (sub_nonneg.mpr (anchor_bounds ha hb hc i).2.2.2.le)
    dsimp [upper]
    nlinarith only [h0,h1]
  · intro i
    have h0 := mul_nonneg hs' (mul_nonneg (direction_bounds ha hb hc i).1.le
      (sub_nonneg.mpr (direction_bounds ha hb hc (i+1)).2.le))
    have h1 := mul_nonneg hs.le (anchor_compatible_pos ha hb hc hbal i).le
    have he : (1-direction a b c (i+1))*lower a b c s i -
        direction a b c i*upper a b c s (i+1) +
        direction a b c i*direction a b c (i+1) =
        (1-s)*(direction a b c i*(1-direction a b c (i+1))) +
        s*((1-direction a b c (i+1))*lowerAnchor a b c i -
          direction a b c i*upperAnchor a b c (i+1) +
          direction a b c i*direction a b c (i+1)) := by
      dsimp [lower,upper]
      ring
    rw [he]
    exact add_nonneg h0 h1
  · intro i
    have h0 := mul_nonneg hs.le (sub_nonneg.mpr (anchor_bounds ha hb hc i).2.1.le)
    have h1 := mul_nonneg hs.le (sub_nonneg.mpr (anchor_bounds ha hb hc i).2.2.1.le)
    dsimp [lower,upper]
    constructor <;> nlinarith only [h0,h1]
  · intro i
    have hL := lower_weighted_argument hp hq hbal s i
    have hH := upper_weighted_argument hp hq hbal s i
    have h0 := mul_nonneg hs.le (alphaCost_pos ha hb hc i).le
    have h1 := mul_nonneg hs.le (betaCost_pos ha hb hc i).le
    constructor <;> nlinarith only [hL,hH,h0,h1]

/-- Actual-area attainment for the full two-direction-parameter cyclic
family, at every total relative width strictly between zero and one. -/
theorem area_family {a b c s : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (hs : 0 < s) (hs1 : s < 1) :
    (volume (CyclicExteriorAssembly.uncovered a b c (lower a b c s) (upper a b c s))).toReal =
      (1-s)^2/2 := by
  have hd := deficit_family ha hb hc hbal s
  have H := noClippingRegion_family ha hb hc hbal hs hs1.le
  have hcal : CutCalibration a b c (lower a b c s) (upper a b c s) := by
    refine ⟨hbal,fun i => ?_⟩
    rw [hd]
    exact ⟨lowCut_lower (p_pos ha.1 hb.1 hc.1).ne' hbal s i,
      highCut_upper (q_pos ha.2 hb.2 hc.2).ne' hbal s i⟩
  have he := (area_equality_iff ha hb hc _ _ H
    (by rw [hd]; exact sub_pos.mpr hs1)).mpr hcal
  simpa only [hd] using he

/-- The exhaustive parametrized family in the no-clipping cyclic region.
This is an actual-area iff, not a condition on an unevaluated objective. -/
theorem area_equality_iff_family {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) (H : NoClippingRegion a b c l h) (hδ : 0 < deficit l h) :
    (volume (CyclicExteriorAssembly.uncovered a b c l h)).toReal = (deficit l h)^2/2 ↔
      a*b*c = (1-a)*(1-b)*(1-c) ∧
      ∃ s : ℝ, 0 < s ∧ s < 1 ∧ l = lower a b c s ∧ h = upper a b c s := by
  constructor
  · intro he
    obtain ⟨hbal,hl,hh⟩ := (cutCalibration_iff_family ha hb hc l h).mp
      ((area_equality_iff ha hb hc l h H hδ).mp he)
    have hδ1 : deficit l h < 1 := by
      dsimp [deficit]
      linarith [H.ordered 0,H.ordered 1,H.ordered 2]
    exact ⟨hbal,1-deficit l h,sub_pos.mpr hδ1,by linarith,hl,hh⟩
  · rintro ⟨hbal,s,hs,hs1,hl,hh⟩
    rw [hl,hh,deficit_family ha hb hc hbal]
    exact area_family ha hb hc hbal hs hs1

open CyclicBadThresholds in
/-- The explicit cyclic family as actual project planks on the standard
triangle. The three normals and six endpoints are all specified. -/
def configuration {a b c s : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (hs : 0 < s) (hs1 : s ≤ 1) : Config :=
  abcConfig b (1-a) c hb ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩ hc
    ![lower a b c s 1,1-upper a b c s 0,c-upper a b c s 2]
    ![upper a b c s 1,1-lower a b c s 0,c-lower a b c s 2]
    (by
      have H := noClippingRegion_family ha hb hc hbal hs hs1
      intro i
      fin_cases i <;> dsimp <;> linarith [H.ordered 0,H.ordered 1,H.ordered 2])

open CyclicBadThresholds in
theorem lowerLevels_configuration {a b c s : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (hs : 0 < s) (hs1 : s ≤ 1) :
    lowerLevels (configuration ha hb hc hbal hs hs1) c = lower a b c s := by
  funext i
  fin_cases i <;> dsimp [lowerLevels,configuration,abcConfig] <;> ring

open CyclicBadThresholds in
theorem upperLevels_configuration {a b c s : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (hs : 0 < s) (hs1 : s ≤ 1) :
    upperLevels (configuration ha hb hc hbal hs hs1) c = upper a b c s := by
  funext i
  fin_cases i <;> dsimp [upperLevels,configuration,abcConfig] <;> ring

theorem configuration_uncovered {a b c s : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (hs : 0 < s) (hs1 : s ≤ 1) :
    (configuration ha hb hc hbal hs hs1).uncovered =
      CyclicExteriorAssembly.uncovered a b c (lower a b c s) (upper a b c s) := by
  rw [CyclicExteriorAssembly.configuration_uncovered
    (configuration ha hb hc hbal hs hs1) rfl rfl rfl,
    lowerLevels_configuration,upperLevels_configuration,
    show 1-(1-a) = a by ring]

/-- The interpolation parameter is exactly the sum of relative widths. -/
theorem configuration_sumRelW {a b c s : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (hs : 0 < s) (hs1 : s ≤ 1) :
    (configuration ha hb hc hbal hs hs1).sumRelW = s := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hd := CyclicSixTermCompensation.deficit_eq_window_deficit
    (configuration ha hb hc hbal hs hs1) hb ha' hc rfl rfl rfl
  rw [lowerLevels_configuration,upperLevels_configuration] at hd
  change (configuration ha hb hc hbal hs hs1).deficit =
    deficit (lower a b c s) (upper a b c s) at hd
  rw [deficit_family ha hb hc hbal] at hd
  dsimp [Config.deficit] at hd
  linarith only [hd]

/-- Geometric attainment, with both actual uncovered area and the original
relative-width budget, for the full balanced cyclic family. -/
theorem configuration_equality {a b c s : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) (hs : 0 < s) (hs1 : s < 1) :
    TriangleEqualityReductions.Equality (configuration ha hb hc hbal hs hs1.le) := by
  rw [TriangleEqualityReductions.Equality,Config.deficit,configuration_sumRelW,
    max_eq_right (sub_pos.mpr hs1).le,Config.gapArea,configuration_uncovered,
    area_family ha hb hc hbal hs hs1]
  ring

end Quant.CyclicEqualityFamily

/-- info: 'Quant.CyclicEqualityFamily.cutCalibration_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicEqualityFamily.cutCalibration_iff_family
/-- info: 'Quant.CyclicEqualityFamily.area_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicEqualityFamily.area_family
/-- info: 'Quant.CyclicEqualityFamily.area_equality_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicEqualityFamily.area_equality_iff_family
/-- info: 'Quant.CyclicEqualityFamily.configuration_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicEqualityFamily.configuration_equality
