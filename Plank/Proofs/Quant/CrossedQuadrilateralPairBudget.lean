/- Actual area and width formulas for a parallel pair and an arbitrary oblique band. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralObliquePhysical
public import Plank.Proofs.Quant.ParallelPairGapIntegral

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralPairBudget
open Set MeasureTheory Proofs.Basic
open CrossedQuadrilateralAttainment CrossedQuadrilateralSectionGeometry
open CrossedQuadrilateralDiagonalSplit CrossedQuadrilateralPlacement
open CrossedQuadrilateralObliquePhysical CrossedQuadrilateralCommonSupport
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def budget (S : Shape) (k a b c d lo hi : ℝ) : ℝ :=
  (b-a)/(S.a+S.c)+(d-c)/(S.a+S.c)+(hi-lo)/rangeWidth S.body (direction (k,1))

def gap (S : Shape) (k a b c d lo hi : ℝ) : ℝ :=
  (volume (S.body \ ((UnimodalPlanarMerge.band a b ∪ UnimodalPlanarMerge.band c d) ∪
    oblique k lo hi))).toReal

theorem actual_budget (S : Shape) (k a b c d lo hi : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (ho : lo ≤ hi) :
    (∑ i, relativeWidth S (family k a b c d lo hi hab hcd ho i)) =
      budget S k a b c d lo hi := by
  rw [Fin.sum_univ_three]
  change relativeWidth S (axisPlank false a b hab)+relativeWidth S (axisPlank false c d hcd)+
    relativeWidth S (obliquePlank k lo hi ho) = _
  rw [(axisPlank_relative_width S a b lo hi hab ho).1,
    (axisPlank_relative_width S c d lo hi hcd ho).1]
  rfl

theorem actual_area (S : Shape) :
    (volume S.body).toReal = (S.b+S.d)*(S.a+S.c)/2 := by
  rw [area_split,AffineTransport.area_triangle,AffineTransport.area_triangle]
  simp only [half,Shape.Y,Bool.false_eq_true,if_false,if_true,det3,
    sub_neg_eq_add,sub_zero,sub_self,zero_mul,sub_zero,abs_mul,
    abs_of_pos (add_pos S.ha S.hc),abs_neg,abs_of_pos S.hd,abs_of_pos S.hb]
  ring

theorem lower_bound (S : Shape) {k a b c d lo hi : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (ho : lo ≤ hi)
    (hR : budget S k a b c d lo hi < 1) :
    (1-budget S k a b c d lo hi)^2*((S.b+S.d)*(S.a+S.c)/2) ≤
      gap S k a b c d lo hi := by
  have hh := product_lower_bound (compact_body S) (convex_body S) ⟨0,zero_mem S⟩
    (family k a b c d lo hi hab hcd ho)
    (fun i => direction_width_pos S (family k a b c d lo hi hab hcd ho i).u_ne_zero)
  change (max 0 (1-∑ i, relativeWidth S (family k a b c d lo hi hab hcd ho i)))^2*
    (volume S.body).toReal ≤ _ at hh
  rw [actual_budget,CrossedQuadrilateralObliquePhysical.family_union,actual_area,
    max_eq_right (sub_pos.mpr hR).le] at hh
  exact hh

end Quant.CrossedQuadrilateralPairBudget

/-- info: 'Quant.CrossedQuadrilateralPairBudget.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralPairBudget.lower_bound
