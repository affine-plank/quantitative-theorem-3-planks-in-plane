/- Rigidity for one vertical and one arbitrarily oriented positive band. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralPhysicalPairDirections

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralObliqueTwo
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralPlacement
open CrossedQuadrilateralObliquePhysical CrossedQuadrilateralSectionGeometry
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def pair (k l u lo hi : ℝ) (hu : l ≤ u) (ho : lo ≤ hi) : Fin 2 → Plank :=
  ![axisPlank false l u hu,obliquePlank k lo hi ho]

def total (S : Shape) (k l u lo hi : ℝ) : ℝ :=
  (u-l)/(S.a+S.c)+(hi-lo)/rangeWidth S.body (direction (k,1))

theorem pair_budget (S : Shape) (k l u lo hi : ℝ) (hu : l ≤ u) (ho : lo ≤ hi) :
    (∑ i, relativeWidth S (pair k l u lo hi hu ho i)) = total S k l u lo hi := by
  rw [Fin.sum_univ_two]
  change relativeWidth S (axisPlank false l u hu)+relativeWidth S (obliquePlank k lo hi ho) = _
  rw [(axisPlank_relative_width S l u lo hi hu ho).1]
  rfl

theorem pair_union (k l u lo hi : ℝ) (hu : l ≤ u) (ho : lo ≤ hi) :
    (⋃ i, (pair k l u lo hi hu ho i).set) =
      UnimodalPlanarMerge.band l u ∪ oblique k lo hi := by
  have hunion : (⋃ i, (pair k l u lo hi hu ho i).set) =
      (axisPlank false l u hu).set ∪ (obliquePlank k lo hi ho).set := by
    ext z
    simp [pair,Fin.exists_fin_two]
  rw [hunion]
  rw [axisPlank_set,obliquePlank_set]
  rfl

theorem lower_bound (S : Shape) {k l u lo hi : ℝ} (hu : l ≤ u) (ho : lo ≤ hi)
    (hR : total S k l u lo hi < 1) :
    (1-total S k l u lo hi)^2*(volume S.body).toReal ≤
      (volume (S.body \ (UnimodalPlanarMerge.band l u ∪ oblique k lo hi))).toReal := by
  have hh := CrossedQuadrilateralPhysicalPairDirections.lower_bound S (pair k l u lo hi hu ho)
  rw [pair_budget,pair_union,max_eq_right (sub_pos.mpr hR).le] at hh
  exact hh

/-- Every positive vertical/oblique equality has horizontal second direction. -/
theorem direction_of_equality (S : Shape) {k l u lo hi : ℝ} (hu : l < u) (ho : lo < hi)
    (hR : total S k l u lo hi < 1)
    (he : (volume (S.body \ (UnimodalPlanarMerge.band l u ∪ oblique k lo hi))).toReal =
      (1-total S k l u lo hi)^2*(volume S.body).toReal) : k = 0 := by
  have hd := CrossedQuadrilateralPhysicalPairDirections.physical S
    (pair k l u lo hi hu.le ho.le) (by intro i; fin_cases i; exact hu; exact ho)
    (by rwa [pair_budget]) (by rwa [pair_budget,pair_union])
  have h := hd 1
  change k = 0 ∨ (1 : ℝ) = 0 at h
  exact h.resolve_right one_ne_zero

end Quant.CrossedQuadrilateralObliqueTwo

/-- info: 'Quant.CrossedQuadrilateralObliqueTwo.direction_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralObliqueTwo.direction_of_equality
