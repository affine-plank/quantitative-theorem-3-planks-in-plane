/- Actual unit-range section densities in every affine direction. -/
module

public import Plank.Proofs.Quant.PlanarConvexSectionDensity
public import Plank.Proofs.Quant.PlanarBodySectionDensity
public import Plank.Proofs.Quant.PlanarGapAnalysis
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarUnitSectionDensity

open Set MeasureTheory PlanarQuantitative PlanarDirectionDerivatives
open PlanarBodySectionDensity PlanarSevenCellArea ConcaveDensity
open Plank.Convex.DeficientHeightTilt

/-- The actual integral data on the normalized body range. No derivative
across a supporting face is part of this certificate. -/
structure UnitSectionDensity (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) where
  density : ℝ → ℝ
  continuous : Continuous density
  nonnegative : ∀ t, 0 ≤ density t
  concave : ConcaveOn ℝ (Icc (0 : ℝ) 1) density
  area_integral : ∀ lo hi, 0 ≤ lo → lo ≤ hi → hi ≤ 1 →
    coveredArea K f lo hi = ∫ t in lo..hi, density t
  mass_eq : mass density = (volume K).toReal

def chart (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) : Point ≃ᵃ[ℝ] (ℝ × ℝ) :=
  ((directionCoordinates f hf).toAffineEquiv.trans
    (LinearEquiv.finTwoArrow ℝ ℝ).toAffineEquiv).trans
      (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (f 0,0))

theorem chart_first (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (x : Point) :
    (chart f hf x).1 = f x := by
  change f 0+directionCoordinates f hf x 0 = f x
  rw [directionCoordinates_first]
  ring

/-- Exact change of area, including the affine constant and the conversion
from function coordinates to product coordinates. -/
theorem area_chart (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (S : Set Point) :
    (volume S).toReal = areaFactor (directionCoordinates f hf)*
      (volume (chart f hf '' S)).toReal := by
  let T := directionCoordinates f hf
  have hrep : chart f hf '' S = (fun p : ℝ × ℝ => (f 0,0)+p) ''
      (MeasurableEquiv.finTwoArrow '' (T '' S)) := by
    rw [← image_comp,← image_comp]
    rfl
  have hp : volume (T '' S) =
      volume (MeasurableEquiv.finTwoArrow '' (T '' S)) := by
    rw [← (volume_preserving_finTwoArrow ℝ).measure_preimage_equiv]
    rw [Set.preimage_image_eq _ MeasurableEquiv.finTwoArrow.injective]
  have ht : T ⁻¹' (T '' S) = S := Set.preimage_image_eq _ T.injective
  have hh := area_preimage T (T '' S)
  rw [ht,hp] at hh
  letI : (volume : Measure (ℝ × ℝ)).IsAddLeftInvariant :=
    inferInstanceAs (Measure.IsAddLeftInvariant ((volume : Measure ℝ).prod volume))
  rw [hrep,Set.image_add_left,measure_preimage_add]
  exact hh

theorem image_plank (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (K : Set Point) (lo hi : ℝ) :
    chart f hf '' (K ∩ plank f lo hi) =
      PlanarConvexSectionIntegral.slab (chart f hf '' K) lo hi := by
  ext p
  constructor
  · rintro ⟨x,⟨hx,hlo,hhi⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,by simpa only [mem_ofPred_eq,chart_first] using And.intro hlo hhi⟩
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩
    exact ⟨x,⟨hx,by simpa only [plank,mem_ofPred_eq,chart_first] using hp⟩,rfl⟩

/-- Every positive-area compact convex body has actual continuous concave
unit-range section data in every normalized direction, including directions
parallel to a supporting face. -/
theorem exists_unitSectionDensity {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (hunit : rangeWidth K f = 1) : Nonempty (UnitSectionDensity K f) := by
  have hf : f.linear ≠ 0 := PlanarGapCells.linear_ne_zero_of_rangeWidth_pos hne f
    (by rw [hunit]; norm_num)
  let T := chart f hf
  let B := T '' K
  let A := areaFactor (directionCoordinates f hf)
  have hA : 0 < A := areaFactor_pos _
  have hB : IsCompact B := hK.image T.toContinuousAffineEquiv.continuous
  have hcB : Convex ℝ B := hc.affine_image T.toAffineMap
  have hiB : (interior B).Nonempty := by
    change (interior (T.toContinuousAffineEquiv.toHomeomorph '' K)).Nonempty
    rw [← T.toContinuousAffineEquiv.toHomeomorph.image_interior K]
    exact (PlanarGapAnalysis.interior_nonempty_of_area_pos hK hc hV).image T
  have hp : Prod.fst '' B = Icc (0 : ℝ) 1 := by
    rw [show Prod.fst '' B = f '' K by
      rw [show B = T '' K from rfl,← image_comp]
      congr 1
      funext x
      exact chart_first f hf x]
    exact image_eq_unitInterval hK hc hne f hnorm hunit
  let D := PlanarConvexSectionDensity.density B
  refine ⟨{
    density := fun t => A*D t
    continuous := continuous_const.mul
      (PlanarConvexSectionDensity.continuous_density hB hcB hiB hp)
    nonnegative := fun t => mul_nonneg hA.le
      (PlanarConvexSectionDensity.nonnegative_density B t)
    concave := (PlanarConvexSectionDensity.concaveOn_density hB hcB hp).smul hA.le
    area_integral := ?_
    mass_eq := ?_ }⟩
  · intro lo hi hlo ho hhi
    rw [coveredArea,area_chart f hf,image_plank,
      PlanarConvexSectionDensity.area_slab_eq_integral_density hB hlo ho hhi,
      intervalIntegral.integral_const_mul]
  · change (∫ t in (0 : ℝ)..1, A*D t) = _
    rw [intervalIntegral.integral_const_mul]
    change A*mass D = _
    rw [PlanarConvexSectionDensity.mass_density hB hp]
    exact (area_chart f hf K).symm

end Plank.PlanarUnitSectionDensity

/-- info: 'Plank.PlanarUnitSectionDensity.exists_unitSectionDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarUnitSectionDensity.exists_unitSectionDensity
