/- The diagonal-pair catalogue for original affine forms in every affine chart. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralDiagonalPairCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralDiagonalPairAffine
open Set MeasureTheory CrossedQuadrilateralAttainment
open CrossedQuadrilateralDiagonalPairCatalogue
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- The first two original bands are parallel to one diagonal. The third
positive band is unrestricted; all affine scales and orientations are retained. -/
theorem original (S : Shape) (T : Point ≃ᵃ[ℝ] Point)
    (F : Fin 3 → Point →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (ho : ∀ i, lo i < hi i) (hW : ∀ i, 0 < rangeWidth (T '' S.body) (F i))
    (hy0 : (CrossedQuadrilateralCommonSupportAffine.inChart T (F 0)).linear (0,1) = 0)
    (hy1 : (CrossedQuadrilateralCommonSupportAffine.inChart T (F 1)).linear (0,1) = 0)
    (hR : (∑ i, (hi i-lo i)/rangeWidth (T '' S.body) (F i)) < 1) :
    (volume ((T '' S.body) \ ⋃ i, {z | lo i ≤ F i z ∧ F i z ≤ hi i})).toReal =
      (1-∑ i, (hi i-lo i)/rangeWidth (T '' S.body) (F i))^2*(volume (T '' S.body)).toReal ↔
        Catalogue S (CrossedQuadrilateralCommonSupportAffine.family S T F lo hi
          (fun i => (ho i).le) hW) := by
  let P := CrossedQuadrilateralCommonSupportAffine.family S T F lo hi (fun i => (ho i).le) hW
  have hp (i) : (P i).lo < (P i).hi := sub_lt_sub_right (ho i) _
  have hsum : (∑ i, relativeWidth S (P i)) =
      ∑ i, (hi i-lo i)/rangeWidth (T '' S.body) (F i) := by
    simp only [P,CrossedQuadrilateralCommonSupportAffine.family_width]
  have himage : T '' (⋃ i, (P i).set) = ⋃ i, {z | lo i ≤ F i z ∧ F i z ≤ hi i} := by
    rw [image_iUnion]
    exact iUnion_congr fun i => CrossedQuadrilateralCommonSupportAffine.family_set
      S T F lo hi (fun i => (ho i).le) hW i
  have he := equality_iff_catalogue S P hp hy0 hy1 (by rwa [hsum])
  rw [hsum] at he
  have ht := CrossedQuadrilateralAffine.image_equality_iff T S.body (⋃ i, (P i).set)
    ((1-∑ i, (hi i-lo i)/rangeWidth (T '' S.body) (F i))^2)
  rw [himage] at ht
  exact ht.trans he

end Quant.CrossedQuadrilateralDiagonalPairAffine

/-- info: 'Quant.CrossedQuadrilateralDiagonalPairAffine.original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralDiagonalPairAffine.original
