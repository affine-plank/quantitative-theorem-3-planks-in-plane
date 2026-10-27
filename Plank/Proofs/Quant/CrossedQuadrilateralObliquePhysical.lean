/- Actual physical widths and affine transport for the oblique-support catalogue. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralObliqueCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralObliquePhysical
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionProfile
open CrossedQuadrilateralSectionGeometry CrossedQuadrilateralObliqueCatalogue
open CrossedQuadrilateralSupport CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralCommonSupport CrossedQuadrilateralPlacement
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem oblique_bounds (S : Shape) {k : ℝ} (hk : YSupports S k) {z : Point} (hz : z ∈ S.body) :
    -S.d ≤ k*z.1+z.2 ∧ k*z.1+z.2 ≤ S.b := by
  have hs : swap z ∈ (transpose S).body := by
    rw [← swap_body]
    exact mem_image_of_mem swap hz
  rw [body_eq_union] at hs
  have ht (j : Bool) (hz' : swap z ∈ (half (transpose S) j).set) :=
    triangle_bounds _ (CrossedQuadrilateralObliquePair.swappedPlank k 0 0 le_rfl)
      (CrossedQuadrilateralObliquePair.common S hk 0 0 le_rfl j) hz'
  rcases hs with hs | hs
  · simpa only [half,transpose,CrossedQuadrilateralObliquePair.swappedPlank,dot,
      swap_apply,one_mul,mul_zero,add_zero,add_comm] using ht false hs
  · simpa only [half,transpose,CrossedQuadrilateralObliquePair.swappedPlank,dot,
      swap_apply,one_mul,mul_zero,add_zero,add_comm] using ht true hs

/-- The denominator in the catalogue is the full actual directional range. -/
theorem oblique_range (S : Shape) {k : ℝ} (hk : YSupports S k) :
    rangeWidth S.body (direction (k,1)) = S.b+S.d := by
  have hh := Plank.Body.width_eq_of_realisers (f := direction (k,1))
    (vertexY_mem S true) (vertexY_mem S false)
    (fun z hz => by simpa [dot,Shape.Y] using (oblique_bounds S hk hz).2)
    (fun z hz => by simpa [dot,Shape.Y] using (oblique_bounds S hk hz).1)
  change rangeWidth S.body (direction (k,1)) = _ at hh
  simpa [dot,Shape.Y] using hh

def obliquePlank (k lo hi : ℝ) (ho : lo ≤ hi) : Plank where
  u := (k,1)
  u_ne_zero := by simp
  lo := lo
  hi := hi
  lo_le_hi := ho

theorem obliquePlank_set (k lo hi : ℝ) (ho : lo ≤ hi) :
    (obliquePlank k lo hi ho).set = oblique k lo hi := by
  ext z
  change (lo ≤ dot (k,1) z ∧ dot (k,1) z ≤ hi) ↔
    (lo ≤ k*z.1+z.2 ∧ k*z.1+z.2 ≤ hi)
  simp only [dot,one_mul]

def family (k a b c d lo hi : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (ho : lo ≤ hi) : Fin 3 → Plank :=
  ![axisPlank false a b hab,axisPlank false c d hcd,obliquePlank k lo hi ho]

theorem family_union (k a b c d lo hi : ℝ) (hab : a ≤ b) (hcd : c ≤ d) (ho : lo ≤ hi) :
    (⋃ i, (family k a b c d lo hi hab hcd ho i).set) =
      (UnimodalPlanarMerge.band a b ∪ UnimodalPlanarMerge.band c d) ∪ oblique k lo hi := by
  rw [CrossedQuadrilateralCommonPairSplit.union_three]
  change (axisPlank false a b hab).set ∪ ((axisPlank false c d hcd).set ∪
    (obliquePlank k lo hi ho).set) = _
  rw [axisPlank_set,axisPlank_set,obliquePlank_set,← Set.union_assoc]
  rfl

theorem family_budget (S : Shape) {k : ℝ} (hk : YSupports S k) (a b c d lo hi : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (ho : lo ≤ hi) :
    (∑ i, relativeWidth S (family k a b c d lo hi hab hcd ho i)) = total S a b c d lo hi := by
  rw [Fin.sum_univ_three]
  change relativeWidth S (axisPlank false a b hab)+relativeWidth S (axisPlank false c d hcd)+
    relativeWidth S (obliquePlank k lo hi ho) = _
  rw [(axisPlank_relative_width S a b lo hi hab ho).1,
    (axisPlank_relative_width S c d lo hi hcd ho).1]
  change (b-a)/(S.a+S.c)+(d-c)/(S.a+S.c)+(hi-lo)/rangeWidth S.body (direction (k,1)) = _
  rw [oblique_range S hk]
  rfl

/-- The sector iff uses the actual sum of the three physical relative widths. -/
theorem equality_iff_catalogue (S : Shape) {k a b c d lo hi : ℝ} (hk : YSupports S k)
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : total S a b c d lo hi < 1) :
    (volume (S.body \ ⋃ i, (family k a b c d lo hi hab.le hcd.le ho.le i).set)).toReal =
      (1-∑ i, relativeWidth S (family k a b c d lo hi hab.le hcd.le ho.le i))^2*
        (volume S.body).toReal ↔ Catalogue S k a b c d lo hi := by
  rw [family_union,family_budget S hk]
  exact CrossedQuadrilateralObliqueCatalogue.equality_iff_catalogue S hk hab hcd ho hR

/-- Every invertible affine image preserves the physical family, actual
relative widths and the complete geometric iff. -/
theorem affine_equality_iff (S : Shape) (T : Point ≃ᵃ[ℝ] Point)
    {k a b c d lo hi : ℝ} (hk : YSupports S k)
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : total S a b c d lo hi < 1) :
    (volume (T '' S.body \ ⋃ i, CrossedQuadrilateralAffine.imagePlank T
      (family k a b c d lo hi hab.le hcd.le ho.le i))).toReal =
      (1-∑ i, CrossedQuadrilateralAffine.imageRelativeWidth S T
        (family k a b c d lo hi hab.le hcd.le ho.le i))^2*(volume (T '' S.body)).toReal ↔
        Catalogue S k a b c d lo hi := by
  rw [CrossedQuadrilateralAffine.family_equality_iff]
  exact equality_iff_catalogue S hk hab hcd ho hR

end Quant.CrossedQuadrilateralObliquePhysical

/-- info: 'Quant.CrossedQuadrilateralObliquePhysical.affine_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralObliquePhysical.affine_equality_iff
