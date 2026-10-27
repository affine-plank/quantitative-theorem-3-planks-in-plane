/- Complete exclusion of the adjacent Y-minus/X-plus support sector. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAdjacentMerge

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAdjacentExclusion
open Set MeasureTheory CrossedQuadrilateralAttainment
open CrossedQuadrilateralAdjacentProfile CrossedQuadrilateralPairBudget
open CrossedQuadrilateralSectionGeometry UnimodalPlanarMerge
open CrossedQuadrilateralObliquePhysical CrossedQuadrilateralAffine
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- The sector inequalities are exactly the asserted adjacent support bounds. -/
theorem support_bounds (S : Shape) {k : ℝ} (hk : Sector S k)
    {z : ℝ × ℝ} (hz : z ∈ S.body) : -S.d ≤ k*z.1+z.2 ∧ k*z.1+z.2 ≤ k*S.a := by
  have hka := (div_le_iff₀ S.ha).mp hk.1
  have hkc := (le_div_iff₀ S.hc).mp hk.2
  have hpa := mul_pos (sector_pos S hk) S.ha
  have hpc := mul_pos (sector_pos S hk) S.hc
  have hv : S.vertices ⊆ {z : ℝ × ℝ | -S.d ≤ dot (k,1) z ∧ dot (k,1) z ≤ k*S.a} := by
    rintro z (rfl | rfl | rfl | rfl) <;> simp only [mem_ofPred_eq,dot,mul_zero,one_mul,add_zero,zero_add]
    all_goals constructor <;> nlinarith only [hka,hkc,hpa,hpc,S.hb,S.hd]
  simpa only [mem_ofPred_eq,dot,one_mul] using
    convexHull_min hv ((convex_Icc (-S.d) (k*S.a)).linear_preimage (form (k,1)).toLinearMap) hz

theorem support_range (S : Shape) {k : ℝ} (hk : Sector S k) :
    rangeWidth S.body (direction (k,1)) = k*S.a+S.d := by
  have h := Plank.Body.width_eq_of_realisers (f := direction (k,1))
    (vertexX_mem S true) (vertexY_mem S false)
    (fun z hz => by simpa [dot,Shape.X] using (support_bounds S hk hz).2)
    (fun z hz => by simpa [dot,Shape.Y] using (support_bounds S hk hz).1)
  change rangeWidth S.body (direction (k,1)) = _ at h
  simpa [dot,Shape.X,Shape.Y] using h

theorem merge_not_equality (S : Shape) {k lo hi a b c d : ℝ} (hk : Sector S k)
    (ho : lo < hi) (hab : a < b) (hcd : c < d)
    (hR : budget S k a b c d lo hi < 1)
    (hm : ∃ l u : ℝ, l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (volume (S.body \ (band l u ∪ oblique k lo hi))).toReal ≤
        gap S k a b c d lo hi) :
    gap S k a b c d lo hi ≠ (1-budget S k a b c d lo hi)^2*(volume S.body).toReal := by
  intro he
  obtain ⟨l,u,_,hw,hgap⟩ := hm
  have hu : l < u := by linarith only [hw,hab,hcd]
  have hbudget : CrossedQuadrilateralObliqueTwo.total S k l u lo hi =
      budget S k a b c d lo hi := by
    unfold CrossedQuadrilateralObliqueTwo.total budget
    rw [hw]
    ring
  have hR' : CrossedQuadrilateralObliqueTwo.total S k l u lo hi < 1 := by rwa [hbudget]
  have hlow := CrossedQuadrilateralObliqueTwo.lower_bound S hu.le ho.le hR'
  have he' : (volume (S.body \ (band l u ∪ oblique k lo hi))).toReal =
      (1-CrossedQuadrilateralObliqueTwo.total S k l u lo hi)^2*(volume S.body).toReal := by
    rw [hbudget] at hlow ⊢
    linarith only [hlow,hgap,he]
  exact (sector_pos S hk).ne' (CrossedQuadrilateralObliqueTwo.direction_of_equality S hu ho hR' he')

theorem separated_not_equality (S : Shape) {k lo hi a b c d : ℝ} (hk : Sector S k)
    (ho : lo < hi) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hR : budget S k a b c d lo hi < 1) :
    gap S k a b c d lo hi ≠ (1-budget S k a b c d lo hi)^2*(volume S.body).toReal := by
  rcases le_or_gt d (valley S k lo) with hd | hd
  · apply merge_not_equality S hk ho hab hcd hR
    exact CrossedQuadrilateralAdjacentMerge.before_valley S hk ho hab.le hbc.le hcd.le hd
  · exact (CrossedQuadrilateralAdjacentStrict.strict S hk ho hab hbc hcd hd hR).ne'

/-- Every placement is strict: separated, touching, overlapping and either label order. -/
theorem strict (S : Shape) {k lo hi a b c d : ℝ} (hk : Sector S k)
    (ho : lo < hi) (hab : a < b) (hcd : c < d)
    (hR : budget S k a b c d lo hi < 1) :
    (1-budget S k a b c d lo hi)^2*(volume S.body).toReal < gap S k a b c d lo hi := by
  have hbnd := CrossedQuadrilateralPairBudget.lower_bound S hab.le hcd.le ho.le hR
  rw [← actual_area] at hbnd
  apply lt_of_le_of_ne hbnd
  intro he
  have he' := he.symm
  by_cases hbc : b < c
  · exact separated_not_equality S hk ho hab hbc hcd hR he'
  by_cases hda : d < a
  · have hg : gap S k c d a b lo hi = gap S k a b c d lo hi := by
      unfold gap
      rw [union_comm (band c d) (band a b)]
    have hB : budget S k c d a b lo hi = budget S k a b c d lo hi := by
      unfold budget
      ring
    have hs := separated_not_equality S hk ho hcd hda hab (by rwa [hB])
    rw [hg,hB] at hs
    exact hs he'
  · exact merge_not_equality S hk ho hab hcd hR
      (CrossedQuadrilateralAdjacentMerge.overlap S k lo hi hab.le hcd.le
        (le_of_not_gt hbc) (le_of_not_gt hda)) he'

theorem physical_strict (S : Shape) {k lo hi a b c d : ℝ} (hk : Sector S k)
    (ho : lo < hi) (hab : a < b) (hcd : c < d)
    (hR : budget S k a b c d lo hi < 1) :
    (1-∑ i, relativeWidth S (family k a b c d lo hi hab.le hcd.le ho.le i))^2*
        (volume S.body).toReal <
      (volume (S.body \ ⋃ i, (family k a b c d lo hi hab.le hcd.le ho.le i).set)).toReal := by
  rw [actual_budget,CrossedQuadrilateralObliquePhysical.family_union]
  exact strict S hk ho hab hcd hR

/-- All invertible affine images are excluded, using each actual physical relative width. -/
theorem affine_not_equality (S : Shape) (T : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ))
    {k lo hi a b c d : ℝ} (hk : Sector S k)
    (ho : lo < hi) (hab : a < b) (hcd : c < d)
    (hR : budget S k a b c d lo hi < 1) :
    (volume (T '' S.body \ ⋃ i, imagePlank T
      (family k a b c d lo hi hab.le hcd.le ho.le i))).toReal ≠
      (1-∑ i, imageRelativeWidth S T (family k a b c d lo hi hab.le hcd.le ho.le i))^2*
        (volume (T '' S.body)).toReal := by
  intro he
  have he' := (family_equality_iff S T (family k a b c d lo hi hab.le hcd.le ho.le)).mp he
  exact (physical_strict S hk ho hab hcd hR).ne' he'

end Quant.CrossedQuadrilateralAdjacentExclusion

/-- info: 'Quant.CrossedQuadrilateralAdjacentExclusion.affine_not_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAdjacentExclusion.affine_not_equality
