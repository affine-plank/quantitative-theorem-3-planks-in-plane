/- Width-preserving mergers before the adjacent-support valley and at overlaps. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAdjacentStrict
public import Plank.Proofs.Quant.CrossedQuadrilateralObliqueTwo

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAdjacentMerge
open Set MeasureTheory CrossedQuadrilateralAttainment
open CrossedQuadrilateralAdjacentProfile CrossedQuadrilateralSectionProfile
open CrossedQuadrilateralSectionGeometry UnimodalPlanarMerge
open Plank.PlanarConvexSectionLength Plank.PlanarConvexSectionIntegral

theorem before_valley (S : Shape) {k lo hi a b c d : ℝ} (hk : Sector S k)
    (ho : lo < hi) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hd : d ≤ valley S k lo) :
    ∃ l u : ℝ, l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (volume (S.body \ (band l u ∪ oblique k lo hi))).toReal ≤
        (volume (S.body \ ((band a b ∪ band c d) ∪ oblique k lo hi))).toReal := by
  let f (x : ℝ) := residual S k lo hi (min x (valley S k lo))
  have hf := truncated_unimodal S hk ho.le
  obtain ⟨l,u,hal,hud,hlu,hw,hm⟩ :=
    UnimodalIntervalMerge.exists_interval hf.1 hf.2.1 hf.2.2 hab hbc hcd
  have hI {v w : ℝ} (hvw : v ≤ w) (hwd : w ≤ d) :
      (∫ x in v..w, residual S k lo hi x) = ∫ x in v..w, f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hvw] at hx
    dsimp only [f]
    rw [min_eq_left (hx.2.trans (hwd.trans hd))]
  let K := closedResidual S k lo hi
  have hK : IsCompact K := compact_closedResidual S k lo hi
  have hmass : volume.real (K ∩ (band a b ∪ band c d)) ≤ volume.real (K ∩ band l u) := by
    rw [inter_union_distrib_left]
    apply (measureReal_union_le _ _).trans
    change (volume (slab K a b)).toReal+(volume (slab K c d)).toReal ≤
      (volume (slab K l u)).toReal
    rw [area_slab_eq_integral hK hab,area_slab_eq_integral hK hcd,
      area_slab_eq_integral hK hlu]
    simp only [K,length_closedResidual S k ho]
    rw [hI hab (hbc.trans hcd),hI hcd le_rfl,hI hlu hud]
    exact hm
  have hs := measureReal_sdiff_add_inter (μ := volume) (s := K)
    (measurable_band l u) hK.measure_ne_top
  have hp := measureReal_sdiff_add_inter (μ := volume) (s := K)
    ((measurable_band a b).union (measurable_band c d)) hK.measure_ne_top
  refine ⟨l,u,hlu,hw,?_⟩
  rw [gap_eq_closedResidual,gap_eq_closedResidual]
  change volume.real (K \ band l u) ≤ volume.real (K \ (band a b ∪ band c d))
  linarith only [hmass,hs,hp]

/-- Touching or overlapping intervals can be enlarged to one interval
of the same total width, for an arbitrary residual geometry. -/
theorem overlap (S : Shape) (k lo hi : ℝ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hcb : c ≤ b) (had : a ≤ d) :
    ∃ l u : ℝ, l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (volume (S.body \ (band l u ∪ oblique k lo hi))).toReal ≤
        (volume (S.body \ ((band a b ∪ band c d) ∪ oblique k lo hi))).toReal := by
  let l := min a c
  let u := l+(b-a)+(d-c)
  have hbu : b ≤ u := by
    dsimp only [u,l]
    rcases le_total a c with h | h
    · rw [min_eq_left h]; linarith only [hcd]
    · rw [min_eq_right h]; linarith only [had]
  have hdu : d ≤ u := by
    dsimp only [u,l]
    rcases le_total a c with h | h
    · rw [min_eq_left h]; linarith only [hcb]
    · rw [min_eq_right h]; linarith only [hab]
  have hsub : band a b ∪ band c d ⊆ band l u := by
    intro z hz
    rcases hz with hz | hz
    · exact ⟨(min_le_left a c).trans hz.1,hz.2.trans hbu⟩
    · exact ⟨(min_le_right a c).trans hz.1,hz.2.trans hdu⟩
  refine ⟨l,u,by dsimp only [u]; linarith only [hab,hcd],by dsimp only [u]; ring,?_⟩
  apply ENNReal.toReal_mono (measure_ne_top_of_subset sdiff_subset (compact_body S).measure_ne_top)
  exact measure_mono (Set.sdiff_subset_sdiff_right (union_subset_union_left _ hsub))

end Quant.CrossedQuadrilateralAdjacentMerge

/-- info: 'Quant.CrossedQuadrilateralAdjacentMerge.before_valley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAdjacentMerge.before_valley
