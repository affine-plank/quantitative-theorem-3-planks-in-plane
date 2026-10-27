/- A geometric gap comparison obtained by merging parallel intervals. -/
module
public import Plank.Proofs.Quant.UnimodalIntervalMerge
public import Plank.Proofs.Quant.PlanarConvexSectionIntegral

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.UnimodalPlanarMerge
open Set MeasureTheory
open Plank.PlanarConvexSectionLength Plank.PlanarConvexSectionIntegral

def band (l u : ℝ) : Set (ℝ × ℝ) := {z | l ≤ z.1 ∧ z.1 ≤ u}

theorem measurable_band (l u : ℝ) : MeasurableSet (band l u) :=
  (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)

/-- Actual uncovered-area comparison, for any compact planar set whose
vertical section lengths form a continuous unimodal function. -/
theorem exists_interval {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hf : Continuous (length K)) {m a b c d : ℝ}
    (hin : MonotoneOn (length K) (Iic m)) (hout : AntitoneOn (length K) (Ici m))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ∃ l u : ℝ, a ≤ l ∧ u ≤ d ∧ l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (volume (K \ band l u)).toReal ≤
        (volume (K \ (band a b ∪ band c d))).toReal := by
  obtain ⟨l,u,hal,hud,hlu,hw,hm⟩ :=
    UnimodalIntervalMerge.exists_interval hf hin hout hab hbc hcd
  refine ⟨l,u,hal,hud,hlu,hw,?_⟩
  have hmass : volume.real (K ∩ (band a b ∪ band c d)) ≤
      volume.real (K ∩ band l u) := by
    rw [inter_union_distrib_left]
    apply (measureReal_union_le _ _).trans
    change (volume (slab K a b)).toReal+(volume (slab K c d)).toReal ≤
      (volume (slab K l u)).toReal
    rw [area_slab_eq_integral hK hab,area_slab_eq_integral hK hcd,
      area_slab_eq_integral hK hlu]
    exact hm
  have hsingle := measureReal_sdiff_add_inter (μ := volume) (s := K)
    (measurable_band l u) hK.measure_ne_top
  have hpair := measureReal_sdiff_add_inter (μ := volume) (s := K)
    ((measurable_band a b).union (measurable_band c d)) hK.measure_ne_top
  change volume.real (K \ band l u) ≤ volume.real (K \ (band a b ∪ band c d))
  linarith only [hmass,hsingle,hpair]

/-- With overlaps or arbitrary label order, a merged interval may extend
beyond the original convex hull. Its length still equals the sum of lengths. -/
theorem exists_interval_unordered {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hf : Continuous (length K)) {m a b c d : ℝ}
    (hin : MonotoneOn (length K) (Iic m)) (hout : AntitoneOn (length K) (Ici m))
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∃ l u : ℝ, l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (volume (K \ band l u)).toReal ≤
        (volume (K \ (band a b ∪ band c d))).toReal := by
  by_cases hbc : b ≤ c
  · obtain ⟨l,u,_,_,ho,hw,hg⟩ := exists_interval hK hf hin hout hab hbc hcd
    exact ⟨l,u,ho,hw,hg⟩
  by_cases hda : d ≤ a
  · obtain ⟨l,u,_,_,ho,hw,hg⟩ := exists_interval hK hf hin hout hcd hda hab
    exact ⟨l,u,ho,by linarith only [hw],by simpa only [Set.union_comm] using hg⟩
  let l := min a c
  let u := l+(b-a)+(d-c)
  have hbu : b ≤ u := by
    dsimp only [u,l]
    rcases le_total a c with h | h
    · rw [min_eq_left h]; linarith only [hcd]
    · rw [min_eq_right h]; linarith only [hda]
  have hdu : d ≤ u := by
    dsimp only [u,l]
    rcases le_total a c with h | h
    · rw [min_eq_left h]; linarith only [hbc]
    · rw [min_eq_right h]; linarith only [hab]
  have hsub : band a b ∪ band c d ⊆ band l u := by
    intro z hz
    rcases hz with hz | hz
    · exact ⟨(min_le_left a c).trans hz.1,hz.2.trans hbu⟩
    · exact ⟨(min_le_right a c).trans hz.1,hz.2.trans hdu⟩
  refine ⟨l,u,by dsimp only [u]; linarith only [hab,hcd],by dsimp only [u]; ring,?_⟩
  exact ENNReal.toReal_mono (measure_ne_top_of_subset sdiff_subset hK.measure_ne_top)
    (measure_mono (Set.sdiff_subset_sdiff_right hsub))

end Quant.UnimodalPlanarMerge

/-- info: 'Quant.UnimodalPlanarMerge.exists_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.UnimodalPlanarMerge.exists_interval
