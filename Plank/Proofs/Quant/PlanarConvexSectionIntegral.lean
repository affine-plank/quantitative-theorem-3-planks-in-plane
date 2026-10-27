/- Actual area integrals and interior cut derivatives for arbitrary convex bodies. -/
module

public import Plank.Proofs.Quant.PlanarConvexSectionLength
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarConvexSectionIntegral

open Set MeasureTheory ConvexSections PlanarConvexSectionLength
open scoped Topology

theorem measurable_length {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    Measurable (length K) :=
  (measurable_measure_prodMk_left hK.measurableSet).ennreal_toReal

/-- Fubini for the actual body, with no polygon hypothesis. -/
theorem area_eq_integral {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    (volume K).toReal = ∫ t : ℝ, length K t := by
  rw [Measure.volume_eq_prod ℝ ℝ,Measure.prod_apply hK.measurableSet]
  exact (integral_toReal (measurable_measure_prodMk_left hK.measurableSet).aemeasurable
    (Filter.Eventually.of_forall fun t => (compact_fiber hK t).measure_lt_top)).symm

theorem integrable_length {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    Integrable (length K) := by
  apply integrable_toReal_of_lintegral_ne_top
    (measurable_measure_prodMk_left hK.measurableSet).aemeasurable
  rw [← Measure.prod_apply hK.measurableSet,← Measure.volume_eq_prod ℝ ℝ]
  exact hK.measure_ne_top

def slab (K : Set (ℝ × ℝ)) (lo hi : ℝ) : Set (ℝ × ℝ) :=
  K ∩ {p | lo ≤ p.1 ∧ p.1 ≤ hi}

theorem compact_slab {K : Set (ℝ × ℝ)} (hK : IsCompact K) (lo hi : ℝ) :
    IsCompact (slab K lo hi) :=
  hK.inter_right ((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_fst continuous_const))

/-- The actual area between two cuts is the integral of actual section
lengths. Cuts may lie outside the body's support interval. -/
theorem area_slab_eq_integral {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {lo hi : ℝ} (ho : lo ≤ hi) :
    (volume (slab K lo hi)).toReal = ∫ t in lo..hi, length K t := by
  classical
  have he : length (slab K lo hi) = (Icc lo hi).indicator (length K) := by
    funext t
    by_cases ht : t ∈ Icc lo hi
    · rw [indicator_of_mem ht]
      have hs : fiber (slab K lo hi) t = fiber K t := by
        ext y
        simp only [fiber,slab,mem_preimage,mem_inter_iff,mem_ofPred_eq]
        exact and_iff_left ht
      rw [length,hs,length]
    · rw [indicator_of_notMem ht]
      have hs : fiber (slab K lo hi) t = ∅ := by
        ext y
        simp only [fiber,slab,mem_preimage,mem_inter_iff,mem_ofPred_eq,mem_empty_iff_false]
        exact iff_false_intro (fun h => ht h.2)
      simp only [length,hs,measure_empty,ENNReal.toReal_zero]
  rw [area_eq_integral (compact_slab hK lo hi),he,integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le ho]

/-- Interior cuts have their actual section lengths as area derivatives.
Flat supporting faces cause no difficulty because the cut is internal. -/
theorem hasDerivAt_area_slab_right {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hfull : (interior K).Nonempty)
    {lo hi : ℝ} (ho : lo < hi) (hi_int : hi ∈ interior (Prod.fst '' K)) :
    HasDerivAt (fun t => (volume (slab K lo t)).toReal) (length K hi) hi := by
  have hd := continuousAt_section_measure (volume : Measure ℝ) hK hc hfull hi_int
  apply (intervalIntegral.integral_hasDerivAt_right
    (integrable_length hK).intervalIntegrable
    (measurable_length hK).stronglyMeasurable.stronglyMeasurableAtFilter hd).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ho] with t ht
  exact area_slab_eq_integral hK ht.le

theorem hasFDerivAt_area_slab {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hfull : (interior K).Nonempty)
    {lo hi : ℝ} (ho : lo < hi)
    (hlo : lo ∈ interior (Prod.fst '' K)) (hhi : hi ∈ interior (Prod.fst '' K)) :
    HasFDerivAt (fun p : ℝ × ℝ => (volume (slab K p.1 p.2)).toReal)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (length K hi)-
        (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (length K lo)) (lo,hi) := by
  apply (intervalIntegral.integral_hasFDerivAt
    (integrable_length hK).intervalIntegrable
    (measurable_length hK).stronglyMeasurable.stronglyMeasurableAtFilter
    (measurable_length hK).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_section_measure (volume : Measure ℝ) hK hc hfull hlo)
    (continuousAt_section_measure (volume : Measure ℝ) hK hc hfull hhi)).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_fst continuous_snd).mem_nhds ho] with p hp
  exact area_slab_eq_integral hK hp.le

end Plank.PlanarConvexSectionIntegral

/-- info: 'Plank.PlanarConvexSectionIntegral.hasFDerivAt_area_slab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarConvexSectionIntegral.hasFDerivAt_area_slab
