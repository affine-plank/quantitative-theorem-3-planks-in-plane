/- Actual finite-band gap measure is continuous when both observables and
endpoints vary. No convexity, dimension, or direction-separation assumption. -/
module

public import Plank.Measure.FiniteBandContinuity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.MovingBandContinuity

open Set MeasureTheory Filter Topology FiniteBandContinuity
open scoped ENNReal

variable {E ι P : Type*} [MeasurableSpace E] [Fintype ι]
  [TopologicalSpace P] [FirstCountableTopology P]

omit [FirstCountableTopology P] in
theorem eventually_le_iff_of_ne {g h : P → ℝ} {p : P}
    (hg : ContinuousAt g p) (hh : ContinuousAt h p) (hne : g p≠h p) :
    ∀ᶠ q in 𝓝 p, (g q≤h q ↔ g p≤h p) := by
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact (hg.eventually_lt hh hl).mono fun _ hq => iff_of_true hq.le hl.le
  · exact (hh.eventually_lt hg hl).mono fun _ hq =>
      iff_of_false (not_le_of_gt hq) (not_le_of_gt hl)

omit [MeasurableSpace E] [FirstCountableTopology P] in
/-- Membership is locally constant off the limiting band boundaries, even
when the measured observables themselves vary with the parameter. -/
theorem eventually_mem_uncovered_iff (K : Set E) (f : P → ι → E → ℝ)
    (lo hi : P → ι → ℝ) (p : P) (x : E)
    (hf : ∀ i, ContinuousAt (fun q => f q i x) p)
    (hl : ∀ i, ContinuousAt (fun q => lo q i) p)
    (hh : ∀ i, ContinuousAt (fun q => hi q i) p)
    (hlo : ∀ i, f p i x≠lo p i) (hhi : ∀ i, f p i x≠hi p i) :
    ∀ᶠ q in 𝓝 p, (x∈uncovered K (f q) (lo q,hi q) ↔
      x∈uncovered K (f p) (lo p,hi p)) := by
  have hlow := fun i => eventually_le_iff_of_ne (hl i) (hf i) (hlo i).symm
  have hupp := fun i => eventually_le_iff_of_ne (hf i) (hh i) (hhi i)
  filter_upwards [Filter.eventually_all.mpr hlow, Filter.eventually_all.mpr hupp]
    with q hql hqh
  have hband : (x∈⋃ i, LinearBands.closedBand (f q i) (lo q i) (hi q i)) ↔
      (x∈⋃ i, LinearBands.closedBand (f p i) (lo p i) (hi p i)) := by
    simp only [mem_iUnion, LinearBands.closedBand, mem_ofPred_eq]
    exact exists_congr (fun i => and_congr (hql i) (hqh i))
  simp only [uncovered, Set.mem_sdiff, hband]

/-- Only the limiting observables need null level sets. Nearby bands can
have repeated directions, zero width, reversed endpoints, or other degeneracy. -/
theorem continuousAt_measure_uncovered (μ : Measure E) {K : Set E}
    (hK : MeasurableSet K) (hKfin : μ K≠⊤) (f : P → ι → E → ℝ)
    (lo hi : P → ι → ℝ) (p : P)
    (hmeas : ∀ q i, Measurable (f q i))
    (hf : ∀ i x, ContinuousAt (fun q => f q i x) p)
    (hl : ∀ i, ContinuousAt (fun q => lo q i) p)
    (hh : ∀ i, ContinuousAt (fun q => hi q i) p)
    (hnull : ∀ i r, μ {x | f p i x=r}=0) :
    ContinuousAt (fun q => μ (uncovered K (f q) (lo q,hi q))) p := by
  classical
  have hlo : ∀ᵐ x ∂μ, ∀ i, f p i x≠lo p i := by
    apply ae_all_iff.mpr
    intro i
    simpa only [ae_iff, not_not] using hnull i (lo p i)
  have hhi : ∀ᵐ x ∂μ, ∀ i, f p i x≠hi p i := by
    apply ae_all_iff.mpr
    intro i
    simpa only [ae_iff, not_not] using hnull i (hi p i)
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun q => (uncovered K (f q) (lo q,hi q)).indicator (1 : E → ℝ≥0∞) x)
        (𝓝 p) (𝓝 ((uncovered K (f p) (lo p,hi p)).indicator 1 x)) := by
    filter_upwards [hlo,hhi] with x hxlo hxhi
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_uncovered_iff K f lo hi p x
      (fun i => hf i x) hl hh hxlo hxhi] with q hq
    by_cases hp : x∈uncovered K (f p) (lo p,hi p)
    · simp only [indicator_of_mem hp,indicator_of_mem (hq.mpr hp)]
    · have hnq : x∉uncovered K (f q) (lo q,hi q) := fun h => hp (hq.mp h)
      simp only [indicator_of_notMem hp,indicator_of_notMem hnq]
  have hbound : ∀ q, ∀ᵐ x ∂μ,
      (uncovered K (f q) (lo q,hi q)).indicator (1 : E → ℝ≥0∞) x≤K.indicator 1 x := by
    intro q
    filter_upwards [] with x
    by_cases hx : x∈uncovered K (f q) (lo q,hi q)
    · simp only [indicator_of_mem hx,indicator_of_mem hx.1,le_refl]
    · simp only [indicator_of_notMem hx,zero_le]
  have hfin : ∫⁻ x, K.indicator (1 : E → ℝ≥0∞) x ∂μ≠⊤ := by
    rw [lintegral_indicator_one hK]
    exact hKfin
  have ht := tendsto_lintegral_filter_of_dominated_convergence
    (F := fun q => (uncovered K (f q) (lo q,hi q)).indicator (1 : E → ℝ≥0∞))
    (f := (uncovered K (f p) (lo p,hi p)).indicator (1 : E → ℝ≥0∞))
    (K.indicator (1 : E → ℝ≥0∞))
    (Filter.Eventually.of_forall (fun q => measurable_const.indicator
      (measurableSet_uncovered hK (hmeas q) (lo q,hi q))))
    (Filter.Eventually.of_forall hbound) hfin hlim
  have hi' : ∀ q, (∫⁻ x,
      (uncovered K (f q) (lo q,hi q)).indicator (1 : E → ℝ≥0∞) x ∂μ)=
      μ (uncovered K (f q) (lo q,hi q)) := fun q =>
    lintegral_indicator_one (measurableSet_uncovered hK (hmeas q) (lo q,hi q))
  simpa only [hi', ContinuousAt] using ht

theorem continuousAt_area_uncovered (μ : Measure E) {K : Set E}
    (hK : MeasurableSet K) (hKfin : μ K≠⊤) (f : P → ι → E → ℝ)
    (lo hi : P → ι → ℝ) (p : P)
    (hmeas : ∀ q i, Measurable (f q i))
    (hf : ∀ i x, ContinuousAt (fun q => f q i x) p)
    (hl : ∀ i, ContinuousAt (fun q => lo q i) p)
    (hh : ∀ i, ContinuousAt (fun q => hi q i) p)
    (hnull : ∀ i r, μ {x | f p i x=r}=0) :
    ContinuousAt (fun q => (μ (uncovered K (f q) (lo q,hi q))).toReal) p :=
  (ENNReal.tendsto_toReal (ne_top_of_le_ne_top hKfin
    (measure_mono Set.sdiff_subset))).comp
      (continuousAt_measure_uncovered μ hK hKfin f lo hi p hmeas hf hl hh hnull)

theorem continuous_area_uncovered (μ : Measure E) {K : Set E}
    (hK : MeasurableSet K) (hKfin : μ K≠⊤) (f : P → ι → E → ℝ)
    (lo hi : P → ι → ℝ) (hmeas : ∀ q i, Measurable (f q i))
    (hf : ∀ i x, Continuous (fun q => f q i x))
    (hl : ∀ i, Continuous (fun q => lo q i))
    (hh : ∀ i, Continuous (fun q => hi q i))
    (hnull : ∀ p i r, μ {x | f p i x=r}=0) :
    Continuous (fun q => (μ (uncovered K (f q) (lo q,hi q))).toReal) := by
  rw [continuous_iff_continuousAt]
  exact fun p => continuousAt_area_uncovered μ hK hKfin f lo hi p hmeas
    (fun i x => (hf i x).continuousAt) (fun i => (hl i).continuousAt)
    (fun i => (hh i).continuousAt) (hnull p)

end Plank.MovingBandContinuity

#print axioms Plank.MovingBandContinuity.continuous_area_uncovered
