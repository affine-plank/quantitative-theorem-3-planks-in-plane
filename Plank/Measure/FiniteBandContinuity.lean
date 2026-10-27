module
/- Continuity of finite-band uncovered measure, including reversed windows. -/
public import Plank.Measure.LinearBandsCore
public import Mathlib.MeasureTheory.Integral.Indicator

@[expose] public section
noncomputable section

namespace Plank.FiniteBandContinuity

open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {E ι : Type*} [MeasurableSpace E] [Fintype ι]

/-- The actual complement of the closed bands in the fixed body. Endpoints may
coincide or be reversed. -/
def uncovered (K : Set E) (f : ι → E → ℝ) (p : (ι → ℝ) × (ι → ℝ)) : Set E :=
  K \ ⋃ i, LinearBands.closedBand (f i) (p.1 i) (p.2 i)

theorem measurableSet_uncovered {K : Set E} (hK : MeasurableSet K)
    {f : ι → E → ℝ} (hf : ∀ i, Measurable (f i)) (p : (ι → ℝ) × (ι → ℝ)) :
    MeasurableSet (uncovered K f p) :=
  hK.diff (MeasurableSet.iUnion (fun i =>
    (measurableSet_le measurable_const (hf i)).inter
      (measurableSet_le (hf i) measurable_const)))

private theorem eventually_comparison_of_ne {P : Type*} [TopologicalSpace P]
    {g : P → ℝ} {p : P} {r : ℝ} (hg : ContinuousAt g p) (hne : g p ≠ r) :
    ∀ᶠ q in 𝓝 p, (g q ≤ r ↔ g p ≤ r) ∧ (r ≤ g q ↔ r ≤ g p) := by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [hg.eventually_lt_const h] with q hq
    exact ⟨iff_of_true hq.le h.le, iff_of_false (not_le_of_gt hq) (not_le_of_gt h)⟩
  · filter_upwards [hg.eventually_const_lt h] with q hq
    exact ⟨iff_of_false (not_le_of_gt hq) (not_le_of_gt h), iff_of_true hq.le h.le⟩

omit [MeasurableSpace E] in
/-- Away from the endpoint levels, membership in the actual gap is locally constant. -/
theorem eventually_mem_uncovered_iff (K : Set E) (f : ι → E → ℝ)
    (p : (ι → ℝ) × (ι → ℝ)) (x : E)
    (hlo : ∀ i, f i x ≠ p.1 i) (hhi : ∀ i, f i x ≠ p.2 i) :
    ∀ᶠ q in 𝓝 p, (x ∈ uncovered K f q ↔ x ∈ uncovered K f p) := by
  have hl : ∀ i, ∀ᶠ q in 𝓝 p, (q.1 i ≤ f i x ↔ p.1 i ≤ f i x) := by
    intro i
    have hcont : ContinuousAt (fun q : (ι → ℝ) × (ι → ℝ) => q.1 i) p := by
      fun_prop
    exact (eventually_comparison_of_ne hcont (hlo i).symm).mono fun _ h => h.1
  have hh : ∀ i, ∀ᶠ q in 𝓝 p, (f i x ≤ q.2 i ↔ f i x ≤ p.2 i) := by
    intro i
    have hcont : ContinuousAt (fun q : (ι → ℝ) × (ι → ℝ) => q.2 i) p := by
      fun_prop
    exact (eventually_comparison_of_ne hcont (hhi i).symm).mono fun _ h => h.2
  filter_upwards [Filter.eventually_all.mpr hl, Filter.eventually_all.mpr hh] with q hql hqh
  have hband : (x ∈ ⋃ i, LinearBands.closedBand (f i) (q.1 i) (q.2 i)) ↔
      (x ∈ ⋃ i, LinearBands.closedBand (f i) (p.1 i) (p.2 i)) := by
    simp only [mem_iUnion, LinearBands.closedBand, mem_ofPred_eq]
    exact exists_congr (fun i => and_congr (hql i) (hqh i))
  simp only [uncovered, Set.mem_sdiff, hband]

/-- A finite family of measurable functionals with null levels has continuously
varying uncovered measure inside any fixed measurable body of finite measure. -/
theorem continuous_measure_uncovered (μ : Measure E) {K : Set E}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) {f : ι → E → ℝ}
    (hf : ∀ i, Measurable (f i)) (hnull : ∀ i r, μ {x | f i x = r} = 0) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => μ (uncovered K f p)) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hlo : ∀ᵐ x ∂μ, ∀ i, f i x ≠ p.1 i := by
    apply ae_all_iff.mpr
    intro i
    simpa only [ae_iff, not_not] using hnull i (p.1 i)
  have hhi : ∀ᵐ x ∂μ, ∀ i, f i x ≠ p.2 i := by
    apply ae_all_iff.mpr
    intro i
    simpa only [ae_iff, not_not] using hnull i (p.2 i)
  refine tendsto_measure_of_ae_tendsto_indicator (𝓝 p)
    (measurableSet_uncovered hK hf p) (measurableSet_uncovered hK hf) hK hKfin
    (Eventually.of_forall fun _ => sdiff_subset) ?_
  filter_upwards [hlo, hhi] with x hxlo hxhi
  exact eventually_mem_uncovered_iff K f p x hxlo hxhi

/-- Real-valued form of the same continuity statement. -/
theorem continuous_area_uncovered (μ : Measure E) {K : Set E}
    (hK : MeasurableSet K) (hKfin : μ K ≠ ⊤) {f : ι → E → ℝ}
    (hf : ∀ i, Measurable (f i)) (hnull : ∀ i r, μ {x | f i x = r} = 0) :
    Continuous (fun p : (ι → ℝ) × (ι → ℝ) => (μ (uncovered K f p)).toReal) :=
  ENNReal.continuousOn_toReal.comp_continuous
    (continuous_measure_uncovered μ hK hKfin hf hnull)
    (fun _ => ne_top_of_le_ne_top hKfin (measure_mono Set.sdiff_subset))

end Plank.FiniteBandContinuity
