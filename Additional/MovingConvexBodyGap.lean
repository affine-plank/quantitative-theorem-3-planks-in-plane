/- Continuity of actual gap volume as a convex body and its planks move.
A common inner ball prevents collapse; a fixed compact outer set supplies
domination. These geometric hypotheses are explicit. -/
module

public import CompactConvexBodyDomain
public import MovingBandContinuity
public import Mathlib.Analysis.Convex.Measure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.MovingConvexBodyGap

open Set TopologicalSpace Metric Filter Topology MeasureTheory
open scoped ENNReal

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace P]

/-- A small Hausdorff displacement cannot remove the contracted old body
when the new convex body contains the same inner ball. -/
theorem smul_mem_of_dist_lt (K L : NonemptyCompacts E) (hL : Convex ℝ (L : Set E))
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (ht1 : t < 1)
    (hin : closedBall (0 : E) r ⊆ L) (hd : dist K L < r*(1-t))
    {x : E} (hx : x ∈ K) : t • x ∈ L := by
  obtain ⟨y,hy,hxy⟩ := exists_dist_lt_of_hausdorffDist_lt hx hd (edist_ne_top K L)
  let z := (t/(1-t)) • (x-y)
  have hz : z ∈ L := by
    apply hin
    rw [mem_closedBall, dist_zero_right]
    have hcoef : 0 < t/(1-t) := div_pos ht (sub_pos.mpr ht1)
    have hn : ‖z‖ < t*r := by
      calc
        ‖z‖ = (t/(1-t))*dist x y := by
          simp only [z, norm_smul, Real.norm_eq_abs, abs_of_pos hcoef, dist_eq_norm]
        _ < (t/(1-t))*(r*(1-t)) := mul_lt_mul_of_pos_left hxy hcoef
        _ = t*r := by field_simp [sub_ne_zero.mpr ht1.ne']
    exact hn.le.trans (mul_le_of_le_one_left hr.le ht1.le)
  have heq : t • y + (1-t) • z = t • x := by
    dsimp [z]
    rw [smul_smul, mul_div_cancel₀ _ (sub_ne_zero.mpr ht1.ne')]
    module
  rw [←heq]
  exact hL hy hz ht.le (sub_nonneg.mpr ht1.le) (by ring)

theorem eventually_mem_of_mem_interior (K : P → NonemptyCompacts E) {p : P}
    (hK : ContinuousAt K p) (hconv : ∀ q, Convex ℝ (K q : Set E))
    {r : ℝ} (hr : 0 < r) (hin : ∀ q, closedBall (0 : E) r ⊆ K q)
    {x : E} (hx : x ∈ interior (K p : Set E)) :
    ∀ᶠ q in 𝓝 p, x ∈ K q := by
  have hc : ContinuousAt (fun a : ℝ => a • x) 1 := by fun_prop
  have hn : {a : ℝ | a • x ∈ interior (K p : Set E)} ∈ 𝓝 1 :=
    hc.preimage_mem_nhds (isOpen_interior.mem_nhds (by simpa using hx))
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hn
  let a : ℝ := 1+ε/2
  have ha : 1 < a := by dsimp [a]; linarith only [hε]
  have hax : a • x ∈ K p := by
    apply interior_subset
    apply hsub
    rw [mem_ball, Real.dist_eq, abs_of_pos (by dsimp [a]; linarith only [hε])]
    dsimp [a]
    linarith only [hε]
  have ht : 0 < a⁻¹ := inv_pos.mpr (zero_lt_one.trans ha)
  have ht1 : a⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans ha)).mpr ha
  have hd : ∀ᶠ q in 𝓝 p, dist (K p) (K q) < r*(1-a⁻¹) := by
    have hc' : ContinuousAt (fun q => dist (K p) (K q)) p := continuousAt_const.dist hK
    exact hc'.eventually_lt continuousAt_const (by
      simpa only [dist_self] using mul_pos hr (sub_pos.mpr ht1))
  filter_upwards [hd] with q hq
  simpa only [smul_smul, inv_mul_cancel₀ (zero_lt_one.trans ha).ne', one_smul] using
    smul_mem_of_dist_lt (K p) (K q) (hconv q) hr ht ht1 (hin q) hq hax

theorem eventually_mem_iff (K : P → NonemptyCompacts E) {p : P}
    (hK : ContinuousAt K p) (hconv : ∀ q, Convex ℝ (K q : Set E))
    {r : ℝ} (hr : 0 < r) (hin : ∀ q, closedBall (0 : E) r ⊆ K q)
    {x : E} (hx : x ∉ frontier (K p : Set E)) :
    ∀ᶠ q in 𝓝 p, (x ∈ K q ↔ x ∈ K p) := by
  by_cases hp : x ∈ K p
  · exact (eventually_mem_of_mem_interior K hK hconv hr hin
      ((mem_interior_iff_notMem_frontier hp).mpr hx)).mono fun _ hq => iff_of_true hq hp
  · have hpos : 0 < infDist x (K p : Set E) :=
      (K p).isCompact.isClosed.notMem_iff_infDist_pos (K p).nonempty |>.mp hp
    have hc : ContinuousAt (fun q => infDist x (K q : Set E)) p :=
      (lipschitz_infDist_set x).continuous.continuousAt.comp hK
    filter_upwards [continuousAt_const.eventually_lt hc hpos] with q hq
    exact iff_of_false (fun h => by rw [infDist_zero_of_mem h] at hq; exact lt_irrefl _ hq) hp

section Measure

variable {ι : Type*} [Fintype ι] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FirstCountableTopology P]

/-- Actual uncovered Haar volume varies continuously with the body, observables
and endpoints. Only the limiting observables need null level sets. -/
theorem continuousAt_measure_uncovered (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : P → NonemptyCompacts E) {p : P} (hK : ContinuousAt K p)
    (hconv : ∀ q, Convex ℝ (K q : Set E)) {r : ℝ} (hr : 0 < r)
    (hin : ∀ q, closedBall (0 : E) r ⊆ K q)
    {H : Set E} (hH : IsCompact H) (hout : ∀ q, (K q : Set E) ⊆ H)
    (f : P → ι → E → ℝ) (lo hi : P → ι → ℝ)
    (hmeas : ∀ q i, Measurable (f q i))
    (hf : ∀ i x, ContinuousAt (fun q => f q i x) p)
    (hl : ∀ i, ContinuousAt (fun q => lo q i) p)
    (hh : ∀ i, ContinuousAt (fun q => hi q i) p)
    (hnull : ∀ i s, μ {x | f p i x = s} = 0) :
    ContinuousAt (fun q => μ (FiniteBandContinuity.uncovered
      (K q : Set E) (f q) (lo q,hi q))) p := by
  classical
  let U (q : P) := FiniteBandContinuity.uncovered (K q : Set E) (f q) (lo q,hi q)
  have hmeasU (q) : MeasurableSet (U q) :=
    FiniteBandContinuity.measurableSet_uncovered (K q).isCompact.measurableSet
      (hmeas q) (lo q,hi q)
  have hnf : ∀ᵐ x ∂μ, x ∉ frontier (K p : Set E) :=
    measure_eq_zero_iff_ae_notMem.mp ((hconv p).addHaar_frontier μ)
  have hlo : ∀ᵐ x ∂μ, ∀ i, f p i x ≠ lo p i := by
    apply ae_all_iff.mpr
    intro i
    simpa only [ae_iff, not_not] using hnull i (lo p i)
  have hhi : ∀ᵐ x ∂μ, ∀ i, f p i x ≠ hi p i := by
    apply ae_all_iff.mpr
    intro i
    simpa only [ae_iff, not_not] using hnull i (hi p i)
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun q => (U q).indicator (1 : E → ℝ≥0∞) x)
        (𝓝 p) (𝓝 ((U p).indicator 1 x)) := by
    filter_upwards [hnf,hlo,hhi] with x hx hxl hxh
    have hbody := eventually_mem_iff K hK hconv hr hin hx
    have hband := MovingBandContinuity.eventually_mem_uncovered_iff univ f lo hi p x
      (fun i => hf i x) hl hh hxl hxh
    have heq : ∀ᶠ q in 𝓝 p, (x ∈ U q ↔ x ∈ U p) := by
      filter_upwards [hbody,hband] with q hq hb
      simp only [FiniteBandContinuity.uncovered, Set.mem_sdiff, mem_univ, true_and] at hb
      exact and_congr hq hb
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with q hq
    by_cases hp : x ∈ U p
    · simp only [indicator_of_mem hp,indicator_of_mem (hq.mpr hp)]
    · have hnq : x ∉ U q := fun h => hp (hq.mp h)
      simp only [indicator_of_notMem hp,indicator_of_notMem hnq]
  have hbound : ∀ q, ∀ᵐ x ∂μ, (U q).indicator (1 : E → ℝ≥0∞) x ≤ H.indicator 1 x := by
    intro q
    filter_upwards [] with x
    by_cases hx : x ∈ U q
    · simp only [indicator_of_mem hx,indicator_of_mem (hout q hx.1),le_refl]
    · simp only [indicator_of_notMem hx,zero_le]
  have hfin : ∫⁻ x, H.indicator (1 : E → ℝ≥0∞) x ∂μ ≠ ⊤ := by
    rw [lintegral_indicator_one hH.measurableSet]
    exact hH.measure_ne_top
  have ht := tendsto_lintegral_filter_of_dominated_convergence
    (F := fun q => (U q).indicator (1 : E → ℝ≥0∞))
    (f := (U p).indicator (1 : E → ℝ≥0∞)) (H.indicator (1 : E → ℝ≥0∞))
    (Filter.Eventually.of_forall fun q => measurable_const.indicator (hmeasU q))
    (Filter.Eventually.of_forall hbound) hfin hlim
  have hi' : ∀ q, (∫⁻ x, (U q).indicator (1 : E → ℝ≥0∞) x ∂μ) = μ (U q) :=
    fun q => lintegral_indicator_one (hmeasU q)
  simpa only [hi', ContinuousAt] using ht

theorem continuousAt_area_uncovered (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : P → NonemptyCompacts E) {p : P} (hK : ContinuousAt K p)
    (hconv : ∀ q, Convex ℝ (K q : Set E)) {r : ℝ} (hr : 0 < r)
    (hin : ∀ q, closedBall (0 : E) r ⊆ K q)
    {H : Set E} (hH : IsCompact H) (hout : ∀ q, (K q : Set E) ⊆ H)
    (f : P → ι → E → ℝ) (lo hi : P → ι → ℝ)
    (hmeas : ∀ q i, Measurable (f q i))
    (hf : ∀ i x, ContinuousAt (fun q => f q i x) p)
    (hl : ∀ i, ContinuousAt (fun q => lo q i) p)
    (hh : ∀ i, ContinuousAt (fun q => hi q i) p)
    (hnull : ∀ i s, μ {x | f p i x = s} = 0) :
    ContinuousAt (fun q => μ.real (FiniteBandContinuity.uncovered
      (K q : Set E) (f q) (lo q,hi q))) p :=
  (ENNReal.tendsto_toReal (ne_top_of_le_ne_top hH.measure_ne_top
    (measure_mono (sdiff_subset.trans (hout p))))).comp
    (continuousAt_measure_uncovered μ K hK hconv hr hin hH hout f lo hi hmeas hf hl hh hnull)

/-- The body volume itself is the case with no planks. -/
theorem continuousAt_volume (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : P → NonemptyCompacts E) {p : P} (hK : ContinuousAt K p)
    (hconv : ∀ q, Convex ℝ (K q : Set E)) {r : ℝ} (hr : 0 < r)
    (hin : ∀ q, closedBall (0 : E) r ⊆ K q)
    {H : Set E} (hH : IsCompact H) (hout : ∀ q, (K q : Set E) ⊆ H) :
    ContinuousAt (fun q => μ.real (K q : Set E)) p := by
  have ht := continuousAt_area_uncovered (ι := Empty) μ K hK hconv hr hin hH hout
    (fun _ i => nomatch i) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ i => nomatch i) (fun i => nomatch i) (fun i => nomatch i)
    (fun i => nomatch i) (fun i => nomatch i)
  simpa only [FiniteBandContinuity.uncovered, iUnion_of_empty, sdiff_empty] using ht

end Measure

end Plank.MovingConvexBodyGap
