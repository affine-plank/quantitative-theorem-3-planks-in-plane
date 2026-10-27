/- The actual quantitative margin on finite point hulls.
The anchor's inner ball, the outer bound, and full support of the sampling
measure are explicit hypotheses. No numerical or pseudorandom claim is made. -/
module

public import FiniteHullSampling
public import NormalizedPlankBodyMinimum
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.QuantitativeSamplingSupport

open Set TopologicalSpace Metric MeasureTheory FiniteHullSampling
open scoped ENNReal

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

abbrev Parameters := (ι → NormalizedPlankBodyMinimum.Direction (E := E)) ×
  {p : NormalizedPlankBodyMinimum.Endpoints (ι := ι) |
    p ∈ NormalizedPlankBodyMinimum.windowDomain 1}

variable {A : Finset E} {H : Set E} {r R : ℝ}

def normalizedBody (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R) (K : AnchoredBody A H) :
    NormalizedPlankBodyMinimum.Body (E := E) r R :=
  ⟨K.1,K.2.1,hin.trans (convexHull_min K.2.2.1 K.2.1),K.2.2.2.trans hout⟩

def data (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R) (q : AnchoredBody A H × Parameters (E := E) (ι := ι)) :
    NormalizedPlankBodyMinimum.Data (E := E) (ι := ι) r R :=
  (normalizedBody hin hout q.1,q.2.1,q.2.2.1)

omit [FiniteDimensional ℝ E] in
theorem continuous_data (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R) :
    Continuous (data (ι := ι) hin hout) := by
  unfold data normalizedBody
  fun_prop

omit [FiniteDimensional ℝ E] in
theorem data_mem_domain (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R) (q : AnchoredBody A H × Parameters (E := E) (ι := ι)) :
    data hin hout q ∈ NormalizedPlankBodyMinimum.domain 1 :=
  ⟨mem_univ _,mem_univ _,q.2.2.2⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- A genuine body/plank margin, expressed in support-normalized coordinates. -/
def margin (μ : Measure E) (d : ℕ)
    (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R) (q : AnchoredBody A H × Parameters (E := E) (ι := ι)) : ℝ :=
  NormalizedPlankBodyMinimum.margin μ d 1 (data hin hout q)

theorem continuous_margin (μ : Measure E) [μ.IsAddHaarMeasure] (d : ℕ) (hr : 0 < r)
    (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R) : Continuous (margin (ι := ι) μ d hin hout) :=
  (NormalizedPlankBodyMinimum.continuous_margin μ hr d 1).comp (continuous_data hin hout)

theorem margin_eq_physical (μ : Measure E) [μ.IsAddHaarMeasure] (d : ℕ) (hr : 0 < r)
    (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R) (q : AnchoredBody A H × Parameters (E := E) (ι := ι)) :
    margin μ d hin hout q = GlobalPlankBodyMinimum.margin μ (q.1.1 : Set E)
      (NormalizedPlankBodyMinimum.form (data hin hout q))
      (NormalizedPlankBodyMinimum.lo (data hin hout q))
      (NormalizedPlankBodyMinimum.hi (data hin hout q)) d 1 :=
  NormalizedPlankBodyMinimum.margin_eq_physical μ hr (data hin hout q) d 1

/-- Every strict failure in the anchored domain has a finite point-hull
failure with the same plank directions and normalized endpoints. -/
theorem exists_negative_finite_hull (μ : Measure E) [μ.IsAddHaarMeasure]
    (d : ℕ) (hr : 0 < r) (hA : A.Nonempty) (hH : Convex ℝ H) (hAH : (A : Set E) ⊆ H)
    (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R)
    {K : AnchoredBody A H} {p : Parameters (E := E) (ι := ι)}
    (hbad : margin μ d hin hout (K,p) < 0) :
    ∃ n, ∃ x : Fin n → H, margin μ d hin hout (anchoredHull A hA H hH hAH x,p) < 0 :=
  exists_negative_sample A hA H hH hAH (margin μ d hin hout)
    (continuous_margin μ d hr hin hout) hbad

/-- Positive-measure detection for any full-support parameter laws. In
particular, continuity of actual volume and relative widths is proved, rather
than left as a sampling hypothesis. Full support of the laws remains explicit. -/
theorem exists_positive_measure_failures (μ : Measure E) [μ.IsAddHaarMeasure]
    (d : ℕ) (hr : 0 < r) (hA : A.Nonempty) (hH : Convex ℝ H) (hAH : (A : Set E) ⊆ H)
    (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R)
    [MeasurableSpace (Parameters (E := E) (ι := ι))]
    (ν : ∀ n, Measure ((Fin n → H) × Parameters (E := E) (ι := ι)))
    [∀ n, (ν n).IsOpenPosMeasure]
    {K : AnchoredBody A H} {p : Parameters (E := E) (ι := ι)}
    (hbad : margin μ d hin hout (K,p) < 0) :
    ∃ n, 0 < ν n {q | margin μ d hin hout (anchoredHull A hA H hH hAH q.1,q.2) < 0} :=
  exists_positive_measure_negative_samples A hA H hH hAH (margin μ d hin hout)
    (continuous_margin μ d hr hin hout) ν hbad

/-- A mixture assigning positive weight to every finite point count has
positive failure mass. This is conditional on the explicitly full-support
laws above. No lower bound on this positive mass is asserted. -/
theorem positive_mixture_failures (μ : Measure E) [μ.IsAddHaarMeasure]
    (d : ℕ) (hr : 0 < r) (hA : A.Nonempty) (hH : Convex ℝ H) (hAH : (A : Set E) ⊆ H)
    (hin : closedBall (0 : E) r ⊆ convexHull ℝ (A : Set E))
    (hout : H ⊆ closedBall 0 R)
    [MeasurableSpace (Parameters (E := E) (ι := ι))]
    (ν : ∀ n, Measure ((Fin n → H) × Parameters (E := E) (ι := ι)))
    [∀ n, (ν n).IsOpenPosMeasure] (w : ℕ → ℝ≥0∞) (hw : ∀ n, 0 < w n)
    {K : AnchoredBody A H} {p : Parameters (E := E) (ι := ι)}
    (hbad : margin μ d hin hout (K,p) < 0) :
    0 < ∑' n, w n * ν n {q |
      margin μ d hin hout (anchoredHull A hA H hH hAH q.1,q.2) < 0} := by
  obtain ⟨n,hn⟩ := exists_positive_measure_failures μ d hr hA hH hAH hin hout ν hbad
  exact (ENNReal.mul_pos_iff.mpr ⟨hw n,hn⟩).trans_le
    (ENNReal.le_tsum (f := fun k => w k * ν k {q |
      margin μ d hin hout (anchoredHull A hA H hH hAH q.1,q.2) < 0}) n)

end Plank.QuantitativeSamplingSupport
