/- Every physical strict counterexample enters the canonical finite-hull
proposal family. Positive sampling mass is conditional on full-support laws,
not on a claim about the finite implementation. -/
module

public import CanonicalHullNormalization
public import QuantitativeSamplingSupport
public import SameBodyPlankEncoding
public import FinitePlankAffineTransport

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.CanonicalSampling

open Set MeasureTheory FiniteHullSampling CanonicalHullNormalization
open FiniteDimensionalBodyNormalization (Point innerRadius innerRadius_pos)
open FinitePlankAffineTransport (pull)
open scoped ENNReal

variable {n : ℕ} {ι : Type*} [Fintype ι]

abbrev CanonicalBody (n : ℕ) := AnchoredBody (anchor n) (cube n)
abbrev Parameters (n : ℕ) (ι : Type*) [Fintype ι] :=
  QuantitativeSamplingSupport.Parameters (E := Point n) (ι := ι)

def margin (μ : Measure (Point n)) (d : ℕ) (q : CanonicalBody n × Parameters n ι) : ℝ :=
  QuantitativeSamplingSupport.margin μ d (ball_subset_anchor_hull n) (cube_subset_ball n) q

def hull {k : ℕ} (x : Fin k → cube n) : CanonicalBody n :=
  anchoredHull (anchor n) (anchor_nonempty n) (cube n) (convex_cube n) (anchor_subset_cube n) x

/-- Affine normalization and body-preserving plank encoding have no larger
margin in the fixed canonical domain. -/
theorem exists_parameters_le (μ : Measure (Point n)) [μ.IsAddHaarMeasure]
    {K : Set (Point n)} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0 < μ.real K)
    (f : ι → Point n →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (hW : ∀ i, 0 < Plank.Body.width K (f i)) (horder : ∀ i, a i ≤ b i)
    (d : ℕ) (hbudget : PrunedPlankCounterexample.budget K f a b ≤ 1) :
    ∃ C : CanonicalBody n, ∃ p : Parameters n ι,
      margin μ d (C,p) ≤ GlobalPlankBodyMinimum.margin μ K f a b d 1 := by
  have hfull : (interior K).Nonempty := by
    by_contra hn
    have he : interior K=∅ := not_nonempty_iff_eq_empty.mp hn
    have hs : K⊆frontier K := by rw [frontier,he,sdiff_empty]; exact subset_closure
    have hz := measure_mono_null hs (hconv.addHaar_frontier μ)
    simp [Measure.real,hz] at hV
  obtain ⟨F,C,hC⟩ := exists_affine_anchored hK hconv hfull
  let D := QuantitativeSamplingSupport.normalizedBody
    (ball_subset_anchor_hull n) (cube_subset_ball n) C
  have hw (i) : Plank.Body.width (C.1 : Set (Point n)) (pull F (f i)) =
      Plank.Body.width K (f i) := by
    rw [hC]
    exact FinitePlankAffineTransport.width_pull F K (f i)
  have hb : PrunedPlankCounterexample.budget (C.1 : Set (Point n))
      (fun i => pull F (f i)) a b = PrunedPlankCounterexample.budget K f a b := by
    rw [hC]
    exact FinitePlankAffineTransport.budget_pull F K f a b
  have hwD (i) : 0 < Plank.Body.width (D.1 : Set (Point n)) (pull F (f i)) := by
    change 0 < Plank.Body.width (C.1 : Set (Point n)) (pull F (f i))
    rw [hw]
    exact hW i
  have hbD : PrunedPlankCounterexample.budget (D.1 : Set (Point n))
      (fun i => pull F (f i)) a b ≤ 1 := by
    change PrunedPlankCounterexample.budget (C.1 : Set (Point n)) _ a b ≤ 1
    rw [hb]
    exact hbudget
  obtain ⟨q,hqD,hqdom,hqle⟩ := SameBodyPlankEncoding.exists_data_le μ (innerRadius_pos n) D
    (fun i => pull F (f i)) a b horder hwD d hbD
  let p : Parameters n ι := (q.2.1,⟨q.2.2,hqdom.2.2⟩)
  have hd : QuantitativeSamplingSupport.data
      (ball_subset_anchor_hull n) (cube_subset_ball n) (C,p) = q :=
    Prod.ext hqD.symm rfl
  refine ⟨C,p,?_⟩
  change NormalizedPlankBodyMinimum.margin μ d 1
    (QuantitativeSamplingSupport.data (ball_subset_anchor_hull n) (cube_subset_ball n) (C,p)) ≤ _
  rw [hd]
  apply hqle.trans_eq
  change GlobalPlankBodyMinimum.margin μ (C.1 : Set (Point n)) _ a b d 1 = _
  rw [hC]
  exact FinitePlankAffineTransport.margin_pull μ F K f a b d 1

/-- A physical strict failure has a strict failure in some finite point-hull
proposal family. No fixed point-count bound is asserted. -/
theorem exists_negative_finite_hull (μ : Measure (Point n)) [μ.IsAddHaarMeasure]
    {K : Set (Point n)} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0 < μ.real K)
    (f : ι → Point n →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (hW : ∀ i, 0 < Plank.Body.width K (f i)) (horder : ∀ i, a i ≤ b i)
    (hbudget : PrunedPlankCounterexample.budget K f a b ≤ 1)
    (hbad : GlobalPlankBodyMinimum.margin μ K f a b n 1 < 0) :
    ∃ k, ∃ x : Fin k → cube n, ∃ p : Parameters n ι, margin μ n (hull x,p) < 0 := by
  obtain ⟨C,p,hp⟩ := exists_parameters_le μ hK hconv hV f a b hW horder n hbudget
  obtain ⟨k,x,hx⟩ := QuantitativeSamplingSupport.exists_negative_finite_hull μ n
    (innerRadius_pos n) (anchor_nonempty n) (convex_cube n) (anchor_subset_cube n)
    (ball_subset_anchor_hull n) (cube_subset_ball n) (hp.trans_lt hbad)
  exact ⟨k,x,p,hx⟩

/-- The mass conclusion for actual strict counterexamples. The ideal law
must have full support at every point count, and every count must receive
positive weight. These are hypotheses, not claims about software draws. -/
theorem positive_mixture_of_counterexample (μ : Measure (Point n)) [μ.IsAddHaarMeasure]
    {K : Set (Point n)} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0 < μ.real K)
    (f : ι → Point n →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (hW : ∀ i, 0 < Plank.Body.width K (f i)) (horder : ∀ i, a i ≤ b i)
    (hbudget : PrunedPlankCounterexample.budget K f a b ≤ 1)
    (hbad : GlobalPlankBodyMinimum.margin μ K f a b n 1 < 0)
    [MeasurableSpace (Parameters n ι)]
    (ν : ∀ k, Measure ((Fin k → cube n) × Parameters n ι))
    [∀ k, (ν k).IsOpenPosMeasure] (w : ℕ → ℝ≥0∞) (hw : ∀ k, 0 < w k) :
    0 < ∑' k, w k * ν k {q | margin μ n (hull q.1,q.2) < 0} := by
  obtain ⟨C,p,hp⟩ := exists_parameters_le μ hK hconv hV f a b hW horder n hbudget
  exact QuantitativeSamplingSupport.positive_mixture_failures μ n (innerRadius_pos n)
    (anchor_nonempty n) (convex_cube n) (anchor_subset_cube n)
    (ball_subset_anchor_hull n) (cube_subset_ball n) ν w hw (hp.trans_lt hbad)

end Plank.CanonicalSampling
