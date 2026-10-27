/- Quantitative bounds for arbitrary convex sets of finite volume. -/
module

public import QuantitativePlanks.Extensions.BoundedConvex
public import ResearchFormalized.Convex.FiniteMeasure

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ConvexSetQuantitative

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalInductionBoundary
open scoped BigOperators ENNReal

/-- In the positive-volume case, nonconstant affine forms automatically have
positive directional width. No convexity or closedness is needed for this fact. -/
theorem width_pos_of_measure_pos {d : ℕ} {K : Set (Point d)}
    (hK : Bornology.IsBounded K) (hV : 0 < volume K)
    (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) : 0 < Body.width K f := by
  have hne : K.Nonempty := by
    by_contra h
    simpa [not_nonempty_iff_eq_empty.mp h] using hV
  obtain ⟨a, ha⟩ := hne
  have hcompact := Metric.isCompact_of_isClosed_isBounded isClosed_closure hK.closure
  by_contra! hW
  have hconst (x) (hx : x ∈ K) : f x = f a := by
    have hxa := Body.sub_le_width hcompact (continuous_form f)
      (subset_closure hx) (subset_closure ha)
    have hax := Body.sub_le_width hcompact (continuous_form f)
      (subset_closure ha) (subset_closure hx)
    rw [Body.width_closure hK] at hxa hax
    linarith
  have hnull : volume K = 0 :=
    measure_mono_null (fun x hx => hconst x hx) (measure_level_zero f hf (f a))
  exact hV.ne' hnull

/-- Compactness, closedness, boundedness, nonemptiness and positive directional
width hypotheses can all be omitted from the public quantitative statement.
The finite-volume hypothesis gives a meaningful real-volume interpretation;
nonconstant affine forms express that the windows are genuine planks. -/
theorem sharpBound_of_finite_volume {d m : ℕ} (hbound : SharpBound d m)
    {K : Set (Point d)} (hc : Convex ℝ K) (hfin : volume K ≠ ∞)
    (f : Fin m → Point d →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin m → ℝ) (horder : ∀ i, lo i ≤ hi i) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^(d+1) *
      (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal := by
  by_cases hz : volume K = 0
  · simp only [hz, ENNReal.toReal_zero, mul_zero]
    exact ENNReal.toReal_nonneg
  · have hV : 0 < volume K := pos_iff_ne_zero.mpr hz
    have hb := ResearchFormalized.ConvexFiniteMeasure.isBounded_of_measure_pos_ne_top
      volume hc hV hfin
    exact BoundedConvexBounds.sharpBound_of_isBounded hbound hb hc f lo hi horder
      (fun i => width_pos_of_measure_pos hb hV (f i) (hf i))

/-- Three-plank planar QAPC for every finite-volume convex set, including
nonclosed sets and sets of zero area. -/
theorem planar_three {K : Set (Point 1)} (hc : Convex ℝ K) (hfin : volume K ≠ ∞)
    (f : Fin 3 → Point 1 →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin 3 → ℝ) (horder : ∀ i, lo i ≤ hi i) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^2 * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal :=
  sharpBound_of_finite_volume CoveringFirstQuantitative.sharpBound_three hc hfin f hf lo hi horder

/-- Two-plank QAPC for every finite-volume convex set in every positive dimension. -/
theorem two_planks {d : ℕ} {K : Set (Point d)} (hc : Convex ℝ K) (hfin : volume K ≠ ∞)
    (f : Fin 2 → Point d →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin 2 → ℝ) (horder : ∀ i, lo i ≤ hi i) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^(d+1) * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal :=
  sharpBound_of_finite_volume FiniteDimensionalTwoPlank.sharpBound_two hc hfin f hf lo hi horder

/-- The proportion formulation uses one positive-real-volume condition, which
expresses exactly finite positive volume. The multiplicative variants above
additionally preserve zero-volume cases. -/
theorem proportion {d m : ℕ} (hbound : SharpBound d m)
    {K : Set (Point d)} (hc : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point d →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin m → ℝ) (horder : ∀ i, lo i ≤ hi i) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^(d+1) ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal /
        (volume K).toReal := by
  apply (le_div_iff₀ hV).mpr
  exact sharpBound_of_finite_volume hbound hc
    (ENNReal.toReal_pos_iff.mp hV).2.ne f hf lo hi horder

end Plank.ConvexSetQuantitative

#print axioms Plank.ConvexSetQuantitative.planar_three
#print axioms Plank.ConvexSetQuantitative.two_planks
#print axioms Plank.ConvexSetQuantitative.proportion
