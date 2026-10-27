/- Public APC/QAPC wrappers for bounded convex sets, without closedness. -/
module

public import QuantitativePlanks.Proof
public import QuantitativePlanks.Extensions.Closure

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.BoundedConvexBounds

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalInductionBoundary
open scoped BigOperators

/-- Any proved compact-body QAPC extends to all bounded convex sets, including
the empty set and sets of zero volume. -/
theorem sharpBound_of_isBounded {d m : ℕ} (hbound : SharpBound d m)
    {K : Set (Point d)} (hK : Bornology.IsBounded K) (hc : Convex ℝ K)
    (f : Fin m → Point d →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < Body.width K (f i)) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^(d+1) *
      (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal := by
  by_cases hne : K.Nonempty
  · have h := hbound (closure K)
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure hK.closure)
      hc.closure (hne.mono subset_closure) f lo hi horder
      (fun i => by simpa only [Body.width_closure hK] using hW i)
    simpa only [Body.width_closure hK, ConvexClosure.measure_closure volume hc,
      ConvexClosure.measure_closure_sdiff volume hc] using h
  · simp [not_nonempty_iff_eq_empty.mp hne]

/-- A closure-based planar covering wrapper for bounded convex sets, without
closedness or explicit nonemptiness. Zero plank widths and repeated directions remain allowed. -/
theorem cover_bound {K : Set (Point 1)}
    (hK : Bornology.IsBounded K) (hc : Convex ℝ K)
    (f : Fin 3 → Point 1 →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (p : Endpoints (Fin 3)) (horder : ∀ i, p.1 i ≤ p.2 i)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  have hclosed : IsClosed (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :=
    isClosed_iUnion_of_finite fun i => (isClosed_le continuous_const (continuous_form (f i))).inter
      (isClosed_le (continuous_form (f i)) continuous_const)
  have h := CoveringFirstPlanar.cover_bound
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hK.closure)
    hc.closure ((Body.nonempty_of_width_pos (hW 0)).mono subset_closure)
    f (fun i => by simpa only [Body.width_closure hK] using hW i) p horder
    (closure_minimal hcover hclosed)
  simpa only [budget, Body.width_closure hK] using h

/-- Three-plank planar QAPC for every bounded convex set. -/
theorem planar_three {K : Set (Point 1)}
    (hK : Bornology.IsBounded K) (hc : Convex ℝ K)
    (f : Fin 3 → Point 1 →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < Body.width K (f i)) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^2 * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal :=
  sharpBound_of_isBounded CoveringFirstQuantitative.sharpBound_three hK hc f lo hi horder hW

/-- Two-plank QAPC in every positive dimension for every bounded convex set. -/
theorem two_planks {d : ℕ} {K : Set (Point d)}
    (hK : Bornology.IsBounded K) (hc : Convex ℝ K)
    (f : Fin 2 → Point d →ᵃ[ℝ] ℝ) (lo hi : Fin 2 → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < Body.width K (f i)) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^(d+1) * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal :=
  sharpBound_of_isBounded FiniteDimensionalTwoPlank.sharpBound_two hK hc f lo hi horder hW

end Plank.BoundedConvexBounds

#print axioms Plank.BoundedConvexBounds.cover_bound
#print axioms Plank.BoundedConvexBounds.sharpBound_of_isBounded
#print axioms Plank.BoundedConvexBounds.planar_three
#print axioms Plank.BoundedConvexBounds.two_planks
