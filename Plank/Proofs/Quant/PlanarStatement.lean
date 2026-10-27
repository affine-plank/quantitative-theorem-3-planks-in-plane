/- The actual-area target for the planar quantitative campaign.
This module defines the proposition to be proved; it does not prove it.
No algebraic curvature or geometric chart hypothesis is part of the target. -/
module

public import Plank.Convex.AffineRangeWidth
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarQuantitative

open scoped BigOperators
open MeasureTheory
open Plank.Convex.DeficientHeightTilt

abbrev Point := Fin 2 → ℝ

/-- The sharp lower bound for `m` closed affine planks on a compact convex
planar set. The width in each direction is its actual affine range on `K`.
Only positive ranges and ordered plank endpoints are required. Zero-width
planks, repeated directions, boundary contacts and planks extending outside
the body's support interval are included. Lower-dimensional bodies are also
included when the stated directional ranges are positive.

The campaign's final target is `SharpPlanarBound 3`; the reviewed hand proof
establishes the cases `m = 0, 1, 2, 3` successively. Defining this proposition
is not a formal proof of any of those cases. -/
def SharpPlanarBound (m : ℕ) : Prop :=
  ∀ (K : Set Point), IsCompact K → Convex ℝ K → K.Nonempty →
    ∀ (f : Fin m → Point →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ),
      (∀ i, lo i ≤ hi i) → (∀ i, 0 < rangeWidth K (f i)) →
      (max 0 (1 - ∑ i, (hi i - lo i) / rangeWidth K (f i))) ^ 2 *
        (volume K).toReal ≤
        (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal

end Plank.PlanarQuantitative
