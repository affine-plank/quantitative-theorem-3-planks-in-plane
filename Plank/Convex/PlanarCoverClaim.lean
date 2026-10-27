/- The affine planar three-plank statement, independent of approximation arguments. -/
module
public import Plank.Convex.AffineRangeWidth
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ApproximatePlanarCover
open scoped BigOperators
open DeficientHeightTilt
abbrev Point2 := Fin 2 → ℝ
abbrev Point3 := Fin 3 → ℝ

/-- The arbitrary planar three-plank assertion, including degenerate
bodies and repeated directions whenever the three actual ranges are positive.
This is an explicit proposition supplied as a hypothesis below. -/
def PlanarCoverClaim : Prop :=
  ∀ (K : Set Point2), IsCompact K → Convex ℝ K → K.Nonempty →
    ∀ (f : Fin 3 → Point2 →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ),
      (∀ i, lo i ≤ hi i) → (∀ i, 0 < rangeWidth K (f i)) →
      (∀ p ∈ K, ∃ i, lo i ≤ f i p ∧ f i p ≤ hi i) →
      1 ≤ ∑ i, (hi i - lo i) / rangeWidth K (f i)

end Plank.Convex.ApproximatePlanarCover
