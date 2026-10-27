/- The common root-margin minimum proves the two-plank case: five cells
are impossible, and the zero-gap branch is an elementary two-window cover. -/
module

public import Plank.Proofs.Quant.PlanarMinimumCompletion
public import Plank.Proofs.Quant.FiniteDimensionalTwoPlank
public import Plank.Convex.TwoAffineWindows

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarRootTwoPlank

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt

/-- The elementary two-window covering theorem, without the qualitative
three-plank theorem, expressed in normalized endpoint coordinates. -/
theorem cover_budget_normalized {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (p : Endpoints 2) (hp : p ∈ domain K f)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  exact FiniteDimensionalTwoPlank.cover_budget_normalized hK hc hne f hnorm hunit p hp hcover

/-- A root-margin minimum either covers the body below cost one or has five
closed exterior cells. The elementary two-window bound and the four possible
sign patterns exclude these two alternatives. -/
theorem sharpPlanarBound_two : SharpPlanarBound 2 := by
  exact FiniteDimensionalTwoPlank.sharpBound_two (d := 1)

end Plank.PlanarRootTwoPlank

#print axioms Plank.PlanarRootTwoPlank.cover_budget_normalized
#print axioms Plank.PlanarRootTwoPlank.sharpPlanarBound_two
