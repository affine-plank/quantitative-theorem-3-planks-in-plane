/- Fewer than six closed exterior cells leave a three-plank equality motion. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralTripleInterior
public import Plank.Proofs.Quant.PlanarCellOffsetLines
public import Plank.Proofs.Quant.PlanarLocalMinimumMotion

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.PlanarThreePlankFewCellMotion
open Plank
open Set MeasureTheory Filter PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts PlanarPositiveCellRank
open Plank.Convex.DeficientHeightTilt
open PlanarShiftedDomain (deficit deficit_apply)
open scoped BigOperators Topology

/-- The three-plank equality case of the arbitrary-count local-minimum motion.
The local minimum is supplied by the already proved quantitative bound. -/
theorem exists_motion {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p : Endpoints 3) (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (he : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hcount : (PlanarSevenNonemptyCells.nonemptyCells K f p).card < 6) :
    ∃ z : Endpoints 3, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      p+t • z ∈ interior (domain K f) ∧ budget K f (p+t • z) = budget K f p ∧
      gapArea K f (p+t • z) = (1-budget K f p)^2*(volume K).toReal := by
  exact Plank.PlanarLocalMinimumMotion.exists_motion_of_bound
    PlanarThreePlank.sharpPlanarBound_three hK hc hne hV f hW p hp hR he hcount

end Quant.PlanarThreePlankFewCellMotion

/-- info: 'Quant.PlanarThreePlankFewCellMotion.exists_motion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.PlanarThreePlankFewCellMotion.exists_motion
