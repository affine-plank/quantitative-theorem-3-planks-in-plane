/- The three-plank theorem for compact convex planar bodies, assembled from the extreme-cover
argument (the normalized positive-plane width bound) and the two bridges: to arbitrary affine
three-plank covers, and to the conjecture statement in the Euclidean plane. -/
module
public import Plank.Convex.PlanarThreePlankWidth
public import Plank.Convex.PlanarDirectBridge
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarThreePlankTheorem

/-- The normalized positive-plane width bound follows from an extreme cover. -/
theorem normalizedPlaneClaim : ThreePlankPlaneReduction.NormalizedPlaneClaim :=
  PlanarThreePlankWidth.width_bound

/-- Three planks of positive range covering a compact convex planar body have total relative
width at least one, in affine-functional form. -/
theorem planarCoverClaim : ApproximatePlanarCover.PlanarCoverClaim :=
  ThreePlankPlaneReduction.planar_of_normalized normalizedPlaneClaim

/-- The affine plank conjecture for three planks in the Euclidean plane: a convex body with
nonempty interior covered by three planks receives total relative width at least one. -/
theorem conjectureFor_plane_three : Bang.ConjectureFor (EuclideanSpace ℝ (Fin 2)) 3 :=
  PlanarConjectureBridge.conjectureFor_three_of_normalized normalizedPlaneClaim

end Plank.Convex.PlanarThreePlankTheorem

/-- info: 'Plank.Convex.PlanarThreePlankTheorem.planarCoverClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarThreePlankTheorem.planarCoverClaim

/-- info: 'Plank.Convex.PlanarThreePlankTheorem.conjectureFor_plane_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarThreePlankTheorem.conjectureFor_plane_three
