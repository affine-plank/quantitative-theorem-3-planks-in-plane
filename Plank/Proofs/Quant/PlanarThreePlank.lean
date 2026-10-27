/- The full sharp three-plank quantitative theorem for arbitrary planar convex bodies. -/
module

public import Plank.Proofs.Quant.PlanarRelationPerturbation

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarThreePlank

open PlanarQuantitative
open Plank.Convex.DeficientHeightTilt

/-- Three arbitrary closed planks leave at least the squared positive
relative width deficit times the body's area. Every hypothesis is part of
the original geometric statement; no chart, slope, matrix or approximation
assumption remains. -/
theorem sharpPlanarBound_three : SharpPlanarBound 3 :=
  PlanarRelationPerturbation.sharpPlanarBound_three

end Plank.PlanarThreePlank
