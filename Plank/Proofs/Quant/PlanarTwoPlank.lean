/- The full sharp two-plank quantitative theorem for arbitrary planar convex bodies. -/
module

public import Plank.Proofs.Quant.PlanarRootTwoPlank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTwoPlank

open PlanarQuantitative
open Plank.Convex.DeficientHeightTilt

/-- Two arbitrary closed planks leave at least the squared positive relative
width deficit times the body's area. Parallel directions, zero-width planks,
external windows and zero-area bodies are included. -/
theorem sharpPlanarBound_two : SharpPlanarBound 2 :=
  PlanarRootTwoPlank.sharpPlanarBound_two

end Plank.PlanarTwoPlank
