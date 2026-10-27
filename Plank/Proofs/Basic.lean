module
/-
# Proofs/Basic — elementary plane algebra

Compatibility re-export.  The shared toolbox of the mirror tree — bilinearity of `dot`, the
two-dimensional perpendicularity dichotomy, and the determinant form of
non-collinearity.  Nothing here is specific to planks.

This file is not the mirror of a topic file (`Plank.Core` has none — it
is definitions only, guard G1); it is the mirror tree's own prelude.
-/
public import Plank.Core
public import Plank.Proofs.PlaneBasic

@[expose] public section

-- Every declaration formerly here now lives in `Plank.Proofs.PlaneBasic`
-- (namespace `Proofs.Basic`, unchanged names and statements); importing this
-- module still provides them together with `Plank.Core`.

end
