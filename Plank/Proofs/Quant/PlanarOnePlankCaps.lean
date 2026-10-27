/- The complete one-plank bound directly from the two cap inequalities. -/
module

public import Plank.Proofs.Quant.PlanarNormalization
public import Plank.Proofs.Quant.PlanarCapWindowScaling
public import Plank.Proofs.Quant.FiniteDimensionalOnePlankCaps

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOnePlankCaps

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open Plank.Convex.DeficientHeightTilt

/-- The cap bound already proves the normalized one-plank inequality,
including zero width. The unit-width case has zero target. -/
theorem unitDomainBound_one : PlanarNormalization.UnitDomainBound 1 := by
  exact FiniteDimensionalOnePlankCaps.unitDomainBound_one (d := 1)

/-- Normalization and clipping include arbitrary ordered windows and all
compact convex bodies, without using the translation proof of one plank. -/
theorem sharpPlanarBound_one : SharpPlanarBound 1 := by
  exact FiniteDimensionalOnePlankCaps.sharpBound_one (d := 1)

end Plank.PlanarOnePlankCaps

/-- info: 'Plank.PlanarOnePlankCaps.unitDomainBound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankCaps.unitDomainBound_one
/-- info: 'Plank.PlanarOnePlankCaps.sharpPlanarBound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankCaps.sharpPlanarBound_one
