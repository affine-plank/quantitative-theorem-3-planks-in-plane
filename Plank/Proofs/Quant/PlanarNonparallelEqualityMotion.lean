/- Local equality motion in the remaining three-direction stratum. -/
module

public import Plank.Proofs.Quant.PlanarFewCellEqualityLine
public import Plank.Proofs.Quant.PlanarSevenNonemptyCells
public import Plank.Proofs.Quant.PlanarTripleEndpointBoundary

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarNonparallelEqualityMotion

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarAffineEquality
open PlanarDirectionDerivatives
open Plank.Convex.DeficientHeightTilt

/-- Every positive-deficit equality on a normalized compact convex body
outside the four-point class has a nonzero local equality motion. The
endpoint-interiority and at-most-six-nonempty-cell conditions are derived.
The positive direction does not increase total relative width. -/
theorem exists_local_motion {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints 3) (hp : p ∈ domain K f)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (he : Equality K f p.1 p.2)
    (hnf : ¬∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) :
    ∃ z : Endpoints 3, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      p+t • z ∈ interior (domain K f) ∧
      gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal ∧
      (0 ≤ t → budget K f (p+t • z) ≤ budget K f p) := by
  have heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal := by
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
    rwa [max_eq_right (sub_pos.mpr hR1).le] at he
  have hs := PlanarTripleEndpointBoundary.strict_of_not_four hK hc hne hV f hW
    hnorm hL hU p hp hR0 hR1 heq hnf
  have hcount := PlanarSevenNonemptyCells.at_most_six_of_not_four hK hc hne hV f p
    hW (fun i => (hs i).2.1) hpairs hR1 he hnf
  exact PlanarFewCellEqualityLine.exists_local_motion hK hc hne hV f hW p
    (mem_interior_of_strict K f hs hR1) hR1 heq hcount

end Plank.PlanarNonparallelEqualityMotion

/-- info: 'Plank.PlanarNonparallelEqualityMotion.exists_local_motion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarNonparallelEqualityMotion.exists_local_motion
