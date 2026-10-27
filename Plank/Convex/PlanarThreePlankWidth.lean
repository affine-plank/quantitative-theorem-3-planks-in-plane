/- Three coordinate windows covering a normalized convex set on a positive
plane have total width at least one, by choosing supports and intersecting
the rows of a bounded sublevel polyhedron. -/
module
public import Plank.Convex.PlanarFiniteCover
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarThreePlankWidth
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- The normalized positive-plane three-plank width theorem. The convex set
need not be compact or have interior, and ordered windows may have zero width. -/
theorem width_bound (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) :=
  PlanarFrozenMinimum.width_bound K hK hbox hL hU A D hA hplane lo hi horder hcover

end Plank.Convex.PlanarThreePlankWidth

/-- info: 'Plank.Convex.PlanarThreePlankWidth.width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarThreePlankWidth.width_bound
