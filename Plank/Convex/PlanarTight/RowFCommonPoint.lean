/- Discharge the plane-corner premise of row F for actual tight covers. -/
module
public import Plank.Convex.PlanarTight.RowF
public import Plank.Convex.PlanarTight.CommonPoint
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.RowF
open RowFCapAlgebra

/-- The row-F pattern cannot occur in a positive internal tight cover in
three distinct planar directions. The common-point theorem supplies the
plane-corner condition from the original cover, at equality. -/
theorem not_tight_of_cover (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1) (hwidth : ∀ i, lo i < hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1)
    (hmix21 : ¬ ∃ x ∈ K, hi 2 < x 2 ∧ x 1 < lo 1)
    (hmix10 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ hi 1 < x 1) :
    (∑ i, (hi i - lo i)) ≠ 1 := by
  intro hsum
  have hb := CommonPoint.plane_box_bounds K hK hbox hL hU lo hi A D hA
    hplane hwidth hlo hhi hcover hsum
  exact not_tight_of_caps K hK hL hU lo hi A D hA hplane hlo hhi hwidth
    hb.1 hcapU01 hmix01 hmix21 hmix10 hsum

end Plank.Convex.PlanarTight.RowF

/-- info: 'Plank.Convex.PlanarTight.RowF.not_tight_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowF.not_tight_of_cover
