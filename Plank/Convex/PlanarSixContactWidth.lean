/- Six planar contacts give nonnegative slope slacks. The identity for
three coordinate budgets then gives the width bound directly. -/
module
public import Plank.Convex.PlanarContactWeightsCore
public import Plank.Convex.PlanarSupportWidth
@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Plank.Convex.PlanarContactWeights (Triple)
namespace Plank.Convex.PlanarSixContactWidth
open PlanarSupportMatrix

export PlanarSupportWidth (opposite_bounds support_width_bound)

/-- Six pair contacts on a positive plane suffice for the normalized width
bound. No convexity, covering, or coordinate-box assumption is used here. -/
theorem width_bound (K : Set Triple) (lo hi a b c : Triple) (D : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 < c i)
    (hwidth : ∀ i, lo i < hi i)
    (hplane : ∀ x ∈ K, (∑ i, c i * x i) = D)
    (hzero : ∀ i, ∃ x ∈ K, x i = 0) (hone : ∀ i, ∃ x ∈ K, x i = 1)
    (hL : ∀ i, ∃ x ∈ K, x i = lo i ∧ x (i + 1) = lo (i + 1))
    (hU : ∀ i, ∃ x ∈ K, x i = hi i ∧ x (i + 1) = hi (i + 1))
    (hupper : ∀ i, ∀ x ∈ K, x i + a i * x (i + 1) ≤ hi i + a i * hi (i + 1))
    (hlower : ∀ i, ∀ x ∈ K, lo i + b i * lo (i + 1) ≤ x i + b i * x (i + 1)) :
    1 ≤ ∑ i, (hi i - lo i) := by
  obtain ⟨hab, hba⟩ := PlanarContactWeights.weights_of_contacts K lo hi a b c D
    ha hb (fun i => (hc i).le) hwidth hplane hL hU hupper hlower
  have hgap := PlanarSlopeGap.gap_nonneg a b c ha hb hc hab hba
  simpa only [div_one] using support_width_bound K (fun i x => x i) lo hi a b
    (fun _ => 1) ha hb (fun i => (hwidth i).le) (fun _ => zero_lt_one)
    hzero hone hupper hlower hgap

end Plank.Convex.PlanarSixContactWidth
