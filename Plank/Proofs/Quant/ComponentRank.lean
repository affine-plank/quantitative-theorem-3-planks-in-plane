/- Algebraic client of convex gap-component area quasiconcavity.
Brunn--Minkowski, the geometric midpoint inclusion, and area derivatives
are external inputs, not assertions of this module. -/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section

namespace Plank.ComponentRank

/-- On a direction in the kernel of a quadratic's linear term, the two
opposite area values agree. A midpoint area comparison makes its curvature
nonpositive. The geometric midpoint comparison is an explicit input. -/
theorem curvature_nonpos_of_midpoint (a b t : ℝ) (ht : t ≠ 0)
    (hmid : min (a+b*t^2) (a+b*t^2) ≤ a) : b ≤ 0 := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  rw [min_self] at hmid
  by_contra hn
  have hp := mul_pos (lt_of_not_ge hn) ht2
  linarith

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- If every component's curvature is nonpositive on its gradient kernel,
strict positivity of the summed curvature forces the component gradients
to separate vectors. No geometric meaning is silently imposed on `curvature`. -/
theorem gradient_map_injective
    (gradient : ι → E →ₗ[ℝ] ℝ) (curvature : ι → E → ℝ)
    (hkernel : ∀ i v, gradient i v = 0 → curvature i v ≤ 0)
    (hpos : ∀ v, v ≠ 0 → 0 < ∑ i, curvature i v) :
    Function.Injective (LinearMap.pi gradient) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  by_contra hn
  have hle : ∑ i, curvature i v ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply hkernel i v
    exact congrFun hv i
  exact (not_lt_of_ge hle) (hpos v hn)

theorem dimension_le_components
    (gradient : ι → E →ₗ[ℝ] ℝ) (curvature : ι → E → ℝ)
    (hkernel : ∀ i v, gradient i v = 0 → curvature i v ≤ 0)
    (hpos : ∀ v, v ≠ 0 → 0 < ∑ i, curvature i v) :
    Module.finrank ℝ E ≤ Fintype.card ι := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (gradient_map_injective gradient curvature hkernel hpos)
  simpa only [Module.finrank_pi] using h

/-- With two endpoint variables per plank, at least twice as many positive
gap components are required by the abstract curvature hypotheses. -/
theorem endpoint_count (n : ℕ)
    (gradient : ι → (Fin (2*n) → ℝ) →ₗ[ℝ] ℝ)
    (curvature : ι → (Fin (2*n) → ℝ) → ℝ)
    (hkernel : ∀ i v, gradient i v = 0 → curvature i v ≤ 0)
    (hpos : ∀ v, v ≠ 0 → 0 < ∑ i, curvature i v) :
    2*n ≤ Fintype.card ι := by
  simpa only [Module.finrank_pi, Fintype.card_fin] using
    dimension_le_components gradient curvature hkernel hpos

/-- A concave residual slice has right derivative no larger than its left
derivative. The two inner endpoints of separated parallel windows cannot
both have the positive diagonal curvature required by the margin. -/
theorem no_parallel_inner_pair (V left right : ℝ)
    (hV : 0 ≤ V) (hconcave : right ≤ left)
    (hupper : 0 < -left-2*V) (hlower : 0 < right-2*V) : False := by
  linarith

end Plank.ComponentRank
