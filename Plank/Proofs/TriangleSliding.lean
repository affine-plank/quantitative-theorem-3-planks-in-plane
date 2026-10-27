/- Three planks on a triangle: shrink at an extreme vertex; otherwise the
side intervals give the width bound directly. -/
module
public import Plank.Proofs.TriangleSliding.WidthBound

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace SixBoundaries

/-- The cyclic normalized case remaining after the shrinking reduction. -/
theorem canonical_interior_cover_width_bound (d lo hi : Fin 3 → ℝ)
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hlo0 : ∀ i, 0 < lo i) (hlo : ∀ i, lo i ≤ d i)
    (hhi : ∀ i, d i ≤ hi i) (hhi1 : ∀ i, hi i < 1)
    (hc : ∀ l : Fin 3 → ℝ, (∀ i, 0 ≤ l i) → ∑ i, l i = 1 →
      ∃ i, lo i ≤ d i * l i + l (i + 2) ∧ d i * l i + l (i + 2) ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) := by
  have h := width_bound_strict hd0 hd1 hlo0 hlo
    (fun i => sub_pos.mpr (hhi1 i))
    (fun i => sub_le_sub_left (hhi i) 1)
    (show covers d lo (fun i => 1 - hi i) from by
      intro x hx
      simpa only [level, sub_sub_cancel] using hc x hx.1 hx.2)
  convert h using 1
  congr 1
  funext i
  ring

end SixBoundaries
