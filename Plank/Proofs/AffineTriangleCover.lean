/- Three affine windows covering a three-generator hull pay its full
relative width. The normalization and scalar boundary argument are separate. -/
module
public import Plank.Proofs.AffineTriangleNormalization
public import Plank.Proofs.TriangleCoverShrinking
public import Plank.Proofs.TriangleCoverInterior
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.TriangleNormalization
open scoped BigOperators

/-- Remove an endpoint window from a deficient cover. If none exists,
every plank owns a different middle vertex, so the cyclic argument applies. -/
theorem width_bound {n : ℕ} (C : Cover n) (hn : n ≤ 3) : 1 ≤ C.width := by
  induction n with
  | zero =>
    obtain ⟨i, _⟩ := C.covered (fun j => if j = 0 then 1 else 0)
      (fun j => by split_ifs <;> norm_num) (by simp)
    exact i.elim0
  | succ n ih =>
    by_contra hs
    by_cases hbad : ∃ j, C.lo j ≤ 0 ∨ 1 ≤ C.hi j
    · obtain ⟨j, hj⟩ := hbad
      obtain ⟨D, hD⟩ := drop_bad_window C (lt_of_not_ge hs) j hj
      exact (not_le_of_gt hD) (ih D (by omega))
    · simp only [not_exists, not_or, not_le] at hbad
      exact hs (interior_width_bound C hn (fun i => (hbad i).1) (fun i => (hbad i).2))

end Plank.TriangleNormalization

namespace Plank.AffineTriangle
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The three functions need only have positive ranges on the generators.
No ambient dimension, affine independence, or compactness assumption is used. -/
theorem sum_relative_width_ge_one
    (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (hpos : ∀ k, 0 < vertexSpread v (f k)) (hle : ∀ k, lo k ≤ hi k)
    (hcover : ∀ X ∈ convexHull ℝ (Set.range v), ∃ k, lo k ≤ f k X ∧ f k X ≤ hi k) :
    1 ≤ relativeWidthSum v f lo hi := by
  obtain ⟨C, hwidth⟩ := exists_normalized_cover v f lo hi hpos hle hcover
  simpa only [hwidth] using TriangleNormalization.width_bound C (by decide)

end Plank.AffineTriangle
