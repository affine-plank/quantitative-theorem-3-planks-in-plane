/- A nonconstant affine function has positive bounded range on a set with interior. -/
module
public import Plank.Convex.AffineRangeWidth
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Instances.ENNReal.Lemmas
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Plank.Convex.AffineRangeInterior
open DeficientHeightTilt (rangeWidth)

/-- Nonempty interior prevents a nonconstant affine function from having zero range. -/
theorem positive_width {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK : (interior K).Nonempty) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∃ x y, f x ≠ f y) (hb : Bornology.IsBounded (f '' K)) :
    0 < rangeWidth K f := by
  rw [rangeWidth, Body.width, ← Real.diam_eq hb]
  apply Metric.diam_pos ?_ hb
  by_contra hn
  have hsub := Set.not_nontrivial_iff.mp hn
  obtain ⟨p, hp⟩ := hK.mono interior_subset
  have hspan : affineSpan ℝ K = ⊤ := by
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top hK]
    exact affineSpan_mono ℝ interior_subset
  have heq : f = AffineMap.const ℝ E (f p) :=
    AffineMap.ext_on hspan (fun x hx => hsub ⟨x, hx, rfl⟩ ⟨p, hp, rfl⟩)
  obtain ⟨x, y, hxy⟩ := hf
  exact hxy (by rw [heq]; rfl)

end Plank.Convex.AffineRangeInterior
