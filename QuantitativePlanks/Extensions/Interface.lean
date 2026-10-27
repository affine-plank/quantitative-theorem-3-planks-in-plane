/- Normalize positive-width planks for the small public theorem interface. -/
module
public import QuantitativePlanks.Extensions.Cover

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Plank.AffinePlankBounds

private theorem linear_ne_zero {d : ℕ} (f : (Fin d → ℝ) →ᵃ[ℝ] ℝ)
    (h : ∃ x y, f x ≠ f y) : f.linear ≠ 0 := by
  intro hz
  obtain ⟨c, rfl⟩ := f.linear_eq_zero_iff_exists_const.mp hz
  obtain ⟨x, y, hxy⟩ := h
  exact hxy rfl

/-- A normalized covering bound, including zero or infinite directional spans. -/
theorem planar_cover (K : Set (Fin 2 → ℝ)) (convex : Convex ℝ K)
    (f : Fin 3 → (Fin 2 → ℝ) →ᵃ[ℝ] ℝ)
    (covers : K ⊆ ⋃ i, {x | 0 ≤ f i x ∧ f i x ≤ 1}) :
    1 ≤ ∑ i, 1 / Metric.ediam (f i '' K) := by
  by_cases positive : ∀ i, 0 < ExtendedWidth.width K (f i)
  · simpa only [ExtendedWidth.budget, ExtendedWidth.width, sub_zero,
      ENNReal.ofReal_one] using
      ExtendedCover.cover_bound convex f positive (fun _ => 0) (fun _ => 1) covers
  · obtain ⟨i, hi⟩ := not_forall.mp positive
    have zero : Metric.ediam (f i '' K) = 0 :=
      le_antisymm (le_of_not_gt hi) bot_le
    calc
      1 ≤ 1 / Metric.ediam (f i '' K) := by simp [zero]
      _ ≤ ∑ j, 1 / Metric.ediam (f j '' K) :=
        Finset.single_le_sum
          (f := fun j : Fin 3 => (1 : ℝ≥0∞) / Metric.ediam (f j '' K))
          (fun _ _ => bot_le) (Finset.mem_univ i)

/-- The full noncompact planar bound with each plank normalized to `[0,1]`. -/
theorem planar_quantitative (K : Set (Fin 2 → ℝ)) (convex : Convex ℝ K)
    (f : Fin 3 → (Fin 2 → ℝ) →ᵃ[ℝ] ℝ) (nonconstant : ∀ i, ∃ x y, f i x ≠ f i y) :
    (1 - ∑ i, 1 / Metric.ediam (f i '' K))^2 * volume K ≤
      volume (K \ ⋃ i, {x | 0 ≤ f i x ∧ f i x ≤ 1}) := by
  simpa only [ExtendedWidth.budget, ExtendedWidth.width, sub_zero,
    ENNReal.ofReal_one] using
    ExtendedQuantitative.planar_three convex f
      (fun i => linear_ne_zero (f i) (nonconstant i)) (fun _ => 0) (fun _ => 1)

/-- The full noncompact two-plank bound in dimension `d`. -/
theorem two_planks (d : ℕ) (K : Set (Fin d → ℝ)) (convex : Convex ℝ K)
    (f : Fin 2 → (Fin d → ℝ) →ᵃ[ℝ] ℝ) (nonconstant : ∀ i, ∃ x y, f i x ≠ f i y) :
    (1 - ∑ i, 1 / Metric.ediam (f i '' K))^d * volume K ≤
      volume (K \ ⋃ i, {x | 0 ≤ f i x ∧ f i x ≤ 1}) := by
  cases d with
  | zero =>
    obtain ⟨x, y, hxy⟩ := nonconstant 0
    exact (hxy (congrArg (f 0) (Subsingleton.elim x y))).elim
  | succ n =>
    simpa only [ExtendedWidth.budget, ExtendedWidth.width, sub_zero,
      ENNReal.ofReal_one] using
      ExtendedQuantitative.two_planks convex f
        (fun i => linear_ne_zero (f i) (nonconstant i)) (fun _ => 0) (fun _ => 1)

end Plank.AffinePlankBounds
