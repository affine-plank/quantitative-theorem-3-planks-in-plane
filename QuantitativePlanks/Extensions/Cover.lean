/- Planar APC with genuine extended widths on arbitrary convex sets. -/
module

public import QuantitativePlanks.Extensions.Quantitative

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ExtendedCover

open Set MeasureTheory Metric Filter FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
open scoped ENNReal Topology BigOperators

/-- Planar APC with finite or infinite directional widths. Positive spans are
retained so that null-width windows in a containing hyperplane cannot cover
a lower-dimensional set for cost zero. No boundedness or volume assumption is needed. -/
theorem cover_bound {K : Set (Point 1)} (hc : Convex ℝ K)
    (f : Fin 3 → Point 1 →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < ExtendedWidth.width K (f i))
    (lo hi : Fin 3 → ℝ)
    (hcover : K ⊆ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) :
    1 ≤ ExtendedWidth.budget K f lo hi := by
  let C : ℕ → Set (Point 1) := fun n => K ∩ closedBall 0 (n : ℝ)
  have hC : Monotone C := by
    intro i j hij
    change K ∩ closedBall (0 : Point 1) (i : ℝ) ⊆ K ∩ closedBall 0 (j : ℝ)
    intro x hx
    exact ⟨hx.1, mem_closedBall.mpr ((mem_closedBall.mp hx.2).trans (Nat.cast_le.mpr hij))⟩
  have hunion : (⋃ n, C n) = K := iUnion_inter_closedBall_nat K 0
  have hb (n) : Bornology.IsBounded (C n) :=
    (isBounded_closedBall (x := (0 : Point 1)) (r := (n : ℝ))).subset inter_subset_right
  have hcC (n) : Convex ℝ (C n) := hc.inter (convex_closedBall 0 (n : ℝ))
  have hpos : ∀ᶠ n in atTop, ∀ i, 0 < ExtendedWidth.width (C n) (f i) := by
    apply eventually_all.mpr
    intro i
    have ht := ExtendedWidth.tendsto_width_iUnion C hC (f i)
    rw [hunion] at ht
    exact (tendsto_order.mp ht).1 0 (hW i)
  have hbudget := ExtendedWidth.tendsto_budget_iUnion C hC f lo (fun i => max (lo i) (hi i))
  rw [hunion, ExtendedQuantitative.budget_normalize_hi] at hbudget
  apply ge_of_tendsto hbudget
  filter_upwards [hpos] with n hn
  have hWreal (i) : 0 < Body.width (C n) (f i) := by
    have h := hn i
    rw [ExtendedWidth.width_eq_of_isBounded (hb n)] at h
    exact ENNReal.ofReal_pos.mp h
  have hcoverC : C n ⊆ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ max (lo i) (hi i)} := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx.1)
    exact mem_iUnion.mpr ⟨i, hi.1, hi.2.trans (le_max_right _ _)⟩
  have hreal := BoundedConvexBounds.cover_bound (hb n) (hcC n) f hWreal
    (lo, fun i => max (lo i) (hi i)) (fun i => le_max_left _ _) hcoverC
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_one] at h
  simpa only [ExtendedWidth.budget_eq_of_isBounded (hb n) f lo _
    (fun i => le_max_left (lo i) (hi i)) hWreal, budget] using h

end Plank.ExtendedCover

#print axioms Plank.ExtendedCover.cover_bound
