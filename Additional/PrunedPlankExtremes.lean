/- Outside finitely many closed convex covered pieces, only the retained support points can be extreme. -/
module

public import SupportPruningGeometry
public import FiniteConvexUnion
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Data.Set.Card

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PrunedPlankExtremes

open Set SupportPruningGeometry

variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [Fintype κ]

theorem compact_generating_hull {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (S : κ → Set E) (hS : ∀ i, IsClosed (S i)) (hSc : ∀ i, Convex ℝ (S i))
    (P Q : ι → E) :
    IsCompact (convexHull ℝ ((K∩⋃ i, S i)∪range P∪range Q)) := by
  have hc : IsCompact (convexHull ℝ (K∩⋃ i, S i)) := by
    rw [inter_iUnion]
    exact FiniteConvexUnion.compact_hull_iUnion _ (fun i => hK.inter_right (hS i))
      (fun i => hconv.inter (hSc i))
  exact FiniteConvexUnion.compact_hull_union_of_hulls
    (FiniteConvexUnion.compact_hull_union_of_hulls hc ((finite_range P).isCompact_convexHull ℝ))
    ((finite_range Q).isCompact_convexHull ℝ)

/-- For a finite union of closed convex pieces the closure in pruning is redundant. -/
theorem prune_eq_hull {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (S : κ → Set E) (hS : ∀ i, IsClosed (S i)) (hSc : ∀ i, Convex ℝ (S i))
    (P Q : ι → E) :
    prune K (⋃ i, S i) P Q=convexHull ℝ ((K∩⋃ i, S i)∪range P∪range Q) :=
  (compact_generating_hull hK hconv S hS hSc P Q).isClosed.closure_eq

/-- Every uncovered extreme point is one of the chosen support points. -/
theorem uncovered_extremes_subset {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (S : κ → Set E) (hS : ∀ i, IsClosed (S i)) (hSc : ∀ i, Convex ℝ (S i))
    (P Q : ι → E) :
    (prune K (⋃ i, S i) P Q).extremePoints ℝ\(⋃ i, S i)⊆range P∪range Q := by
  intro x hx
  rw [prune_eq_hull hK hconv S hS hSc P Q] at hx
  rcases extremePoints_convexHull_subset hx.1 with (hcover | hp) | hq
  · exact (hx.2 hcover.2).elim
  · exact Or.inl hp
  · exact Or.inr hq

theorem uncovered_extremes_finite {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (S : κ → Set E) (hS : ∀ i, IsClosed (S i)) (hSc : ∀ i, Convex ℝ (S i))
    (P Q : ι → E) :
    ((prune K (⋃ i, S i) P Q).extremePoints ℝ\(⋃ i, S i)).Finite :=
  ((finite_range P).union (finite_range Q)).subset
    (uncovered_extremes_subset hK hconv S hS hSc P Q)

end Plank.PrunedPlankExtremes

#print axioms Plank.PrunedPlankExtremes.compact_generating_hull
#print axioms Plank.PrunedPlankExtremes.prune_eq_hull
#print axioms Plank.PrunedPlankExtremes.uncovered_extremes_subset
#print axioms Plank.PrunedPlankExtremes.uncovered_extremes_finite
