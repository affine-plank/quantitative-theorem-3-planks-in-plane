/- The general normed-space extreme-minimum theorem, retained for the older
interfaces. The planar proof uses the elementary finite-dimensional version. -/
module
public import Plank.Convex.FiniteExtremeMinimum
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
namespace Plank.Convex.ExtremeMinimum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous linear objective on a nonempty compact set attains its minimum
at an extreme point of the whole feasible set. -/
theorem exists_extreme_minimizer (s : Set E) (hs : IsCompact s)
    (hne : s.Nonempty) (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, IsMinOn f s x := by
  let t := (-f).toExposed s
  have he : IsExposed ℝ s t := ContinuousLinearMap.toExposed.isExposed
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hne f.continuous.continuousOn
  have hne' : t.Nonempty := by
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact neg_le_neg (hmin hy)
  obtain ⟨y, hy⟩ := (he.isCompact hs).extremePoints_nonempty hne'
  refine ⟨y, he.isExtreme.extremePoints_subset_extremePoints hy, ?_⟩
  intro z hz
  exact neg_le_neg_iff.mp (hy.1.2 z hz)

end Plank.Convex.ExtremeMinimum
