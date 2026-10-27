/- A finite family of attained coordinate extrema can be retained in a compact convex subset. -/
module
public import Mathlib.Analysis.Convex.Topology
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace Plank.Convex.NormalizedCompactHull


/-- Restrict a normalized convex set to the hull of two coordinate witnesses per index. -/
theorem exists_subset {ι : Type*} [Fintype ι] (K : Set (ι → ℝ))
    (hK : Convex ℝ K) (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1) :
    ∃ T, T ⊆ K ∧ IsCompact T ∧ Convex ℝ T ∧
      (∀ i, ∃ x ∈ T, x i = 0) ∧ (∀ i, ∃ x ∈ T, x i = 1) := by
  choose pL hpL hpL0 using hL
  choose pU hpU hpU1 using hU
  let S := Set.range pL ∪ Set.range pU
  let T := convexHull ℝ S
  have hTK : T ⊆ K := convexHull_min (by
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hpL i
    · exact hpU i) hK
  refine ⟨T, hTK, ((Set.finite_range pL).union (Set.finite_range pU)).isCompact_convexHull ℝ,
    convex_convexHull ℝ S, ?_, ?_⟩
  · exact fun i => ⟨pL i, subset_convexHull ℝ S (Or.inl ⟨i, rfl⟩), hpL0 i⟩
  · exact fun i => ⟨pU i, subset_convexHull ℝ S (Or.inr ⟨i, rfl⟩), hpU1 i⟩

end Plank.Convex.NormalizedCompactHull
