/- A finite union of compact convex sets has compact convex hull. -/
module

public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic

@[expose] public section
set_option autoImplicit false

namespace Plank.FiniteConvexUnion

open Set

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_join {S T : Set E} (hS : IsCompact S) (hT : IsCompact T) :
    IsCompact (convexJoin ℝ S T) := by
  have he : convexJoin ℝ S T =
      (fun p : ℝ × E × E => (1-p.1)•p.2.1+p.1•p.2.2) '' (Icc 0 1 ×ˢ (S ×ˢ T)) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨a,ha,b,hb,hx⟩ := mem_convexJoin.mp hx
      rw [segment_eq_image] at hx
      obtain ⟨t,ht,rfl⟩ := hx
      exact ⟨(t,a,b),⟨ht,ha,hb⟩,rfl⟩
    · rintro ⟨⟨t,a,b⟩,⟨ht,ha,hb⟩,rfl⟩
      apply mem_convexJoin.mpr
      refine ⟨a,ha,b,hb,?_⟩
      rw [segment_eq_image]
      exact ⟨t,ht,rfl⟩
  rw [he]
  exact (isCompact_Icc.prod (hS.prod hT)).image (by fun_prop)

theorem compact_hull_union {S T : Set E} (hS : IsCompact S) (hT : IsCompact T)
    (hSc : Convex ℝ S) (hTc : Convex ℝ T) : IsCompact (convexHull ℝ (S∪T)) := by
  rcases S.eq_empty_or_nonempty with rfl | hSn
  · simpa only [empty_union,hTc.convexHull_eq] using hT
  rcases T.eq_empty_or_nonempty with rfl | hTn
  · simpa only [union_empty,hSc.convexHull_eq] using hS
  rw [hSc.convexHull_union hTc hSn hTn]
  exact compact_join hS hT

theorem compact_hull_union_of_hulls {S T : Set E}
    (hS : IsCompact (convexHull ℝ S)) (hT : IsCompact (convexHull ℝ T)) :
    IsCompact (convexHull ℝ (S∪T)) := by
  rw [← convexHull_convexHull_union_left,← convexHull_convexHull_union_right]
  exact compact_hull_union hS hT (convex_convexHull _ _) (convex_convexHull _ _)

/-- No dimension bound is needed: there are finitely many compact convex pieces. -/
theorem compact_hull_biUnion (s : Finset ι) (S : ι → Set E)
    (hS : ∀ i∈s, IsCompact (S i)) (hSc : ∀ i∈s, Convex ℝ (S i)) :
    IsCompact (convexHull ℝ (⋃ i∈s, S i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    apply compact_hull_union_of_hulls
    · rw [(hSc i (Finset.mem_insert_self _ _)).convexHull_eq]
      exact hS i (Finset.mem_insert_self _ _)
    · exact ih (fun j hj => hS j (Finset.mem_insert_of_mem hj))
        (fun j hj => hSc j (Finset.mem_insert_of_mem hj))

theorem compact_hull_iUnion [Fintype ι] (S : ι → Set E)
    (hS : ∀ i, IsCompact (S i)) (hSc : ∀ i, Convex ℝ (S i)) :
    IsCompact (convexHull ℝ (⋃ i, S i)) := by
  simpa only [Finset.mem_univ,iUnion_true] using
    compact_hull_biUnion Finset.univ S (fun i _ => hS i) (fun i _ => hSc i)

end Plank.FiniteConvexUnion

#print axioms Plank.FiniteConvexUnion.compact_join
#print axioms Plank.FiniteConvexUnion.compact_hull_union
#print axioms Plank.FiniteConvexUnion.compact_hull_union_of_hulls
#print axioms Plank.FiniteConvexUnion.compact_hull_biUnion
#print axioms Plank.FiniteConvexUnion.compact_hull_iUnion
