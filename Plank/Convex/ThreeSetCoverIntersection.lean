/- Three closed convex sets covering a convex set have a common covered
point whenever all three clipped pairs intersect. This is the three-set
specialization of the finite convex-cover intersection theorem. -/
module
public import Plank.Convex.FiniteConvexCoverIntersection
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ThreeSetCoverIntersection
open Set

abbrev Point := Fin 3 → ℝ

/-- Pairwise intersections of three closed convex covering sets inside K
force a triple intersection inside K. No compactness, closedness, dimension,
or interior condition on K is required. -/
theorem triple_nonempty (K A B C : Set Point)
    (hK : Convex ℝ K) (hA : Convex ℝ A) (hB : Convex ℝ B) (hC : Convex ℝ C)
    (hAc : IsClosed A) (hBc : IsClosed B) (hCc : IsClosed C)
    (hcover : K ⊆ A ∪ B ∪ C)
    (hAB : (K ∩ A ∩ B).Nonempty) (hAC : (K ∩ A ∩ C).Nonempty)
    (hBC : (K ∩ B ∩ C).Nonempty) :
    (K ∩ A ∩ B ∩ C).Nonempty := by
  classical
  let F : Fin 3 → Set Point := ![A, B, C]
  have hF (i : Fin 3) : Convex ℝ (F i) := by fin_cases i <;> assumption
  have hFc (i : Fin 3) : IsClosed (F i) := by fin_cases i <;> assumption
  have hcov : ∀ x ∈ K, ∃ i ∈ (Finset.univ : Finset (Fin 3)), x ∈ F i := by
    intro x hx
    rcases hcover hx with (hx | hx) | hx
    · exact ⟨0, Finset.mem_univ _, hx⟩
    · exact ⟨1, Finset.mem_univ _, hx⟩
    · exact ⟨2, Finset.mem_univ _, hx⟩
  have hproper : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      ∃ x ∈ K, ∀ j ∈ (Finset.univ : Finset (Fin 3)), j ≠ i → x ∈ F j := by
    intro i _
    fin_cases i
    · simpa [Set.Nonempty, F, Fin.forall_fin_succ, and_assoc] using hBC
    · simpa [Set.Nonempty, F, Fin.forall_fin_succ, and_assoc] using hAC
    · simpa [Set.Nonempty, F, Fin.forall_fin_succ, and_assoc] using hAB
  have hne : K.Nonempty := hAB.mono (inter_subset_left.trans inter_subset_left)
  obtain ⟨x, hx, hxF⟩ := FiniteConvexCoverIntersection.inter_nonempty Finset.univ F K
    hne hK (fun i _ => hF i) (fun i _ => hFc i) hcov hproper
  exact ⟨x, ⟨⟨hx, hxF 0 (Finset.mem_univ _)⟩, hxF 1 (Finset.mem_univ _)⟩,
    hxF 2 (Finset.mem_univ _)⟩

end Plank.Convex.ThreeSetCoverIntersection

/-- info: 'Plank.Convex.ThreeSetCoverIntersection.triple_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.ThreeSetCoverIntersection.triple_nonempty
