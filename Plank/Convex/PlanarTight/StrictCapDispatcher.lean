/- Exhaustive strict equality dispatch through the eight cap representatives. -/
module
public import Plank.Convex.PlanarTight.StrictRepresentativeExclusions
public import Plank.Convex.PlanarTight.StrictCyclicTriangle
public import Plank.Convex.PlanarTight.StrictTriangleTransport
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.StrictCapDispatcher
open StrictCapSetting StrictTriangleTransport PlanarCapPatterns

/-- A direct finite certificate uses the same cap action as the geometric
transport theorem. -/
theorem exists_pull (p : Pattern) (hp : p ∈ patterns) :
    ∃ j : Fin 8, ∃ r : Fin 6, ∃ reverse : Bool,
      PlanarCapSymmetry.Pulls p (representatives.get j) r reverse := by
  simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> decide

/-- Once the two remaining representative lemmas are supplied, every
positive strictly internal equality cover has an exact triangle body. -/
theorem triangle (hA : Triangular ⟨63, 0⟩) (hC : Excluded ⟨56, 3⟩)
    (C : Setting) : TriangleBody C.K := by
  have hr (j : Fin 8) : Triangular (representatives.get j) := by
    fin_cases j
    · exact hA
    · intro C hh
      exact (StrictRepresentativeExclusions.rowB C hh).elim
    · intro C hh
      exact (hC C hh).elim
    · intro C hh
      exact (StrictRepresentativeExclusions.rowD C hh).elim
    · intro C hh
      exact (StrictRepresentativeExclusions.rowE C hh).elim
    · intro C hh
      exact (StrictRepresentativeExclusions.rowF C hh).elim
    · exact StrictCyclicTriangle.rowG
    · intro C hh
      exact (StrictRepresentativeExclusions.rowH C hh).elim
  obtain ⟨p, hp, hh⟩ := PlanarCapCaseReduction.exists_cap_pattern_convex C.K C.convex
    (fun i => AffineMap.proj i) C.A C.D C.positive C.plane C.lo C.hi C.covered
  obtain ⟨j, r, reverse, hpr⟩ := exists_pull p hp
  exact triangular_of_pulls p (representatives.get j) r reverse hpr (hr j) C hh

theorem normal (hA : Triangular ⟨63, 0⟩) (hC : Excluded ⟨56, 3⟩)
    (C : Setting) :
    StrictTriangleClassification.Normal C.K (fun i => AffineMap.proj i) C.lo C.hi :=
  normal_of_triangle C (triangle hA hC C)

end Plank.Convex.PlanarTight.StrictCapDispatcher

/-- info: 'Plank.Convex.PlanarTight.StrictCapDispatcher.exists_pull' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictCapDispatcher.exists_pull

/-- info: 'Plank.Convex.PlanarTight.StrictCapDispatcher.triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictCapDispatcher.triangle

/-- info: 'Plank.Convex.PlanarTight.StrictCapDispatcher.normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictCapDispatcher.normal
