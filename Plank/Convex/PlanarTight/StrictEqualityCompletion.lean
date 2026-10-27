/- The original-contact and strict row-C theorems close the final two representatives. -/
module
public import Plank.Convex.SameSignOriginalContacts
public import Plank.Convex.RowCStrictEquality
public import Plank.Convex.PlanarTight.StrictSameSignTriangle
public import Plank.Convex.PlanarTight.StrictCapDispatcher
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.StrictEqualityCompletion
open StrictCapSetting StrictTriangleTransport PlanarCapCaseReduction

theorem rowA : Triangular ⟨63, 0⟩ := by
  intro C hh
  have hsingle : ∀ e, SingleEmpty C.K (fun i => AffineMap.proj i) C.lo C.hi e := by
    intro e
    apply hh.1 e
    fin_cases e <;> decide
  have hcaps := SameSignCapAlgebra.empty_pair_caps_of_single_empty C.K C.lo C.hi hsingle
  have hB : (C.lo, C.hi) ∈ SameSignCapMinimum.wallSet C.K := by
    refine ⟨⟨⟨(fun i => (C.lo_pos i).le),
      (fun i => (C.lo_pos i).le.trans (C.width_pos i).le)⟩,
      ⟨(fun i => (C.width_pos i).le.trans (C.hi_lt i).le), (fun i => (C.hi_lt i).le)⟩⟩,
      Set.mem_iInter.mpr (fun i => (C.width_pos i).le), ?_⟩
    apply Set.mem_iInter.mpr
    intro x
    apply Set.mem_iInter.mpr
    intro hx
    apply Set.mem_iInter.mpr
    intro i
    constructor
    · change x i ≤ C.hi i ∨ x (SameSignCapMinimum.next i) ≤ C.hi (SameSignCapMinimum.next i)
      rw [SameSignCapPlanarWidth.next_eq]
      by_contra! he
      exact hcaps.2 i ⟨x, hx, he.1, he.2⟩
    · change C.lo i ≤ x i ∨ C.lo (SameSignCapMinimum.next i) ≤ x (SameSignCapMinimum.next i)
      rw [SameSignCapPlanarWidth.next_eq]
      by_contra! he
      exact hcaps.1 i ⟨x, hx, he.1, he.2⟩
  have hstrict : (C.lo, C.hi) ∈ SameSignCapMinimum.strictWalls :=
    Set.mem_iInter.mpr fun i => ⟨⟨C.lo_pos i, C.width_pos i⟩, C.hi_lt i⟩
  have hcontacts := SameSignOriginalContacts.upper_lower_contacts C.K C.convex C.box C.min C.max
    C.A C.D C.positive C.plane (C.lo, C.hi) hB hstrict
    (by simpa only [SameSignCapMinimum.width_apply] using C.total)
  simp only [SameSignCapPlanarWidth.next_eq] at hcontacts
  exact StrictSameSignTriangle.of_pair_contacts C hcaps.2 hcaps.1
    (fun i => (hcontacts i).1) (fun i => (hcontacts i).2)

theorem rowC : Excluded ⟨56, 3⟩ := by
  intro C hh
  have hs3 := hh.1 3 (by decide)
  have hs4 := hh.1 4 (by decide)
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  have he1 := hh.2 1 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev]
    at hs3 hs4 hs5 he0 he1
  simp at hs3 hs4 hs5 he0 he1
  have hw := RowCStrictEquality.one_lt_width_of_caps C.K C.convex C.lo C.hi
    C.lo_pos C.hi_lt C.min C.max (fun i => sub_pos.mpr (C.width_pos i))
    C.A C.D (C.positive 1).ne' C.plane
    (by rintro ⟨x, hx, h1, h2⟩; exact absurd (hs5 x hx h1) (not_le.2 h2))
    (by rintro ⟨x, hx, h1, h2⟩; exact absurd (hs3 x hx h1) (not_le.2 h2))
    (by rintro ⟨x, hx, h1, h2⟩; exact absurd (hs4 x hx h2) (not_le.2 h1))
    (by rintro ⟨x, hx, h1, h2⟩; exact absurd (he0 x hx h1) (not_le.2 h2))
    (by rintro ⟨x, hx, h1, h2⟩; exact absurd (he1 x hx h2) (not_le.2 h1))
  rw [C.total] at hw
  exact lt_irrefl 1 hw

/-- Every strict positive equality cover on a positive coordinate plane
has an exact nondegenerate triangle body. There are no residual cap hypotheses. -/
theorem triangle (C : Setting) : TriangleBody C.K := StrictCapDispatcher.triangle rowA rowC C

theorem normal (C : Setting) :
    StrictTriangleClassification.Normal C.K (fun i => AffineMap.proj i) C.lo C.hi :=
  StrictCapDispatcher.normal rowA rowC C

end Plank.Convex.PlanarTight.StrictEqualityCompletion

/-- info: 'Plank.Convex.PlanarTight.StrictEqualityCompletion.triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictEqualityCompletion.triangle

/-- info: 'Plank.Convex.PlanarTight.StrictEqualityCompletion.normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictEqualityCompletion.normal
