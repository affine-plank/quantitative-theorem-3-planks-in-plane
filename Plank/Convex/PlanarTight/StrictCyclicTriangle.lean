/- The cyclic strict equality case gives an exact triangle in the original plane. -/
module
public import Plank.Convex.PlanarTight.PlanarChart
public import Plank.Convex.PlanarTight.StrictTriangleEnclosure
public import Plank.Convex.PlanarTight.StrictTriangleClassification
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.StrictCyclicTriangle
open StrictCapSetting PlanarChart

theorem of_caps (C : Setting)
    (hcaps : ∀ i, ¬ ∃ x ∈ C.K, C.hi i < x i ∧
      x (CyclicCapTriangle.next i) < C.lo (CyclicCapTriangle.next i)) :
    ∃ v : Fin 3 → Point3, AffineIndependent ℝ v ∧ C.K = convexHull ℝ (Set.range v) := by
  let K' := projection '' C.K
  let f := forms C.A C.D
  have hg (x : Point3) (hx : x ∈ C.K) (i : Fin 3) : f i (projection x) = x i :=
    congrFun (graph_projection C.A C.D (C.positive 2).ne' x (C.plane x hx)) i
  have hbox : ∀ z ∈ K', ∀ i, 0 ≤ f i z ∧ f i z ≤ 1 := by
    rintro _ ⟨x, hx, rfl⟩ i
    simpa only [hg x hx i] using C.box x hx i
  have hL (i : Fin 3) : ∃ z ∈ K', f i z = 0 := by
    obtain ⟨x, hx, he⟩ := C.min i
    exact ⟨projection x, ⟨x, hx, rfl⟩, (hg x hx i).trans he⟩
  have hU (i : Fin 3) : ∃ z ∈ K', f i z = 1 := by
    obtain ⟨x, hx, he⟩ := C.max i
    exact ⟨projection x, ⟨x, hx, rfl⟩, (hg x hx i).trans he⟩
  have hcover : ∀ z ∈ K', ∃ i, C.lo i ≤ f i z ∧ f i z ≤ C.hi i := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := C.covered x hx
    exact ⟨i, by simpa only [hg x hx i] using hi⟩
  have hcaps' : ∀ i, ¬ ∃ z ∈ K', C.hi i < f i z ∧
      f (CyclicCapTriangle.next i) z < C.lo (CyclicCapTriangle.next i) := by
    intro i
    rintro ⟨_, ⟨x, hx, rfl⟩, hu, hl⟩
    exact hcaps i ⟨x, hx, by simpa only [hg x hx i] using hu,
      by simpa only [hg x hx (CyclicCapTriangle.next i)] using hl⟩
  obtain ⟨v, hv, hbody⟩ := StrictTriangleEnclosure.cyclic_eq_triangle (by simp)
    K' (Convex.affine_image projection C.convex) f C.A C.D C.positive
    (graph_plane C.A C.D (C.positive 2).ne') (graph_injective C.A C.D)
    hbox hL hU C.lo C.hi C.width_pos C.lo_pos C.hi_lt hcover C.total hcaps'
  exact triangle_of_projection C.K C.A C.D (C.positive 2).ne' C.plane v hv hbody

theorem rowG (C : Setting) (hh : C.holds ⟨0, 21⟩) :
    ∃ v : Fin 3 → Point3, AffineIndependent ℝ v ∧ C.K = convexHull ℝ (Set.range v) := by
  apply of_caps C
  intro i
  have he0 := hh.2 0 (by decide)
  have he2 := hh.2 2 (by decide)
  have he4 := hh.2 4 (by decide)
  fin_cases i
  · simpa [PlanarCapCaseReduction.EdgeEmpty, PlanarCapCaseReduction.EmptyPair,
      PlanarCapCaseReduction.wall, PlanarCapCaseReduction.next, CyclicCapTriangle.next] using he0
  · simpa [PlanarCapCaseReduction.EdgeEmpty, PlanarCapCaseReduction.EmptyPair,
      PlanarCapCaseReduction.wall, PlanarCapCaseReduction.next, CyclicCapTriangle.next] using he4
  · simpa [PlanarCapCaseReduction.EdgeEmpty, PlanarCapCaseReduction.EmptyPair,
      PlanarCapCaseReduction.wall, PlanarCapCaseReduction.next, CyclicCapTriangle.next] using he2

/-- The cyclic ledger case belongs to the explicit two-parameter strict
triangle family, for the original body and the original windows. -/
theorem rowG_normal (C : Setting) (hh : C.holds ⟨0, 21⟩) :
    StrictTriangleClassification.Normal C.K (fun i => AffineMap.proj i) C.lo C.hi := by
  obtain ⟨v, hv, hbody⟩ := rowG C hh
  exact StrictTriangleClassification.of_tight C.K v hv hbody
    (fun i => AffineMap.proj i) C.box C.min C.max C.lo C.hi
    C.lo_pos C.hi_lt C.width_pos C.total C.covered

end Plank.Convex.PlanarTight.StrictCyclicTriangle

/-- info: 'Plank.Convex.PlanarTight.StrictCyclicTriangle.of_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictCyclicTriangle.of_caps

/-- info: 'Plank.Convex.PlanarTight.StrictCyclicTriangle.rowG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictCyclicTriangle.rowG

/-- info: 'Plank.Convex.PlanarTight.StrictCyclicTriangle.rowG_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictCyclicTriangle.rowG_normal
