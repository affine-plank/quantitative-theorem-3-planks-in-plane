/- Exact triangle bodies pass back through the cap symmetries. -/
module
public import Plank.Convex.PlanarTight.StrictCapSetting
public import Plank.Convex.PlanarTight.StrictTriangleClassification
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.StrictTriangleTransport
open StrictCapSetting

def TriangleBody (K : Set Point) : Prop :=
  ∃ v : Fin 3 → Point, AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v)

private theorem inverse_transform (p : Equiv.Perm (Fin 3)) (flip : Bool) (x : Point) :
    CubeSymmetry.transform p.symm flip (CubeSymmetry.transform p flip x) = x := by
  funext i
  cases flip <;> simp

private theorem transform_injective (p : Equiv.Perm (Fin 3)) (flip : Bool) :
    Function.Injective (CubeSymmetry.transform p flip) :=
  Function.LeftInverse.injective (inverse_transform p flip)

theorem TriangleBody.of_transform (K : Set Point) (p : Equiv.Perm (Fin 3)) (flip : Bool)
    (h : TriangleBody (CubeSymmetry.transform p flip '' K)) : TriangleBody K := by
  obtain ⟨v, hv, hbody⟩ := h
  let inv := CubeSymmetry.transform p.symm flip
  have hi : inv '' (CubeSymmetry.transform p flip '' K) = K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simpa only [inv, inverse_transform] using hx
    · intro x hx
      exact ⟨CubeSymmetry.transform p flip x, ⟨x, hx, rfl⟩, inverse_transform p flip x⟩
  refine ⟨inv ∘ v, hv.map' inv (transform_injective p.symm flip), ?_⟩
  calc
    K = inv '' (CubeSymmetry.transform p flip '' K) := hi.symm
    _ = inv '' convexHull ℝ (Set.range v) := by rw [hbody]
    _ = convexHull ℝ (Set.range (inv ∘ v)) := by
      rw [AffineMap.image_convexHull, ← Set.range_comp]

def Triangular (p : PlanarCapPatterns.Pattern) : Prop :=
  ∀ C : Setting, C.holds p → TriangleBody C.K

theorem triangular_of_pulls (p q : PlanarCapPatterns.Pattern) (r : Fin 6) (reverse : Bool)
    (hp : PlanarCapSymmetry.Pulls p q r reverse) (hq : Triangular q) : Triangular p := by
  intro C hh
  exact TriangleBody.of_transform C.K (PlanarCapSymmetry.coordinateOrder r reverse)
    (PlanarCapSymmetry.reflectCube r) (hq _ (C.holds_transform p q r reverse hp hh))

theorem normal_of_triangle (C : Setting) (h : TriangleBody C.K) :
    StrictTriangleClassification.Normal C.K (fun i => AffineMap.proj i) C.lo C.hi := by
  obtain ⟨v, hv, hbody⟩ := h
  exact StrictTriangleClassification.of_tight C.K v hv hbody
    (fun i => AffineMap.proj i) C.box C.min C.max C.lo C.hi
    C.lo_pos C.hi_lt C.width_pos C.total C.covered

end Plank.Convex.PlanarTight.StrictTriangleTransport

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleTransport.triangular_of_pulls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleTransport.triangular_of_pulls

/-- info: 'Plank.Convex.PlanarTight.StrictTriangleTransport.normal_of_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictTriangleTransport.normal_of_triangle
