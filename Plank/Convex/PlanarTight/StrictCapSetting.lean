/- Shared normalized hypotheses for the strict planar equality dispatcher. -/
module
public import Plank.Convex.PlanarCapSymmetry
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.StrictCapSetting

abbrev Point := Fin 3 → ℝ

/-- Internal data for dispatching a positive strict equality cover on a positive plane. -/
structure Setting where
  K : Set Point
  convex : Convex ℝ K
  box : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1
  min : ∀ i, ∃ x ∈ K, x i = 0
  max : ∀ i, ∃ x ∈ K, x i = 1
  A : Point
  D : ℝ
  positive : ∀ i, 0 < A i
  plane : ∀ x ∈ K, ∑ i, A i * x i = D
  lo : Point
  hi : Point
  lo_pos : ∀ i, 0 < lo i
  hi_lt : ∀ i, hi i < 1
  width_pos : ∀ i, lo i < hi i
  covered : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i
  total : ∑ i, (hi i - lo i) = 1

def Setting.holds (C : Setting) (p : PlanarCapPatterns.Pattern) : Prop :=
  PlanarCapPatterns.Holds
    (PlanarCapCaseReduction.SingleEmpty C.K (fun i => AffineMap.proj i) C.lo C.hi)
    (PlanarCapCaseReduction.EdgeEmpty C.K (fun i => AffineMap.proj i) C.lo C.hi) p

def Setting.transform (C : Setting) (p : Equiv.Perm (Fin 3)) (flip : Bool) : Setting where
  K := CubeSymmetry.transform p flip '' C.K
  convex := CubeSymmetry.convex_image C.K C.convex p flip
  box := CubeSymmetry.box C.K p flip C.box
  min := CubeSymmetry.zero_contacts C.K p flip C.min C.max
  max := CubeSymmetry.unit_contacts C.K p flip C.min C.max
  A := fun i => C.A (p i)
  D := if flip then (∑ i, C.A i) - C.D else C.D
  positive := fun i => C.positive (p i)
  plane := CubeSymmetry.transformed_plane C.K C.A C.D C.plane p flip
  lo := CubeSymmetry.lower C.lo C.hi p flip
  hi := CubeSymmetry.upper C.lo C.hi p flip
  lo_pos := fun i => (CubeSymmetry.strict C.lo C.hi p flip
    (fun j => ⟨C.lo_pos j, C.hi_lt j⟩) i).1
  hi_lt := fun i => (CubeSymmetry.strict C.lo C.hi p flip
    (fun j => ⟨C.lo_pos j, C.hi_lt j⟩) i).2
  width_pos := by
    intro i
    cases flip
    · exact C.width_pos (p i)
    · exact sub_lt_sub_left (C.width_pos (p i)) 1
  covered := CubeSymmetry.cover C.K C.lo C.hi p flip C.covered
  total := by simpa only [CubeSymmetry.width_sum] using C.total

theorem Setting.holds_transform (C : Setting) (p q : PlanarCapPatterns.Pattern)
    (r : Fin 6) (reverse : Bool) (hp : PlanarCapSymmetry.Pulls p q r reverse)
    (hh : C.holds p) :
    (C.transform (PlanarCapSymmetry.coordinateOrder r reverse) (PlanarCapSymmetry.reflectCube r)).holds q :=
  PlanarCapSymmetry.holds_transform C.K C.lo C.hi p q r reverse hp hh

def Excluded (p : PlanarCapPatterns.Pattern) : Prop := ∀ C : Setting, C.holds p → False

theorem excluded_of_pulls (p q : PlanarCapPatterns.Pattern) (r : Fin 6) (reverse : Bool)
    (hp : PlanarCapSymmetry.Pulls p q r reverse) (hq : Excluded q) : Excluded p := by
  intro C hh
  exact hq _ (C.holds_transform p q r reverse hp hh)

end Plank.Convex.PlanarTight.StrictCapSetting

/-- info: 'Plank.Convex.PlanarTight.StrictCapSetting.excluded_of_pulls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictCapSetting.excluded_of_pulls
