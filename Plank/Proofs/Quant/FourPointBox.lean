/- Explicit boxed half-plane coordinates for every normalized four-point body. -/
module

public import Plank.Proofs.Quant.FourPointHalfplanes
public import Plank.Proofs.Quant.PlanarPolygonArithmetic
public import Mathlib.Analysis.Convex.Topology

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FourPointBox

open Set MeasureTheory PlanarQuantitative FourPointHalfplanes
open PlanarPolygonHalfplanes PlanarPolygonArithmetic

def radius (a b : ℝ) : ℝ := |a|+|b|+1

def A (a b : ℝ) (i : Row) : ℝ := -(halfplanes a b i).linear (Pi.single 0 1)
def B (a b : ℝ) (i : Row) : ℝ := -(halfplanes a b i).linear (Pi.single 1 1)
def C (a b : ℝ) (i : Row) : ℝ := halfplanes a b i 0

theorem body_subset_box (a b : ℝ) :
    body a b ⊆ Icc (fun _ => -radius a b) (fun _ => radius a b) := by
  apply convexHull_min _ (convex_Icc _ _)
  intro x hx
  simp only [mem_insert_iff,mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  all_goals
    constructor <;> intro i <;> fin_cases i <;> dsimp [radius] <;>
      linarith [abs_nonneg a,abs_nonneg b,le_abs_self a,le_abs_self b,neg_abs_le a,neg_abs_le b]

theorem body_eq_boxed (a b : ℝ) :
    body a b = boxedRegion (-radius a b) (radius a b) (-radius a b) (radius a b)
      (A a b) (B a b) (C a b) := by
  ext x
  constructor
  · intro hx
    have hb := body_subset_box a b hx
    refine ⟨⟨hb.1 0,hb.2 0⟩,⟨hb.1 1,hb.2 1⟩,fun i => ?_⟩
    have hi := (mem_body_iff a b x).mp hx i
    have he := affine_eval_coordinates (halfplanes a b i) x
    dsimp [A,B,C]
    linarith only [hi,he]
  · intro hx
    apply (mem_body_iff a b x).mpr
    intro i
    have hi := hx.2.2 i
    have he := affine_eval_coordinates (halfplanes a b i) x
    dsimp [A,B,C] at hi
    linarith only [hi,he]

theorem compact_body (a b : ℝ) : IsCompact (body a b) :=
  (Set.toFinite _).isCompact_convexHull ℝ

theorem nonempty_body (a b : ℝ) : (body a b).Nonempty :=
  ⟨![0,0],subset_convexHull ℝ _ (by simp)⟩

/-- A completely arithmetic test for the actual area, valid for every
fourth vertex including points inside the standard triangle. -/
theorem body_area_iff (a b z : ℝ) :
    BoxTest (-radius a b) (radius a b) (-radius a b) (radius a b)
      (A a b) (B a b) (C a b) z ↔ (volume (body a b)).toReal = z := by
  rw [body_eq_boxed]
  exact boxTest_iff _ _ _ _ _ _ _ _

end Plank.FourPointBox

/-- info: 'Plank.FourPointBox.body_area_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FourPointBox.body_area_iff
