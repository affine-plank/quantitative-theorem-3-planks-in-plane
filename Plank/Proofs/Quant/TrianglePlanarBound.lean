/- Apply the general planar bound to the original triangle/plank interface. -/
module
public import Plank.Proofs.Quant.PlanarProductCoordinates
public import Plank.Proofs.TriangleGeometry

@[expose] public section
noncomputable section

namespace Plank.TrianglePlanarBound
open Set MeasureTheory Proofs.Transport
open Plank.Convex.DeficientHeightTilt

/-- A normal-vector functional as an affine map. -/
def dotForm (u : ℝ × ℝ) : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  (u.1 • LinearMap.fst ℝ ℝ ℝ + u.2 • LinearMap.snd ℝ ℝ ℝ).toAffineMap

@[simp] theorem dotForm_apply (u x : ℝ × ℝ) : dotForm u x = dot u x := rfl

/-- The actual affine range on a filled triangle is its vertex spread. -/
theorem rangeWidth_triangle (T : Triangle) (f : (ℝ × ℝ) →ᵃ[ℝ] ℝ) :
    rangeWidth T.set f =
      max (f T.A) (max (f T.B) (f T.C)) - min (f T.A) (min (f T.B) (f T.C)) := by
  have hmax := (isGreatest_pair (a := f T.B) (b := f T.C)).insert (f T.A)
  have hmin := (isLeast_pair (a := f T.B) (b := f T.C)).insert (f T.A)
  have hg : IsGreatest (convexHull ℝ ({f T.A,f T.B,f T.C} : Set ℝ))
      (max (f T.A) (max (f T.B) (f T.C))) :=
    ⟨subset_convexHull ℝ _ hmax.1,convexHull_min hmax.2 (convex_Iic _)⟩
  have hl : IsLeast (convexHull ℝ ({f T.A,f T.B,f T.C} : Set ℝ))
      (min (f T.A) (min (f T.B) (f T.C))) :=
    ⟨subset_convexHull ℝ _ hmin.1,convexHull_min hmin.2 (convex_Ici _)⟩
  rw [rangeWidth,Body.width,set_eq_convexHull,f.image_convexHull]
  simp only [image_insert_eq,image_singleton]
  rw [hg.csSup_eq,hl.csInf_eq]

@[simp] theorem rangeWidth_dotForm (T : Triangle) (u : ℝ × ℝ) :
    rangeWidth T.set (dotForm u) = T.width u :=
  rangeWidth_triangle T (dotForm u)

/-- Every sharp planar bound gives the original quantitative triangle
statement for the same number of planks, with actual areas and relative widths. -/
theorem bound_of_planar {m : ℕ} (h : PlanarQuantitative.SharpPlanarBound m)
    (T : Triangle) (p : Fin m → Plank) :
    (max 0 (1-∑ i, (p i).relWidth T))^2*(volume T.set).toReal ≤
      (volume (T.set \ ⋃ i, (p i).set)).toReal := by
  have hK : IsCompact T.set := by
    rw [set_eq_convexHull]
    exact (Set.toFinite ({T.A,T.B,T.C} : Set (ℝ × ℝ))).isCompact_convexHull ℝ
  have hW (i : Fin m) : 0 < rangeWidth T.set (dotForm (p i).u) := by
    rw [rangeWidth_dotForm]
    exact width_pos T (p i).u_ne_zero
  simpa only [rangeWidth_dotForm,Plank.relWidth,dotForm_apply,Plank.set,Proofs.Basic.mem_plank_iff] using
    PlanarQuantitative.bound_prod h T.set hK (convex_triangle T) ⟨T.A,mem_A T⟩
      (fun i => dotForm (p i).u) (fun i => (p i).lo) (fun i => (p i).hi)
      (fun i => (p i).lo_le_hi) hW

end Plank.TrianglePlanarBound

#print axioms Plank.TrianglePlanarBound.bound_of_planar
