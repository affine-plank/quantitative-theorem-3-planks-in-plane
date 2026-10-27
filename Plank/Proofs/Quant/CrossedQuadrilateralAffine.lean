/- Affine transport of the actual-area diagonal-direction classification. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralTwoDirections

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAffine
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment Quant.CrossedQuadrilateralPlacement
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

local instance : (volume : Measure Point).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure)

/-- The original affine coordinate, expressed after the change of coordinates. -/
def pull (T : Point ≃ᵃ[ℝ] Point) (f : Point →ᵃ[ℝ] ℝ) : Point →ᵃ[ℝ] ℝ :=
  f.comp T.symm.toAffineMap

@[simp] theorem pull_apply (T : Point ≃ᵃ[ℝ] Point) (f : Point →ᵃ[ℝ] ℝ) (z : Point) :
    pull T f (T z) = f z := by simp [pull]

theorem width_pull (T : Point ≃ᵃ[ℝ] Point) (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) :
    rangeWidth (T '' K) (pull T f) = rangeWidth K f := by
  simpa [pull, Set.image_image] using
    Plank.Body.width_comp_image (T '' K) T.symm.toAffineMap f

def jacobian (T : Point ≃ᵃ[ℝ] Point) : ℝ := |LinearMap.det T.linear.toLinearMap|

theorem jacobian_pos (T : Point ≃ᵃ[ℝ] Point) : 0 < jacobian T :=
  abs_pos.mpr (LinearEquiv.isUnit_det' T.linear).ne_zero

theorem volume_image (T : Point ≃ᵃ[ℝ] Point) (A : Set Point) :
    volume (T '' A) = ENNReal.ofReal (jacobian T)*volume A := by
  have h (z : Point) : T z = T 0+T.linear z := by
    simpa [add_comm] using T.map_vadd 0 z
  have he : T '' A = (fun z : Point => T 0+z) '' (T.linear '' A) := by
    rw [Set.image_image]
    congr 1
    funext z
    exact h z
  rw [he,Set.image_add_left,measure_preimage_add]
  exact Measure.addHaar_image_linearMap volume T.linear.toLinearMap A

theorem area_image (T : Point ≃ᵃ[ℝ] Point) (A : Set Point) :
    (volume (T '' A)).toReal = jacobian T*(volume A).toReal := by
  rw [volume_image,ENNReal.toReal_mul,ENNReal.toReal_ofReal (jacobian_pos T).le]

/-- Area equality is unchanged by an invertible affine transformation. -/
theorem image_equality_iff (T : Point ≃ᵃ[ℝ] Point) (K A : Set Point) (q : ℝ) :
    (volume (T '' K \ T '' A)).toReal = q*(volume (T '' K)).toReal ↔
      (volume (K \ A)).toReal = q*(volume K).toReal := by
  rw [← Set.image_sdiff T.injective,area_image,area_image]
  constructor <;> intro h <;> nlinarith [jacobian_pos T]

/-- A physical plank transported as a closed band of a nonconstant affine form. -/
def imagePlank (T : Point ≃ᵃ[ℝ] Point) (p : Plank) : Set Point :=
  {z | p.lo ≤ pull T (direction p.u) z ∧ pull T (direction p.u) z ≤ p.hi}

theorem imagePlank_eq (T : Point ≃ᵃ[ℝ] Point) (p : Plank) :
    imagePlank T p = T '' p.set := by
  ext z
  constructor
  · intro h
    exact ⟨T.symm z,h,T.apply_symm_apply z⟩
  · rintro ⟨x,hx,rfl⟩
    change p.lo ≤ dot p.u x ∧ dot p.u x ≤ p.hi at hx
    simpa [imagePlank,Plank.set,pull] using hx

theorem image_form_nonconstant (T : Point ≃ᵃ[ℝ] Point) (p : Plank) :
    (pull T (direction p.u)).linear ≠ 0 := by
  intro hf
  have hconst (z : Point) : pull T (direction p.u) z = pull T (direction p.u) 0 := by
    simpa [hf] using (pull T (direction p.u)).map_vadd 0 z
  have hzero := hconst (T 0)
  have hx := (hconst (T (1,0))).trans hzero.symm
  have hy := (hconst (T (0,1))).trans hzero.symm
  apply p.u_ne_zero
  exact Prod.ext (by simpa [dot] using hx) (by simpa [dot] using hy)

theorem image_body (S : Shape) (T : Point ≃ᵃ[ℝ] Point) :
    T '' S.body = convexHull ℝ {T (S.a,0),T (0,S.b),T (-S.c,0),T (0,-S.d)} := by
  change T.toAffineMap '' convexHull ℝ S.vertices = _
  rw [AffineMap.image_convexHull]
  simp [Shape.vertices,Set.image_insert_eq]

/-- Relative width from the full actual directional range of the image body. -/
def imageRelativeWidth (S : Shape) (T : Point ≃ᵃ[ℝ] Point) (p : Plank) : ℝ :=
  (p.hi-p.lo)/rangeWidth (T '' S.body) (pull T (direction p.u))

@[simp] theorem imageRelativeWidth_eq (S : Shape) (T : Point ≃ᵃ[ℝ] Point) (p : Plank) :
    imageRelativeWidth S T p = relativeWidth S p := by
  simp [imageRelativeWidth,width_pull,relativeWidth]

theorem image_width_pos (S : Shape) (T : Point ≃ᵃ[ℝ] Point) (p : Plank) :
    0 < rangeWidth (T '' S.body) (pull T (direction p.u)) := by
  rw [width_pull]
  exact direction_width_pos S p.u_ne_zero

/-- Both uncovered area and the actual width budget are transported. -/
theorem family_equality_iff {ι : Type*} [Fintype ι] (S : Shape)
    (T : Point ≃ᵃ[ℝ] Point) (P : ι → Plank) :
    (volume (T '' S.body \ ⋃ i, imagePlank T (P i))).toReal =
        (1-∑ i, imageRelativeWidth S T (P i))^2*(volume (T '' S.body)).toReal ↔
      (volume (S.body \ ⋃ i, (P i).set)).toReal =
        (1-∑ i, relativeWidth S (P i))^2*(volume S.body).toReal := by
  simp_rw [imageRelativeWidth_eq,imagePlank_eq]
  rw [← Set.image_iUnion]
  exact image_equality_iff T S.body (⋃ i, (P i).set) _

/-- Every affine image of the chart has the same complete two-direction
placement catalogue, with actual widths and actual area. -/
theorem two_directions_equality_iff (S : Shape) (T : Point ≃ᵃ[ℝ] Point)
    (l₀ u₀ l₁ u₁ ly uy : ℝ) (h₀ : l₀ < u₀) (h₁ : l₁ < u₁)
    (horder : l₀ ≤ l₁) (hy : ly ≤ uy)
    (hbudget : (u₀-l₀)/(S.a+S.c)+(u₁-l₁)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1) :
    let P := CrossedQuadrilateralTwoDirections.physicalFamily l₀ u₀ l₁ u₁ ly uy h₀.le h₁.le hy
    (volume (T '' S.body \ ⋃ i, imagePlank T (P i))).toReal =
        (1-∑ i, imageRelativeWidth S T (P i))^2*(volume (T '' S.body)).toReal ↔
      u₀ = l₁ ∧ u₁/S.a = -l₀/S.c ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  dsimp only
  rw [family_equality_iff]
  exact CrossedQuadrilateralTwoDirections.physicalFamily_equality_iff S
    l₀ u₀ l₁ u₁ ly uy h₀ h₁ horder hy hbudget

/-- The two crossed bands and arbitrary null third plank, in affine coordinates. -/
theorem crossed_with_null_equality_iff (S : Shape) (T : Point ≃ᵃ[ℝ] Point)
    (lx ux ly uy : ℝ) (hx : lx ≤ ux) (hy : ly ≤ uy)
    (hbudget : (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d) < 1)
    (n : Plank) (hn : n.lo = n.hi) :
    let P := CrossedQuadrilateralPlacement.physicalFamily lx ux ly uy hx hy n
    (volume (T '' S.body \ ⋃ i, imagePlank T (P i))).toReal =
        (1-∑ i, imageRelativeWidth S T (P i))^2*(volume (T '' S.body)).toReal ↔
      (ux = lx ∨ ux/S.a = -lx/S.c) ∧ (uy = ly ∨ uy/S.b = -ly/S.d) := by
  dsimp only
  rw [family_equality_iff]
  exact CrossedQuadrilateralPlacement.physicalFamily_equality_iff S lx ux ly uy hx hy hbudget n hn

end Quant.CrossedQuadrilateralAffine

/-- info: 'Quant.CrossedQuadrilateralAffine.two_directions_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralAffine.two_directions_equality_iff
