/- Exact overlap scaling when the canonical anchor lines concur. -/
module

public import Plank.Proofs.Quant.PlanarOverlapCorrection

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarConcurrentScaling

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarSevenCellArea
open PlanarSevenCellEquality PlanarOverlapCorrection PlanarInductionBoundary

theorem homothety_surjective (z : Point) (q : ℝ) (hq : q ≠ 0) :
    Function.Surjective (AffineMap.homothety z q) := by
  intro x
  refine ⟨AffineMap.homothety z q⁻¹ x,?_⟩
  rw [← AffineMap.homothety_mul_apply,mul_inv_cancel₀ hq,AffineMap.homothety_one]
  rfl

/-- A window's canonical motion is an actual homothety whenever its
anchor value is the image of the common center. -/
theorem image_window (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (z : Point)
    (c r : Fin 3 → ℝ) (hc : ∀ i, f i z = c i) (t : ℝ) (ht : -1 < t) (i : Fin 3) :
    AffineMap.homothety z (1+t) '' windows f (path c r 0) i =
      windows f (path c r t) i := by
  have hq : 0 < 1+t := by linarith only [ht]
  have hlo : (path c r t).1 i = (1-(1+t))*c i+(1+t)*(path c r 0).1 i := by
    dsimp [path]
    ring
  have hhi : (path c r t).2 i = (1-(1+t))*c i+(1+t)*(path c r 0).2 i := by
    dsimp [path]
    ring
  have hmem (x : Point) :
      AffineMap.homothety z (1+t) x ∈ windows f (path c r t) i ↔
        x ∈ windows f (path c r 0) i := by
    simp only [windows,plank,mem_ofPred_eq,form_homothety,hc,hlo,hhi,
      add_le_add_iff_left,mul_le_mul_iff_right₀ hq]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    obtain ⟨x,rfl⟩ := homothety_surjective z (1+t) hq.ne' y
    exact ⟨x,(hmem x).mp hy,rfl⟩

/-- The full overlap correction scales quadratically, including positive
triple area. No body containment or area-equality premise is used. -/
theorem correction_scale (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (z : Point)
    (c r : Fin 3 → ℝ) (hc : ∀ i, f i z = c i) (t : ℝ) (ht : -1 < t) :
    correction (windows f (path c r t)) =
      (1+t)^2*correction (windows f (path c r 0)) := by
  let T := AffineMap.homothety z (1+t)
  let P := windows f (path c r 0)
  have hinj : Function.Injective T := AffineMap.homothety_injective z (by linarith only [ht])
  have hi (i) : windows f (path c r t) i = T '' P i := (image_window f z c r hc t ht i).symm
  simp only [correction,hi,← image_inter hinj,← image_union]
  change (volume (AffineMap.homothety z (1+t) '' ((P 0 ∩ P 1) ∪ (P 0 ∩ P 2)))).toReal+
    (volume (AffineMap.homothety z (1+t) '' (P 1 ∩ P 2))).toReal = _
  rw [area_homothety,area_homothety]
  ring

end Plank.PlanarConcurrentScaling

/-- info: 'Plank.PlanarConcurrentScaling.correction_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarConcurrentScaling.correction_scale
