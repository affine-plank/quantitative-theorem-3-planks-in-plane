/- Every nonconstant planar affine form is represented in the compact
unit-normal direction space by its actual support normalization. -/
module

public import PlanarUnitDirections

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarAffineDirections

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarUnitDirections
open Plank.Convex.DeficientHeightTilt

def coefficients (f : Point →ᵃ[ℝ] ℝ) : Point := fun i => f.linear (Pi.single i 1)

theorem raw_coefficients (f : Point →ᵃ[ℝ] ℝ) (x : Point) :
    raw (coefficients f) x=f.linear x := by
  have hx : x=x 0 • Pi.single 0 1+x 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  conv_rhs => rw [hx, map_add, map_smul, map_smul]
  simp only [raw_apply, coefficients, smul_eq_mul]
  ring

theorem coefficients_ne_zero (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear≠0) : coefficients f≠0 := by
  intro hc
  apply hf
  apply LinearMap.ext
  intro x
  change f.linear x=0
  rw [←raw_coefficients, hc]
  simp

def direction (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear≠0) : Direction :=
  ⟨‖coefficients f‖⁻¹ • coefficients f, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (coefficients_ne_zero f hf))⟩

theorem raw_direction (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear≠0) (x : Point) :
    raw (direction f hf) x=‖coefficients f‖⁻¹*(f x-f 0) := by
  have hd : f.linear x=f x-f 0 := congrFun f.decomp' x
  calc
    raw (direction f hf) x = ‖coefficients f‖⁻¹*raw (coefficients f) x := by
      simp only [raw_apply, direction, Pi.smul_apply, smul_eq_mul]
      ring
    _ = _ := by rw [raw_coefficients, hd]

def lower (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) : ℝ := sInf (f '' K)

theorem lower_eq_of_min {K : Set Point} (f : Point →ᵃ[ℝ] ℝ)
    {b : Point} (hb : b∈K) (hmin : ∀ x∈K, f b≤f x) : lower K f=f b := by
  apply IsLeast.csInf_eq
  exact ⟨mem_image_of_mem f hb, fun _ hx => by
    obtain ⟨x,hx,rfl⟩ := hx
    exact hmin x hx⟩

/-- The compact direction form equals the actual support normalization of
the original affine form everywhere, including outside the body. -/
theorem normalized_direction {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (hW : 0<rangeWidth K f) (x : Point) :
    normalized K (direction f (linear_ne_zero_of_rangeWidth_pos hne f hW)) x=
      (f x-lower K f)/rangeWidth K f := by
  let hf := linear_ne_zero_of_rangeWidth_pos hne f hW
  let u := direction f hf
  let q := ‖coefficients f‖⁻¹
  have hq : 0<q := inv_pos.mpr (norm_pos_iff.mpr (coefficients_ne_zero f hf))
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form f)
  have hraw (y : Point) : raw u y=q*(f y-f 0) := raw_direction f hf y
  have hlow : PlanarUnitDirections.lower K u=q*(f b-f 0) := by
    have hm : ∀ y∈K, raw u b≤raw u y := fun y hy => by
      rw [hraw,hraw]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hmin y hy) _) hq.le
    exact (lower_eq_of_min (raw u) hb hm).trans (hraw b)
  have hwidth : rangeWidth K (raw u)=q*rangeWidth K f := by
    have hw : rangeWidth K (raw u)=raw u a-raw u b :=
      Body.width_eq_of_realisers ha hb (fun y hy => by
      rw [hraw,hraw]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hmax y hy) _) hq.le)
      (fun y hy => by
        rw [hraw,hraw]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hmin y hy) _) hq.le)
    have hwf : rangeWidth K f=f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
    rw [hw,hraw,hraw,hwf]
    ring
  change normalized K u x=_
  rw [normalized_apply,hlow,hwidth,hraw,lower_eq_of_min f hb hmin]
  field_simp [hq.ne',hW.ne']
  ring

/-- A form already having actual unit width and values in [0,1] is itself
one of the normalized compact-direction forms. -/
theorem normalized_eq_unit_form {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (hunit : rangeWidth K f=1)
    (hnorm : ∀ x∈K, 0≤f x ∧ f x≤1) :
    ∃ u : Direction, normalized K u=f := by
  have hW : 0<rangeWidth K f := by rw [hunit]; norm_num
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form f)
  have hspan : rangeWidth K f=f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
  have hbzero : f b=0 := by
    have hla := (hnorm a ha).2
    have hlb := (hnorm b hb).1
    linarith only [hunit,hspan,hla,hlb]
  refine ⟨direction f (linear_ne_zero_of_rangeWidth_pos hne f hW),?_⟩
  apply AffineMap.ext
  intro x
  rw [normalized_direction hK hne f hW,lower_eq_of_min f hb hmin,hbzero,hunit]
  ring

end Plank.PlanarAffineDirections

#print axioms Plank.PlanarAffineDirections.normalized_direction
#print axioms Plank.PlanarAffineDirections.normalized_eq_unit_form
