/- Split one nonzero affine coordinate from its kernel. Haar comparison
transfers actual physical volumes to product-measure cut coordinates. -/
module
public import NoncoincidentCutDerivatives
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalCutCoordinates

open Set MeasureTheory
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_unit_vector (L : E →ₗ[ℝ] ℝ) (hL : L≠0) : ∃ v,L v=1 := by
  obtain ⟨x,hx⟩ : ∃ x,L x≠0 := by
    by_contra! h
    exact hL (by ext x; exact h x)
  exact ⟨(L x)⁻¹ • x,by simp [hx]⟩

def split (L : E →ₗ[ℝ] ℝ) (v : E) (hv : L v=1) :
    (ℝ × L.ker) ≃ₗ[ℝ] E where
  toFun p := p.1 • v+p.2
  invFun x := (L x,⟨x-L x • v,by simp [hv]⟩)
  map_add' p q := by simp [add_smul]; abel
  map_smul' r p := by simp [smul_add,smul_smul]
  left_inv p := by
    ext
    · simp [hv]
    · simp [hv]
  right_inv x := by simp

theorem split_first (L : E →ₗ[ℝ] ℝ) (v : E) (hv : L v=1)
    (p : ℝ × L.ker) : L (split L v hv p)=p.1 := by
  change L (p.1 • v+p.2)=p.1
  simp [hv]

theorem affine_split (f : E →ᵃ[ℝ] ℝ) (v : E) (hv : f.linear v=1)
    (p : ℝ × f.linear.ker) : f (split f.linear v hv p)=p.1+f 0 := by
  have he := congrFun f.decomp (split f.linear v hv p)
  change f (split f.linear v hv p)=f.linear (split f.linear v hv p)+f 0 at he
  rw [he,split_first]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A positive constant compares physical volume with the product measure.
No determinant, orthonormal basis, or dimension-specific coordinates are needed. -/
theorem exists_volume_factor (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E →ₗ[ℝ] ℝ) (v : E) (hv : L v=1) :
    ∃ c : ℝ, 0<c ∧ ∀ S : Set E, MeasurableSet S →
      μ.real S=c*(volume.prod (Measure.addHaar : Measure L.ker)).real
        (split L v hv ⁻¹' S) := by
  let F := split L v hv
  let ν : Measure (ℝ × L.ker) := volume.prod Measure.addHaar
  let τ : Measure E := ν.map F
  letI : τ.IsAddHaarMeasure := F.toContinuousLinearEquiv.isAddHaarMeasure_map ν
  let a : ℝ≥0 := Measure.addHaarScalarFactor τ μ
  have hpos : 0<a := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure τ μ
  have he : τ=a • μ := Measure.isAddLeftInvariant_eq_smul τ μ
  refine ⟨(a : ℝ)⁻¹,inv_pos.mpr hpos,?_⟩
  intro S hS
  have hm : ν.real (F ⁻¹' S)=(a : ℝ)*μ.real S := by
    have hmap : τ.real S=ν.real (F ⁻¹' S) := congrArg ENNReal.toReal
      (Measure.map_apply F.toContinuousLinearEquiv.continuous.measurable hS)
    rw [←hmap]
    rw [he,measureReal_nnreal_smul_apply]
  change μ.real S=(a : ℝ)⁻¹*ν.real (F ⁻¹' S)
  rw [hm,←mul_assoc,inv_mul_cancel₀ (ne_of_gt (show (0 : ℝ)<a from hpos)),one_mul]

end Plank.FiniteDimensionalCutCoordinates
