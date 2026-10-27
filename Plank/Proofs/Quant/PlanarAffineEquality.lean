/- Actual quantitative equality is invariant under every invertible affine chart. -/
module

public import Plank.Proofs.Quant.FourPointNormalization
public import Plank.Proofs.AffineWidth

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarAffineEquality

open Set MeasureTheory PlanarQuantitative
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def transform (T : Point ≃ᵃ[ℝ] Point) (f : Point →ᵃ[ℝ] ℝ) : Point →ᵃ[ℝ] ℝ :=
  f.comp T.symm.toAffineMap

theorem rangeWidth_transform (T : Point ≃ᵃ[ℝ] Point) (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) :
    rangeWidth (T '' K) (transform T f) = rangeWidth K f := by
  simpa [transform, Set.image_image] using
    Body.width_comp_image (T '' K) T.symm.toAffineMap f

def factor (T : Point ≃ᵃ[ℝ] Point) : ℝ := |LinearMap.det (T.linear : Point →ₗ[ℝ] Point)|

theorem factor_ne_zero (T : Point ≃ᵃ[ℝ] Point) : factor T ≠ 0 :=
  abs_ne_zero.mpr T.linear.isUnit_det'.ne_zero

theorem area_image (T : Point ≃ᵃ[ℝ] Point) (S : Set Point) :
    (volume (T '' S)).toReal = factor T*(volume S).toReal := by
  have he : (T : Point → Point) = (fun x => T 0+x) ∘ (T.linear : Point →ₗ[ℝ] Point) := by
    funext x
    have hh := congrFun T.toAffineMap.decomp x
    change T x = T.linear x+T 0 at hh
    change T x = T 0+T.linear x
    rw [hh,add_comm]
  rw [he,Set.image_comp,Set.image_add_left,measure_preimage_add,
    Measure.addHaar_image_linearMap,ENNReal.toReal_mul,ENNReal.toReal_ofReal (abs_nonneg _)]
  rfl

variable {ι : Type*} [Fintype ι]

def Equality (K : Set Point) (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) : Prop :=
  (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal =
    (max 0 (1-∑ i, (hi i-lo i)/rangeWidth K (f i)))^2*(volume K).toReal

omit [Fintype ι] in
theorem image_gap (T : Point ≃ᵃ[ℝ] Point) (K : Set Point) (f : ι → Point →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) :
    T '' (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) =
      (T '' K) \ ⋃ i, {x | lo i ≤ transform T (f i) x ∧ transform T (f i) x ≤ hi i} := by
  rw [Set.image_sdiff T.injective,Set.image_iUnion]
  congr 1
  apply iUnion_congr
  intro i
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simpa [transform] using hx
  · intro hy
    exact ⟨T.symm y,hy,T.apply_symm_apply y⟩

/-- No compactness, polygonality or genericity hypothesis is needed for
transport: the nonzero determinant factor and all actual ranges cancel. -/
theorem equality_transform_iff (T : Point ≃ᵃ[ℝ] Point) (K : Set Point)
    (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    Equality (T '' K) (fun i => transform T (f i)) lo hi ↔ Equality K f lo hi := by
  unfold Equality
  rw [← image_gap,area_image,area_image]
  simp only [rangeWidth_transform]
  rw [show (max 0 (1-∑ i, (hi i-lo i)/rangeWidth K (f i)))^2*(factor T*(volume K).toReal) =
    factor T*((max 0 (1-∑ i, (hi i-lo i)/rangeWidth K (f i)))^2*(volume K).toReal) by ring]
  exact ⟨mul_left_cancel₀ (factor_ne_zero T),fun h => congrArg (fun x => factor T*x) h⟩

end Plank.PlanarAffineEquality

/-- info: 'Plank.PlanarAffineEquality.equality_transform_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarAffineEquality.equality_transform_iff
