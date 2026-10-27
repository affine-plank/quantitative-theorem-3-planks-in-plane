/- The normalized quantitative objective is affine invariant in every
finite dimension, for every finite indexed family and natural exponent. -/
module

public import GlobalPlankBodyMinimum
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FinitePlankAffineTransport

open Set MeasureTheory PrunedPlankCounterexample

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

def pull (F : E ≃ᵃ[ℝ] E) (f : E →ᵃ[ℝ] ℝ) : E →ᵃ[ℝ] ℝ := f.comp F.toAffineMap

def volumeScale (F : E ≃ᵃ[ℝ] E) : ℝ := |LinearMap.det (F.linear.symm : E →ₗ[ℝ] E)|

omit [FiniteDimensional ℝ E] in
theorem volumeScale_pos (F : E ≃ᵃ[ℝ] E) : 0 < volumeScale F :=
  abs_pos.mpr F.linear.symm.isUnit_det'.ne_zero

omit [FiniteDimensional ℝ E] in
theorem width_pull (F : E ≃ᵃ[ℝ] E) (K : Set E) (f : E →ᵃ[ℝ] ℝ) :
    Body.width (F ⁻¹' K) (pull F f)=Body.width K f := by
  have he : pull F f '' (F ⁻¹' K)=f '' K := by
    change (f ∘ F) '' (F ⁻¹' K)=_
    rw [Set.image_comp,Set.image_preimage_eq _ F.surjective]
  change sSup (pull F f '' (F ⁻¹' K))-sInf (pull F f '' (F ⁻¹' K))=
    sSup (f '' K)-sInf (f '' K)
  rw [he]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem volume_preimage (F : E ≃ᵃ[ℝ] E) (K : Set E) :
    μ.real (F ⁻¹' K)=volumeScale F*μ.real K := by
  have he : F ⁻¹' K=F.linear ⁻¹' ((fun x => F 0+x) ⁻¹' K) := by
    ext x
    have hh := congrFun F.toAffineMap.decomp x
    change F x=F.linear x+F 0 at hh
    simp only [mem_preimage,hh,add_comm]
  have hm : μ (F ⁻¹' K)=ENNReal.ofReal (volumeScale F)*μ K := by
    rw [he,Measure.addHaar_preimage_linearEquiv,measure_preimage_add]
    rfl
  simp only [Measure.real,hm,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (volumeScale_pos F).le]

variable [Fintype ι]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
theorem budget_pull (F : E ≃ᵃ[ℝ] E) (K : Set E)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    budget (F ⁻¹' K) (fun i => pull F (f i)) lo hi=budget K f lo hi := by
  simp only [budget,width_pull]

omit [Fintype ι] in
theorem gap_pull (F : E ≃ᵃ[ℝ] E) (K : Set E)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    μ.real ((F ⁻¹' K)\covered (fun i => pull F (f i)) lo hi)=
      volumeScale F*μ.real (K\covered f lo hi) := by
  have he : (F ⁻¹' K)\covered (fun i => pull F (f i)) lo hi=F ⁻¹' (K\covered f lo hi) := by
    ext x
    simp only [covered,pull,AffineMap.comp_apply,AffineEquiv.coe_toAffineMap,
      mem_sdiff,mem_preimage,mem_iUnion,mem_ofPred_eq]
  rw [he,volume_preimage]

theorem margin_pull (F : E ≃ᵃ[ℝ] E) (K : Set E)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (d : ℕ) (B : ℝ) :
    GlobalPlankBodyMinimum.margin μ (F ⁻¹' K) (fun i => pull F (f i)) lo hi d B=
      GlobalPlankBodyMinimum.margin μ K f lo hi d B := by
  unfold GlobalPlankBodyMinimum.margin
  rw [gap_pull,volume_preimage,budget_pull,
    mul_div_mul_left _ _ (volumeScale_pos F).ne']

end Plank.FinitePlankAffineTransport
