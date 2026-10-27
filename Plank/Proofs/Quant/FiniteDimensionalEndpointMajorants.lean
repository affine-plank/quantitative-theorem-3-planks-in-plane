/- Local power majorants and null-cell constraints in every positive dimension. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells
public import Plank.Proofs.Quant.FiniteDimensionalCellSupportingAffine
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalEndpointMajorants

open Set MeasureTheory Filter FiniteDimensionalCellSupportingAffine FiniteDimensionalCapWindowScaling
open scoped Topology

variable {n : ℕ}

variable {κ : Type*} [Fintype κ]

/-- A positive exterior cell has a dimension-power affine-root upper bound in a
neighborhood of the original endpoints, including empty target cells. -/
theorem exists_local_power_majorant {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (f : κ → (Point n) →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (s : Finset κ) (p : Endpoints κ)
    (hpos : 0 < (volume (signCell K f p s)).toReal) :
    ∃ G : Endpoints κ →L[ℝ] ℝ, ∀ᶠ e in 𝓝 p,
      0 < volumeRoot (signCell K f p s)+G (e-p) ∧
      (volume (signCell K f e s)).toReal ≤
        (volumeRoot (signCell K f p s)+G (e-p))^(n+1) := by
  rw [signCell_eq_cell] at hpos
  obtain ⟨L,hL⟩ := FiniteDimensionalCellSupportingAffine.exists_local_power_majorant
    hK hc (cutForms f s) (cutForms_ne_zero f hf s) (cutOffsets f p s) hpos
  let G := L.comp (cutLinear s).toContinuousLinearMap
  have hcont : Continuous (fun e : Endpoints κ => cutOffsets f e s) := by
    classical
    apply continuous_pi
    intro i
    by_cases hi : i ∈ s <;> simp only [cutOffsets,hi,ite_true,ite_false] <;> fun_prop
  refine ⟨G,?_⟩
  filter_upwards [hcont.continuousAt.tendsto.eventually hL] with e he
  simpa [signCell_eq_cell,
    cutOffsets_sub,G,ContinuousLinearMap.comp_apply,LinearMap.coe_toContinuousLinearMap'] using he

/-- One endpoint equation preserves zero volume along the entire line, even
when the original exterior cell is nonempty and degenerate. -/
theorem exists_zero_constraint {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : κ → (Point n) →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (s : Finset κ) (p : Endpoints κ)
    (hzero : (volume (signCell K f p s)).toReal = 0) :
    ∃ L : Endpoints κ →ₗ[ℝ] ℝ, ∀ z, L z = 0 → ∀ t : ℝ,
      (volume (signCell K f (p+t • z) s)).toReal = 0 := by
  rw [signCell_eq_cell] at hzero
  obtain ⟨L,_,hL⟩ := exists_zero_volume_constraint hK hc hne hV
    (cutForms f s) (cutForms_ne_zero f hf s) (cutOffsets f p s) hzero
  refine ⟨L.toLinearMap.comp (cutLinear s),?_⟩
  intro z hz t
  rw [signCell_eq_cell,cutOffsets_motion]
  exact hL (cutLinear s z) hz t

/-- One equation controls proportional upper scaling for either a positive
or a zero-volume cell. Zero volume simply gives a zero right-hand side. -/
theorem exists_scaling_constraint {K : Set (Point n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : κ → (Point n) →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (s : Finset κ) (p : Endpoints κ) :
    ∃ L : Endpoints κ →ₗ[ℝ] ℝ, ∀ z c,
      L z = volumeRoot (signCell K f p s)*c →
      ∀ᶠ t : ℝ in 𝓝 0, (volume (signCell K f (p+t • z) s)).toReal ≤
        (volume (signCell K f p s)).toReal*(1+t*c)^(n+1) := by
  by_cases hpos : 0 < (volume (signCell K f p s)).toReal
  · obtain ⟨L,hL⟩ := exists_local_power_majorant hK hc f hf s p hpos
    refine ⟨L.toLinearMap,fun z c hz => ?_⟩
    have ht : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
      have hh : Continuous (fun t : ℝ => p+t • z) := by fun_prop
      simpa using (hh.continuousAt (x := (0 : ℝ))).tendsto
    filter_upwards [ht.eventually hL] with t h
    have he : volumeRoot (signCell K f p s)+L (p+t • z-p) =
        volumeRoot (signCell K f p s)*(1+t*c) := by
      rw [add_sub_cancel_left,map_smul,smul_eq_mul,show L z = _ from hz]
      ring
    simpa only [he,mul_pow,volumeRoot_pow] using h.2
  · have hzero : (volume (signCell K f p s)).toReal = 0 :=
      le_antisymm (le_of_not_gt hpos) ENNReal.toReal_nonneg
    have hb : volumeRoot (signCell K f p s) = 0 :=
      (pow_eq_zero_iff (Nat.succ_ne_zero n)).mp ((volumeRoot_pow _).trans hzero)
    obtain ⟨L,hL⟩ := exists_zero_constraint hK hc hne hV f hf s p hzero
    refine ⟨L,fun z c hz => Filter.Eventually.of_forall fun t => ?_⟩
    rw [hL z (by simpa only [hb,zero_mul] using hz) t,hzero,zero_mul]

end Plank.FiniteDimensionalEndpointMajorants

#print axioms Plank.FiniteDimensionalEndpointMajorants.exists_local_power_majorant
#print axioms Plank.FiniteDimensionalEndpointMajorants.exists_zero_constraint
#print axioms Plank.FiniteDimensionalEndpointMajorants.exists_scaling_constraint
