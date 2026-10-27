/- Moving-cut derivatives in every dimension, allowing parallel planks whose
boundary hyperplanes do not contain the chosen cut. -/
module
public import Plank.Proofs.Quant.ConvexExposedSections
public import MovingCutArea

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.NoncoincidentCutDerivatives

open Set MeasureTheory ConvexSections
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def transverseForm (H : (ℝ × E) →ᵃ[ℝ] ℝ) : E →ᵃ[ℝ] ℝ :=
  H.comp (LinearMap.inr ℝ ℝ E).toAffineMap

theorem affine_eval (H : (ℝ × E) →ᵃ[ℝ] ℝ) (t : ℝ) (y : E) :
    H (t,y)=transverseForm H y+H.linear (1,0)*t := by
  have he : (t,y)=t • (1,0)+(0,y) := by ext <;> simp
  rw [he]
  change H (t • ((1,0) : ℝ × E) +ᵥ ((0,y) : ℝ × E))=_
  rw [H.map_vadd,map_smul]
  change t*H.linear (1,0)+H (0,y)=H (0,y)+H.linear (1,0)*t
  ring

def residual (K : Set (ℝ × E)) (s : Finset ι)
    (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) : Set (ℝ × E) :=
  K\⋃ j∈s,{p | lo j≤H j p ∧ H j p≤hi j}

theorem fiber_residual (K : Set (ℝ × E)) (s : Finset ι)
    (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (t : ℝ) :
    fiber (residual K s H lo hi) t=
      ConvexExposedSections.exposed K s (fun j => transverseForm (H j))
        (fun j => lo j-(H j).linear (1,0)*t)
        (fun j => hi j-(H j).linear (1,0)*t) t := by
  ext y
  simp only [fiber,residual,ConvexExposedSections.exposed,mem_preimage,
    mem_sdiff,mem_iUnion,mem_ofPred_eq,mem_Icc,affine_eval,
    sub_le_iff_le_add,le_sub_iff_add_le]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]

theorem measurable_residual {K : Set (ℝ × E)} (hK : MeasurableSet K)
    (s : Finset ι) (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    MeasurableSet (residual K s H lo hi) := by
  apply hK.diff
  exact s.finite_toSet.measurableSet_biUnion fun j _ =>
    measurableSet_Icc.preimage (H j).continuous_of_finiteDimensional.measurable

/-- The actual residual-section volume is continuous at an interior cut.
Parallel windows are permitted: only a boundary containing the cut is excluded. -/
theorem continuousAt_density {K : Set (ℝ × E)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hfull : (interior K).Nonempty)
    (s : Finset ι) (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) {c : ℝ}
    (hcut : c∈interior (Prod.fst '' K))
    (hsep : ∀ j∈s, (¬∀ y,H j (c,y)=lo j) ∧ (¬∀ y,H j (c,y)=hi j)) :
    ContinuousAt (MovingCutArea.density μ (residual K s H lo hi)) c := by
  change ContinuousAt (fun t => μ.real (fiber (residual K s H lo hi) t)) c
  simp_rw [fiber_residual]
  apply ConvexExposedSections.continuousAt_exposed_measure_of_null_levels μ
    hK hc hfull s (fun j => transverseForm (H j))
  · intro j hj
    apply ConvexExposedSections.measure_affine_level_eq_zero_of_not_forall
    intro h
    apply (hsep j hj).1
    intro y
    rw [affine_eval,h y]
    ring
  · intro j hj
    apply ConvexExposedSections.measure_affine_level_eq_zero_of_not_forall
    intro h
    apply (hsep j hj).2
    intro y
    rw [affine_eval,h y]
    ring
  · exact continuousAt_id
  · exact hcut
  · intro j _; fun_prop
  · intro j _; fun_prop

/-- Actual upper-endpoint differentiability, with no transversality assumption. -/
theorem upper_derivative {K : Set (ℝ × E)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hfull : (interior K).Nonempty)
    (s : Finset ι) (H : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    {a b : ℝ} (hab : a<b) (hcut : b∈interior (Prod.fst '' K))
    (hsep : ∀ j∈s, (¬∀ y,H j (b,y)=lo j) ∧ (¬∀ y,H j (b,y)=hi j)) :
    HasDerivAt (MovingCutArea.gapArea μ (residual K s H lo hi) a)
      (-MovingCutArea.density μ (residual K s H lo hi) b) b :=
  MovingCutArea.hasDerivAt_gapArea_upper μ (measurable_residual hK.measurableSet s H lo hi)
    (measure_ne_top_of_subset sdiff_subset hK.measure_ne_top) hab
    (continuousAt_density μ hK hc hfull s H lo hi hcut hsep)

end Plank.NoncoincidentCutDerivatives
