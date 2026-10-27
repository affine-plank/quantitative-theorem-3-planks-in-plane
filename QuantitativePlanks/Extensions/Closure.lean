/- Closure does not change affine widths or the volume remaining in a convex set. -/
module

public import Plank.Proofs.AffineWidthCore
public import Mathlib.Analysis.Convex.Measure

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory

namespace Plank.Body

/-- Positive actual affine width already supplies nonemptiness. -/
theorem nonempty_of_width_pos {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} {f : E →ᵃ[ℝ] ℝ} (hW : 0 < width K f) : K.Nonempty := by
  by_contra h
  simp [not_nonempty_iff_eq_empty.mp h, width] at hW

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Passing to the closure preserves the actual affine width of a bounded set.
Convexity and attainment of the original extrema are not needed. -/
theorem width_closure {K : Set E} (hK : Bornology.IsBounded K) (f : E →ᵃ[ℝ] ℝ) :
    width (closure K) f = width K f := by
  by_cases hne : K.Nonempty
  · have hf : Continuous f := f.continuous_of_finiteDimensional
    have hcompact : IsCompact (closure K) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hK.closure
    have hsub : f '' K ⊆ f '' closure K := image_mono subset_closure
    have hsub' : f '' closure K ⊆ closure (f '' K) :=
      image_closure_subset_closure_image hf
    have hne' : (f '' closure K).Nonempty := (hne.mono subset_closure).image f
    have hsup := ((isLUB_iff_of_subset_of_subset_closure hsub hsub').mp
      (isLUB_csSup (hne.image f) ((hcompact.image hf).bddAbove.mono hsub))).csSup_eq hne'
    have hinf := ((isGLB_iff_of_subset_of_subset_closure hsub hsub').mp
      (isGLB_csInf (hne.image f) ((hcompact.image hf).bddBelow.mono hsub))).csInf_eq hne'
    simp only [width, hsup, hinf]
  · simp [not_nonempty_iff_eq_empty.mp hne, width]

end Plank.Body

namespace Plank.ConvexClosure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- This is the standard null-boundary theorem from Mathlib; no boundedness,
closedness or nonempty-interior hypothesis is required. -/
theorem measure_closure {K : Set E} (hc : Convex ℝ K) :
    μ (closure K) = μ K :=
  measure_closure_of_null_frontier (hc.addHaar_frontier μ)

/-- Removing any fixed set commutes with closing a convex body up to null sets.
The removed set need not itself be measurable. -/
theorem measure_closure_sdiff {K U : Set E} (hc : Convex ℝ K) :
    μ (closure K \ U) = μ (K \ U) := by
  apply measure_congr
  filter_upwards [closure_ae_eq_of_null_frontier (hc.addHaar_frontier μ)] with x hx
  simp only [mem_sdiff, hx]

end Plank.ConvexClosure
