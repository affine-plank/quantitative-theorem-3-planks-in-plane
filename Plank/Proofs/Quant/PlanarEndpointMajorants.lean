/- Affine square-root bounds and zero-cell constraints in endpoint space. -/
module

public import Plank.Proofs.Quant.PlanarCellSupportingAffine

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarEndpointMajorants

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarCellChartCalculus
  PlanarInactiveCellMotion PlanarPlankCellCharts
open Plank.Convex.DeficientHeightTilt

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
theorem cutForms_ne_zero {K : Set Point} (hne : K.Nonempty)
    (f : κ → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i)) (s : Finset κ) :
    ∀ i, cutForms f s i ≠ 0 := by
  classical
  intro i
  have hf : (f i).linear.toContinuousLinearMap ≠ 0 := by
    intro he
    apply linear_ne_zero_of_rangeWidth_pos hne (f i) (hW i)
    simpa using congrArg ContinuousLinearMap.toLinearMap he
  by_cases hs : i ∈ s <;> simpa [cutForms,hs] using hf

omit [Fintype κ] in
theorem cutOffsets_sub (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ)
    (p e : EndpointSpace κ) :
    cutOffsets f e.1 e.2 s-cutOffsets f p.1 p.2 s = cutLinear s (e-p) := by
  classical
  ext i
  by_cases hs : i ∈ s <;> simp [cutOffsets,cutLinear,cutDirection,hs]

/-- At each positive cell, a squared affine function bounds actual area
at every endpoint configuration, including empty target cells. -/
theorem exists_majorant {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (s : Finset κ) (p : EndpointSpace κ)
    (hpos : 0 < (volume (signCell K f p.1 p.2 s)).toReal) :
    ∃ L : EndpointSpace κ →L[ℝ] ℝ, ∀ e : EndpointSpace κ,
      (volume (signCell K f e.1 e.2 s)).toReal ≤
        (Real.sqrt (volume (signCell K f p.1 p.2 s)).toReal+L (e-p))^2 := by
  rw [signCell_eq_cell] at hpos
  obtain ⟨L,hL⟩ := PlanarCellSupportingAffine.exists_sqrt_majorant hK hconv
    (cutForms f s) (cutForms_ne_zero hne f hW s) (cutOffsets f p.1 p.2 s) hpos
  refine ⟨L.comp (cutLinear s).toContinuousLinearMap,?_⟩
  intro e
  by_cases he : (signCell K f e.1 e.2 s).Nonempty
  · rw [signCell_eq_cell] at he
    have hh := hL (cutOffsets f e.1 e.2 s) he
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hh
    rw [← sq,Real.sq_sqrt ENNReal.toReal_nonneg,← sq,cutOffsets_sub] at hsq
    simpa only [signCell_eq_cell,ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap'] using hsq
  · rw [not_nonempty_iff_eq_empty] at he
    rw [he,measure_empty,ENNReal.toReal_zero]
    exact sq_nonneg _

/-- Each zero-area cell imposes at most one linear equation on a motion
that preserves its zero area for the entire line. -/
theorem exists_zero_constraint {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : κ → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (s : Finset κ) (p : EndpointSpace κ)
    (hzero : (volume (signCell K f p.1 p.2 s)).toReal = 0) :
    ∃ L : EndpointSpace κ →ₗ[ℝ] ℝ, ∀ z, L z = 0 → ∀ t : ℝ,
      (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal = 0 := by
  rw [signCell_eq_cell] at hzero
  obtain ⟨L,_,hL⟩ := PlanarCellSupportingAffine.exists_zero_area_constraint hK hconv hne hV
    (cutForms f s) (cutForms_ne_zero hne f hW s) (cutOffsets f p.1 p.2 s) hzero
  refine ⟨L.toLinearMap.comp (cutLinear s),?_⟩
  intro z hz t
  rw [signCell_eq_cell]
  change (volume (PlanarCellArea.cell K (cutForms f s)
    (cutOffsets f (p.1+t • z.1) (p.2+t • z.2) s))).toReal = 0
  rw [cutOffsets_motion]
  exact hL (cutLinear s z) hz t

end Plank.PlanarEndpointMajorants

/-- info: 'Plank.PlanarEndpointMajorants.exists_majorant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEndpointMajorants.exists_majorant
/-- info: 'Plank.PlanarEndpointMajorants.exists_zero_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEndpointMajorants.exists_zero_constraint
