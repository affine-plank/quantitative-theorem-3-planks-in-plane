/- Explicit statement bridges for the journal's ancillary consequences. -/
module

public import Plank.Convex.BangMinimumWidthVolume
public import FinitePlankAffineTransport
public import Plank.Proofs.Quant.FiniteDimensionalCapWindowCore
public import Plank.Proofs.Quant.PlanarThreePlank
public import Plank.Proofs.Quant.PlanarTwoPlankCells
public import SimplexFacetSharpExample

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Plank.JournalQuantitativeCorollaries

/-- The manuscript includes the empty family and both induction base cases. -/
theorem planar_bound_at_most_three {m : ℕ} (hm : m ≤ 3) :
    PlanarQuantitative.SharpPlanarBound m := by
  have cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · intro K _ _ _ f lo hi _ _
    simp
  · exact FiniteDimensionalOnePlankCaps.sharpBound_one
  · exact PlanarTwoPlankCells.sharpBound_two
  · exact PlanarThreePlank.sharpPlanarBound_three

/-- The familiar planar polynomial form of the general contraction theorem. -/
theorem planar_window_contraction {K : Set PlanarQuantitative.Point}
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : PlanarQuantitative.Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x = 0) (hone : ∃ x ∈ K, f x = 1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    volume.real (K ∩ {x | (1-t*r)*c ≤ f x ∧ f x ≤ c+(1-c)*(t*r)}) ≤
      t^2 * volume.real (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r}) +
        2*t*r*(1-t)*volume.real K := by
  have h := FiniteDimensionalCapWindowScaling.window_contraction
    (d := 1) hK hconv f hf hzero hone hc ht hr
  norm_num only [Nat.reduceAdd] at h
  simp only [measureReal_def]
  convert h using 1
  ring

/-- The simplex sharpness example includes the endpoint budget R=1. -/
theorem simplex_gap_eq_of_budget_le_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ)) [μ.IsAddHaarMeasure] (a : ℝ) (r : ι → ℝ)
    (ha : 0 ≤ a) (hr : ∀ i, 0 ≤ r i) (hR : a + (∑ i, r i) ≤ 1) :
    μ.real (SimplexSharpExample.body ι \ SimplexFacetSharpExample.covered ι a r) =
      (1-(a+∑ i, r i))^Fintype.card ι * μ.real (SimplexSharpExample.body ι) := by
  rcases lt_or_eq_of_le hR with hlt | heq
  · exact SimplexFacetSharpExample.gap_eq ι μ a r ha hr hlt
  · have hempty : SimplexSharpExample.body ι \
        SimplexFacetSharpExample.covered ι a r = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hu : (∑ i, x i) < 1-a := by
        apply lt_of_not_ge
        intro h
        apply hx.2 (mem_iUnion.mpr ⟨none, ?_⟩)
        simpa [LinearBands.closedBand, SimplexFacetSharpExample.lo,
          SimplexFacetSharpExample.hi] using And.intro h hx.1.2
      have hl (i) : r i < x i := by
        apply lt_of_not_ge
        intro h
        exact hx.2 (mem_iUnion.mpr ⟨some i, hx.1.1 i, h⟩)
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hl i).le)
      linarith only [hs, hu, heq]
    simp [hempty, heq, Fintype.card_ne_zero]

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

omit [FiniteDimensional ℝ E] in
/-- A constant directional width is the minimum width. The hypothesis is
the usual homogeneous form of constant width, including nonunit normals. -/
theorem minWidth_eq_of_constant_width (K : ConvexBody E) (w : ℝ)
    (hw : ∀ u : E, u ≠ 0 → widthAlong (K : Set E) u = w * ‖u‖) :
    minWidth (K : Set E) = w := by
  have himage : (fun u => widthAlong (K : Set E) u / ‖u‖) ''
      {u : E | u ≠ 0} = {w} := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      simp only [hw u hu, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hu), mem_singleton_iff]
    · intro hy
      obtain ⟨u, hu⟩ := exists_ne (0 : E)
      refine ⟨u, hu, ?_⟩
      change widthAlong (K : Set E) u / ‖u‖ = y
      rw [hw u hu, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hu)]
      exact (mem_singleton_iff.mp hy).symm
  unfold minWidth
  rw [himage, csInf_singleton]

variable [MeasurableSpace E] [BorelSpace E] [Fintype ι]

/-- Bang's Euclidean volume bound becomes the direction-relative bound on
a constant-width body, for every finite indexed family of planks. -/
theorem constant_width_bound (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : ConvexBody E) {w : ℝ} (hw : 0 < w)
    (hconstant : ∀ u : E, u ≠ 0 → widthAlong (K : Set E) u = w * ‖u‖)
    (u : ι → E) (hu : ∀ i, ‖u i‖ = 1)
    (lo hi : ι → ℝ) (horder : ∀ i, lo i ≤ hi i) :
    (ENNReal.ofReal (max 0
      (1 - ∑ i, (hi i-lo i)/widthAlong (K : Set E) (u i)))) ^
      Module.finrank ℝ E * μ (K : Set E) ≤
      μ ((K : Set E) \ ⋃ i,
        LinearBands.closedBand (fun z => ⟪u i, z⟫) (lo i) (hi i)) := by
  have hmin := minWidth_eq_of_constant_width K w hconstant
  have hdir (i) : widthAlong (K : Set E) (u i) = w := by
    have hne : u i ≠ 0 := norm_ne_zero_iff.mp (by rw [hu i]; norm_num)
    rw [hconstant _ hne, hu i, mul_one]
  simpa only [hdir, ← Finset.sum_div, hmin] using
    BangVolume.measure_gap_ge_of_minWidth μ K (hmin.symm ▸ hw) u hu lo hi horder

omit [Nontrivial E] [Fintype ι] in
/-- The uncovered fraction itself, and not only the defect, is affine
invariant. Consequently every proved direction-relative bound transports
to every simultaneous affine image of its body and planks. -/
theorem uncovered_fraction_pull (μ : Measure E) [μ.IsAddHaarMeasure]
    (F : E ≃ᵃ[ℝ] E) (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) :
    μ.real ((F ⁻¹' K) \ PrunedPlankCounterexample.covered
      (fun i => FinitePlankAffineTransport.pull F (f i)) lo hi) /
        μ.real (F ⁻¹' K) =
    μ.real (K \ PrunedPlankCounterexample.covered f lo hi) / μ.real K := by
  rw [FinitePlankAffineTransport.gap_pull, FinitePlankAffineTransport.volume_preimage,
    mul_div_mul_left _ _ (FinitePlankAffineTransport.volumeScale_pos F).ne']

omit [Nontrivial E] in
/-- Any proved power bound transfers to the simultaneous affine image. -/
theorem relative_bound_pull (μ : Measure E) [μ.IsAddHaarMeasure]
    (F : E ≃ᵃ[ℝ] E) (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (d : ℕ)
    (hbound : (max 0 (1 - PrunedPlankCounterexample.budget K f lo hi))^d ≤
      μ.real (K \ PrunedPlankCounterexample.covered f lo hi) / μ.real K) :
    (max 0 (1 - PrunedPlankCounterexample.budget (F ⁻¹' K)
      (fun i => FinitePlankAffineTransport.pull F (f i)) lo hi))^d ≤
      μ.real ((F ⁻¹' K) \ PrunedPlankCounterexample.covered
        (fun i => FinitePlankAffineTransport.pull F (f i)) lo hi) /
          μ.real (F ⁻¹' K) := by
  simpa only [FinitePlankAffineTransport.budget_pull, uncovered_fraction_pull] using hbound

end Plank.JournalQuantitativeCorollaries
