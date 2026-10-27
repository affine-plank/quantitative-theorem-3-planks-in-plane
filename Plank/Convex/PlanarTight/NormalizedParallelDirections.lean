/- Parallel affine functions with actual unit ranges differ only by reflection. -/
module
public import Plank.Convex.PlanarTight.OrientedCommonChord
public import Plank.Convex.ThreePlanarDirections
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.NormalizedParallelDirections
open TwoPlankClassification (reflect)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem linear_ne_zero (K : Set E) (X : E →ᵃ[ℝ] ℝ)
    (hL : ∃ x ∈ K, X x = 0) (hU : ∃ x ∈ K, X x = 1) : X.linear ≠ 0 := by
  intro hz
  obtain ⟨c, hc⟩ := X.linear_eq_zero_iff_exists_const.mp hz
  obtain ⟨x, _, hx⟩ := hL
  obtain ⟨y, _, hy⟩ := hU
  rw [hc] at hx hy
  simp only [AffineMap.const_apply] at hx hy
  linarith only [hx, hy]

private theorem affine_relation (X Y : E →ᵃ[ℝ] ℝ) (hX : X.linear ≠ 0)
    (hdep : ¬ LinearIndependent ℝ ![X.linear, Y.linear]) :
    ∃ a c : ℝ, ∀ x, Y x = a * X x + c := by
  have hdep' : ¬ LinearIndependent ℝ ![Y.linear, X.linear] := by
    rwa [LinearIndependent.pair_symm_iff]
  rw [linearIndependent_fin2] at hdep'
  have hex : ∃ a : ℝ, a • X.linear = Y.linear := by
    by_contra! hn
    exact hdep' ⟨hX, hn⟩
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, Y 0 - a * X 0, fun x => ?_⟩
  have hXx : X x = X.linear x + X 0 := by simpa using X.map_vadd (0 : E) x
  have hYx : Y x = Y.linear x + Y 0 := by simpa using Y.map_vadd (0 : E) x
  rw [← ha] at hYx
  simp only [LinearMap.smul_apply, smul_eq_mul] at hYx
  rw [hXx, hYx]
  ring

/-- With both actual ranges equal to `[0,1]`, parallel directions are
the same affine function or its unit reflection, globally on the ambient space. -/
theorem eq_or_reflect (K : Set E) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ x ∈ K, (0 ≤ X x ∧ X x ≤ 1) ∧ (0 ≤ Y x ∧ Y x ≤ 1))
    (hXL : ∃ x ∈ K, X x = 0) (hXU : ∃ x ∈ K, X x = 1)
    (hYL : ∃ x ∈ K, Y x = 0) (hYU : ∃ x ∈ K, Y x = 1)
    (hdep : ¬ LinearIndependent ℝ ![X.linear, Y.linear]) :
    Y = X ∨ Y = reflect X := by
  obtain ⟨a, c, hrel⟩ := affine_relation X Y (linear_ne_zero K X hXL hXU) hdep
  obtain ⟨L, hL, hXL⟩ := hXL
  obtain ⟨U, hU, hXU⟩ := hXU
  obtain ⟨B, hB, hYB⟩ := hYL
  obtain ⟨T, hT, hYT⟩ := hYU
  have hL' := hrel L
  have hU' := hrel U
  have hB' := hrel B
  have hT' := hrel T
  rw [hXL, mul_zero, zero_add] at hL'
  rw [hXU, mul_one] at hU'
  rw [hYB] at hB'
  rw [hYT] at hT'
  have hc0 : 0 ≤ c := hL' ▸ (hbox L hL).2.1
  have hc1 : c ≤ 1 := hL' ▸ (hbox L hL).2.2
  have hac0 : 0 ≤ a + c := hU' ▸ (hbox U hU).2.1
  have hac1 : a + c ≤ 1 := hU' ▸ (hbox U hU).2.2
  rcases le_total 0 a with ha | ha
  · have hc : c = 0 := by
      have hprod := mul_nonneg ha (hbox B hB).1.1
      linarith only [hB', hc0, hprod]
    have hae : a = 1 := by
      have hprod := mul_le_mul_of_nonneg_left (hbox T hT).1.2 ha
      nlinarith only [hT', hc, hac1, hprod]
    left
    ext x
    rw [hrel x, hae, hc, one_mul, add_zero]
  · have hc : c = 1 := by
      have hprod := mul_nonpos_of_nonpos_of_nonneg ha (hbox T hT).1.1
      linarith only [hT', hc1, hprod]
    have hae : a = -1 := by
      have hprod := mul_le_mul_of_nonpos_left (hbox B hB).1.2 ha
      nlinarith only [hB', hc, hac0, hprod]
    right
    ext x
    rw [hrel x, hae, hc, TwoPlankClassification.reflect_apply]
    ring

end Plank.Convex.PlanarTight.NormalizedParallelDirections

/-- info: 'Plank.Convex.PlanarTight.NormalizedParallelDirections.eq_or_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.NormalizedParallelDirections.eq_or_reflect
