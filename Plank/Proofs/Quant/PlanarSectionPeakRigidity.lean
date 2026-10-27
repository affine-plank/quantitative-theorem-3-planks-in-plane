/- A maximally efficient section forces an actual four-point body. -/
module

public import Plank.Proofs.Quant.ConcaveDensityPeak
public import Plank.Proofs.Quant.PlanarUnitWindowRigidity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSectionPeakRigidity

open Set MeasureTheory PlanarQuantitative PlanarUnitSectionDensity
open PlanarSevenCellArea PlanarBodySectionDensity ConcaveDensity intervalIntegral
open Plank.Convex.DeficientHeightTilt

theorem density_le_twice_area {K : Set Point} {f : Point →ᵃ[ℝ] ℝ}
    (D : UnitSectionDensity K f) {c : ℝ} (hc : c ∈ Icc 0 1) :
    D.density c ≤ 2*(volume K).toReal := by
  have hh := ConcaveDensityPeak.start_le_twice_mass (canonicalDensity D.density c)
    (continuous_canonicalDensity _ D.continuous c)
    (concaveOn_canonicalDensity _ D.concave hc)
    (canonicalDensity_endpoint_nonneg _ (D.nonnegative 0) (D.nonnegative 1) hc)
  rw [mass_canonicalDensity _ D.continuous,D.mass_eq] at hh
  simpa only [canonicalDensity,sub_zero,one_mul,mul_zero,add_zero,
    ← add_mul,add_sub_cancel] using hh

/-- This is geometric rigidity, not merely a scalar density optimizer:
a section of twice the body area gives an actual sharp half-width plank,
so the original body is the convex hull of at most four points. -/
theorem four_vertices_of_peak_eq {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (D : UnitSectionDensity K f)
    (hunit : rangeWidth K f = 1) {c : ℝ} (hc : c ∈ Icc 0 1)
    (he : D.density c = 2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  have hstart : canonicalDensity D.density c 0 =
      2*mass (canonicalDensity D.density c) := by
    rw [mass_canonicalDensity _ D.continuous,D.mass_eq]
    simpa only [canonicalDensity,sub_zero,one_mul,mul_zero,add_zero,
      ← add_mul,add_sub_cancel] using he
  have hh := ConcaveDensityPeak.integral_eq_of_start_eq (canonicalDensity D.density c)
    (continuous_canonicalDensity _ D.continuous c)
    (concaveOn_canonicalDensity _ D.concave hc)
    (canonicalDensity_endpoint_nonneg _ (D.nonnegative 0) (D.nonnegative 1) hc)
    hstart (show (1/2 : ℝ) ∈ Icc 0 1 by norm_num)
  rw [mass_canonicalDensity _ D.continuous,D.mass_eq,
    PlanarUnitWindowRigidity.integral_canonical D hc (by norm_num : (1/2 : ℝ) ∈ Icc 0 1)] at hh
  let lo := (1-(1/2 : ℝ))*c
  let hi := c+(1-c)*(1/2 : ℝ)
  have hw : hi-lo = 1/2 := by dsimp [hi,lo]; ring
  have hd := measureReal_sdiff_add_inter (μ := volume) (s := K)
    (isClosed_plank f lo hi).measurableSet hK.measure_ne_top
  change (volume (K \ plank f lo hi)).toReal+coveredArea K f lo hi =
    (volume K).toReal at hd
  apply PlanarOnePlankClassification.equality_implies_four_vertices hK hconv hne hV
    f lo hi (sub_pos.mp (by rw [hw]; norm_num)) (by rw [hunit]; norm_num)
    (by rw [hw,hunit]; norm_num)
  change (volume (K \ plank f lo hi)).toReal =
    (1-(hi-lo)/rangeWidth K f)^2*(volume K).toReal
  rw [hw,hunit]
  change coveredArea K f lo hi = _ at hh
  nlinarith only [hh,hd]

/-- On a body outside the four-point class, compactness makes the strict
section bound uniform over every placement in a fixed direction. -/
theorem exists_strict_window_bound {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (hunit : rangeWidth K f = 1)
    (hnf : ¬∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) :
    ∃ M : ℝ, M < 2*(volume K).toReal ∧
      ∀ lo hi, 0 ≤ lo → lo ≤ hi → hi ≤ 1 →
        coveredArea K f lo hi ≤ M*(hi-lo) := by
  obtain ⟨D⟩ := exists_unitSectionDensity hK hconv hne hV f hnorm hunit
  obtain ⟨c,hc,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩) D.continuous.continuousOn
  refine ⟨D.density c,lt_of_le_of_ne (density_le_twice_area D hc) ?_,?_⟩
  · intro he
    exact hnf (four_vertices_of_peak_eq hK hconv hne hV f D hunit hc he)
  · intro lo hi hlo ho hhi
    rw [D.area_integral lo hi hlo ho hhi]
    have hh := integral_mono_on (μ := volume) ho (D.continuous.intervalIntegrable lo hi)
      (intervalIntegrable_const (c := D.density c))
      (fun t ht => hmax ⟨hlo.trans ht.1,ht.2.trans hhi⟩)
    rw [intervalIntegral.integral_const] at hh
    simpa only [smul_eq_mul,mul_comm] using hh

end Plank.PlanarSectionPeakRigidity

/-- info: 'Plank.PlanarSectionPeakRigidity.four_vertices_of_peak_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSectionPeakRigidity.four_vertices_of_peak_eq
/-- info: 'Plank.PlanarSectionPeakRigidity.exists_strict_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSectionPeakRigidity.exists_strict_window_bound
