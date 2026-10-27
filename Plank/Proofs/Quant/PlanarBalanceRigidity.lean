/- Rigidity of the actual one-window Euler balance. -/
module

public import Plank.Proofs.Quant.ConcaveDensitySlack
public import Plank.Proofs.Quant.ActualConcaveWindows
public import Plank.Proofs.Quant.PlanarOnePlankClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarBalanceRigidity

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarSevenCellArea
open PlanarBodySectionDensity ActualConcaveWindows ConcaveDensity intervalIntegral
open Plank.Convex.DeficientHeightTilt

/-- A zero Euler slack for an actual normalized window gives actual
one-plank equality. The section-density certificate is an explicit hypothesis. -/
theorem gap_eq_of_balance_eq {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (D : BodySectionDensity K f)
    (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) (hunit : rangeWidth K f = 1)
    {c r : ℝ} (hc : c ∈ Icc 0 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (he : 2*coveredArea K f ((1-r)*c) (c+(1-c)*r) =
      r*canonicalDensity D.density c r+2*r*(volume K).toReal) :
    (volume (K \ plank f ((1-r)*c) (c+(1-c)*r))).toReal =
      (1-r)^2*(volume K).toReal := by
  have hf : f.linear ≠ 0 := linear_ne_zero_of_rangeWidth_pos hne f (by
    rw [hunit]; norm_num)
  have hmass : mass (canonicalDensity D.density c) = (volume K).toReal := by
    rw [mass_canonicalDensity _ D.continuous,density_mass hK f hf D hnorm]
  have harea : (∫ w in 0..r, canonicalDensity D.density c w) =
      coveredArea K f ((1-r)*c) (c+(1-c)*r) := by
    rw [integral_canonicalDensity _ D.continuous,
      coveredArea_eq_integral hK f hf D
        (mul_nonneg (sub_nonneg.mpr hr1.le) hc.1) (by nlinarith only [hr0])]
  have hh := ConcaveDensitySlack.integral_eq_of_balance_eq
    (canonicalDensity D.density c) (continuous_canonicalDensity _ D.continuous c)
    (concaveOn_canonicalDensity _ (D.concave_unit hK hconv hne hnorm hunit) hc)
    (canonicalDensity_endpoint_nonneg _ (D.nonnegative 0) (D.nonnegative 1) hc)
    hr0 hr1 (by rwa [hmass,harea])
  rw [hmass,harea] at hh
  have hd := measureReal_sdiff_add_inter (μ := volume) (s := K)
    (isClosed_plank f ((1-r)*c) (c+(1-c)*r)).measurableSet hK.measure_ne_top
  change (volume (K \ plank f ((1-r)*c) (c+(1-c)*r))).toReal+
    coveredArea K f ((1-r)*c) (c+(1-c)*r) = (volume K).toReal at hd
  nlinarith only [hh,hd]

/-- Saturation of the actual Euler balance forces the original convex
body to have at most four vertices, for every positive window width below one.
No affine-density or polygon premise is assumed. -/
theorem four_vertices_of_balance_eq {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (D : BodySectionDensity K f)
    (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) (hunit : rangeWidth K f = 1)
    {c r : ℝ} (hc : c ∈ Icc 0 1) (hr0 : 0 < r) (hr1 : r < 1)
    (he : 2*coveredArea K f ((1-r)*c) (c+(1-c)*r) =
      r*canonicalDensity D.density c r+2*r*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  have hw : c+(1-c)*r-(1-r)*c = r := by ring
  apply PlanarOnePlankClassification.equality_implies_four_vertices hK hconv hne hV
    f ((1-r)*c) (c+(1-c)*r) (sub_pos.mp (by rwa [hw]))
    (by rw [hunit]; norm_num) (by rwa [hw,hunit,div_one])
  rw [hw,hunit,div_one]
  exact gap_eq_of_balance_eq hK hconv hne f D hnorm hunit hc hr0.le hr1 he

end Plank.PlanarBalanceRigidity

/-- info: 'Plank.PlanarBalanceRigidity.four_vertices_of_balance_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarBalanceRigidity.four_vertices_of_balance_eq
