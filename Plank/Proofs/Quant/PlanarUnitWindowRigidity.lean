/- Actual canonical windows require no derivative across a support face. -/
module

public import Plank.Proofs.Quant.PlanarUnitSectionDensity
public import Plank.Proofs.Quant.ConcaveDensitySlack
public import Plank.Proofs.Quant.PlanarOnePlankClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarUnitWindowRigidity

open Set MeasureTheory Filter Topology PlanarQuantitative PlanarGapCells
open PlanarBodySectionDensity PlanarUnitSectionDensity PlanarSevenCellArea
open ConcaveDensity intervalIntegral
open Plank.Convex.DeficientHeightTilt

theorem integral_canonical {K : Set Point} {f : Point →ᵃ[ℝ] ℝ}
    (D : UnitSectionDensity K f) {c r : ℝ} (hc : c ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (∫ t in 0..r, canonicalDensity D.density c t) =
      coveredArea K f ((1-r)*c) (c+(1-c)*r) := by
  rw [integral_canonicalDensity _ D.continuous]
  apply (D.area_integral _ _ (mul_nonneg (sub_nonneg.mpr hr.2) hc.1)
    (by nlinarith only [hr.1]) ?_).symm
  nlinarith only [mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hr.2)]

/-- The actual canonical motion is differentiable even when one edge is
a supporting face: that edge remains fixed along this motion. -/
theorem canonical_line_deriv {K : Set Point} {f : Point →ᵃ[ℝ] ℝ}
    (D : UnitSectionDensity K f) {c r : ℝ} (hc : c ∈ Icc 0 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun t => coveredArea K f ((1-r)*c+t*(-r*c))
      (c+(1-c)*r+t*(r*(1-c)))) (r*canonicalDensity D.density c r) 0 := by
  have hp : HasDerivAt (fun t : ℝ => (1+t)*r) r 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const r using 1
    simp
  have hprim : HasDerivAt (fun u => ∫ x in 0..u, canonicalDensity D.density c x)
      (canonicalDensity D.density c r) ((1+0)*r) := by
    simpa only [add_zero,one_mul] using
      ((continuous_canonicalDensity D.density D.continuous c).integral_hasStrictDerivAt 0 r).hasDerivAt
  have hd := hprim.comp 0 hp
  rw [mul_comm] at hd
  apply hd.congr_of_eventuallyEq
  have hnr : ∀ᶠ x : ℝ in 𝓝 r, x ∈ Ioo (0 : ℝ) 1 := isOpen_Ioo.mem_nhds ⟨hr0,hr1⟩
  have hn : ∀ᶠ t : ℝ in 𝓝 0, (1+t)*r ∈ Ioo (0 : ℝ) 1 :=
    hp.continuousAt.tendsto.eventually (by simpa only [add_zero,one_mul] using hnr)
  filter_upwards [hn] with t ht
  simp only [Function.comp_apply]
  rw [integral_canonical D hc ⟨ht.1.le,ht.2.le⟩]
  congr 1 <;> ring

theorem coveredArea_balance {K : Set Point} {f : Point →ᵃ[ℝ] ℝ}
    (D : UnitSectionDensity K f) {c r : ℝ} (hc : c ∈ Icc 0 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2*coveredArea K f ((1-r)*c) (c+(1-c)*r) ≤
      r*canonicalDensity D.density c r+2*r*(volume K).toReal := by
  have hh := integral_balance (canonicalDensity D.density c)
    (continuous_canonicalDensity _ D.continuous c)
    (concaveOn_canonicalDensity _ D.concave hc) hr0 hr1
  have hm : (∫ t in (0 : ℝ)..1, canonicalDensity D.density c t) =
      (volume K).toReal := by
    change mass (canonicalDensity D.density c) = _
    rw [mass_canonicalDensity _ D.continuous,D.mass_eq]
  rw [hm,integral_canonical D hc ⟨hr0,hr1.le⟩] at hh
  have hn := mul_nonneg hr0 (canonicalDensity_endpoint_nonneg _
    (D.nonnegative 0) (D.nonnegative 1) hc)
  linarith only [hh,hn]

theorem gap_eq_of_balance_eq {K : Set Point} (hK : IsCompact K)
    {f : Point →ᵃ[ℝ] ℝ} (D : UnitSectionDensity K f)
    {c r : ℝ} (hc : c ∈ Icc 0 1) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (he : 2*coveredArea K f ((1-r)*c) (c+(1-c)*r) =
      r*canonicalDensity D.density c r+2*r*(volume K).toReal) :
    (volume (K \ plank f ((1-r)*c) (c+(1-c)*r))).toReal =
      (1-r)^2*(volume K).toReal := by
  have hm : mass (canonicalDensity D.density c) = (volume K).toReal := by
    rw [mass_canonicalDensity _ D.continuous,D.mass_eq]
  have hh := ConcaveDensitySlack.integral_eq_of_balance_eq
    (canonicalDensity D.density c) (continuous_canonicalDensity _ D.continuous c)
    (concaveOn_canonicalDensity _ D.concave hc)
    (canonicalDensity_endpoint_nonneg _ (D.nonnegative 0) (D.nonnegative 1) hc)
    hr0 hr1 (by rwa [hm,integral_canonical D hc ⟨hr0,hr1.le⟩])
  rw [hm,integral_canonical D hc ⟨hr0,hr1.le⟩] at hh
  have hd := measureReal_sdiff_add_inter (μ := volume) (s := K)
    (isClosed_plank f ((1-r)*c) (c+(1-c)*r)).measurableSet hK.measure_ne_top
  change (volume (K \ plank f ((1-r)*c) (c+(1-c)*r))).toReal+
    coveredArea K f ((1-r)*c) (c+(1-c)*r) = (volume K).toReal at hd
  nlinarith only [hh,hd]

theorem four_vertices_of_balance_eq {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (D : UnitSectionDensity K f) (hunit : rangeWidth K f = 1)
    {c r : ℝ} (hc : c ∈ Icc 0 1) (hr0 : 0 < r) (hr1 : r < 1)
    (he : 2*coveredArea K f ((1-r)*c) (c+(1-c)*r) =
      r*canonicalDensity D.density c r+2*r*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  have hw : c+(1-c)*r-(1-r)*c = r := by ring
  apply PlanarOnePlankClassification.equality_implies_four_vertices hK hconv hne hV
    f ((1-r)*c) (c+(1-c)*r) (sub_pos.mp (by rwa [hw]))
    (by rw [hunit]; norm_num) (by rwa [hw,hunit,div_one])
  rw [hw,hunit,div_one]
  exact gap_eq_of_balance_eq hK D hc hr0.le hr1 he

end Plank.PlanarUnitWindowRigidity

/-- info: 'Plank.PlanarUnitWindowRigidity.canonical_line_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarUnitWindowRigidity.canonical_line_deriv
/-- info: 'Plank.PlanarUnitWindowRigidity.four_vertices_of_balance_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarUnitWindowRigidity.four_vertices_of_balance_eq
