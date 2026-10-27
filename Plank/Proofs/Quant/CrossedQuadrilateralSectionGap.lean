/- Uniform inefficiency of every fixed non-diagonal direction. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSurvivingDirections
public import Plank.Proofs.Quant.PlanarSmallBudgetGap

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSectionGap
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarUnitSectionDensity PlanarSevenCellArea PlanarBodySectionDensity
  ConcaveDensity intervalIntegral CrossedQuadrilateralImageStrata PlanarEqualityReductions
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- A section of maximal possible length gives an actual sharp half-width
window, whose direction must be a diagonal of the genuine quadrilateral. -/
theorem diagonal_of_peak {K : Set Point} (hK : IsCompact K)
    (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point)
    (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Point →ᵃ[ℝ] ℝ) (D : UnitSectionDensity K f)
    (hunit : rangeWidth K f = 1) {c : ℝ} (hc : c ∈ Icc 0 1)
    (he : D.density c = 2*(volume K).toReal) :
    f.linear (T.linear ![1,0]) = 0 ∨ f.linear (T.linear ![0,1]) = 0 := by
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
  change coveredArea K f lo hi = _ at hh
  let g : Fin 1 → Point →ᵃ[ℝ] ℝ := fun _ => f
  let p : Endpoints 1 := (fun _ => lo,fun _ => hi)
  have hb : budget K g p = 1/2 := by
    simp only [budget,Fin.sum_univ_one,g,p,hunit,div_one,hw]
  have hgap : gapArea K g p = (volume (K \ plank f lo hi)).toReal := by
    simp [gapArea,g,p,plank,iUnion_const]
  have hEq : Equality K g p := by
    change gapArea K g p = (max 0 (1-budget K g p))^2*(volume K).toReal
    rw [hb,hgap]
    norm_num
    nlinarith only [hd,hh]
  exact CrossedQuadrilateralSurvivingDirections.single_in_chart S T hbody g p
    (fun _ => by change 0 < rangeWidth K f; rw [hunit]; norm_num)
    (by rw [hb]; norm_num) hEq 0 (sub_pos.mp (by change 0 < hi-lo; rw [hw]; norm_num))
    (fun i hi => False.elim (hi (Subsingleton.elim _ _)))

/-- A fixed non-diagonal direction has a uniform strict section bound over
every position. This controls actual covered area, including null windows. -/
theorem strict_window_bound {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point)
    (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Point →ᵃ[ℝ] ℝ) (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (hunit : rangeWidth K f = 1)
    (hbad : ¬(f.linear (T.linear ![1,0]) = 0 ∨ f.linear (T.linear ![0,1]) = 0)) :
    ∃ M : ℝ, M < 2*(volume K).toReal ∧
      ∀ lo hi, 0 ≤ lo → lo ≤ hi → hi ≤ 1 →
        coveredArea K f lo hi ≤ M*(hi-lo) := by
  obtain ⟨D⟩ := exists_unitSectionDensity hK hconv hne hV f hnorm hunit
  obtain ⟨c,hc,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩) D.continuous.continuousOn
  refine ⟨D.density c,lt_of_le_of_ne (PlanarSectionPeakRigidity.density_le_twice_area D hc) ?_,?_⟩
  · intro he
    exact hbad (diagonal_of_peak hK S T hbody f D hunit hc he)
  · intro lo hi hlo ho hhi
    rw [D.area_integral lo hi hlo ho hhi]
    have hh := integral_mono_on (μ := volume) ho (D.continuous.intervalIntegrable lo hi)
      (intervalIntegrable_const (c := D.density c))
      (fun t ht => hmax ⟨hlo.trans ht.1,ht.2.trans hhi⟩)
    rw [intervalIntegral.integral_const] at hh
    simpa only [smul_eq_mul,mul_comm] using hh

/-- Three fixed non-diagonal directions cannot give equality at arbitrarily
small positive actual budgets, uniformly over all placements and overlaps. -/
theorem positive_budget_gap {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point)
    (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hbad : ∀ i, ¬((f i).linear (T.linear ![1,0]) = 0 ∨
      (f i).linear (T.linear ![0,1]) = 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ domain K f, 0 < budget K f p →
      gapArea K f p = (1-budget K f p)^2*(volume K).toReal → ε ≤ budget K f p := by
  choose M hM hbound using fun i =>
    strict_window_bound hK hc hne hV S T hbody (f i) (hnorm i) (hunit i) (hbad i)
  let B := max (M 0) (max (M 1) (M 2))
  have hB : B < 2*(volume K).toReal := max_lt (hM 0) (max_lt (hM 1) (hM 2))
  have hMB (i : Fin 3) : M i ≤ B := by
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨(2*(volume K).toReal-B)/(volume K).toReal,div_pos (sub_pos.mpr hB) hV,?_⟩
  intro p hp hR he
  have hsum : (∑ i, (p.2 i-p.1 i)) = budget K f p := by
    unfold budget
    simp only [hunit,div_one]
  have hu := (PlanarSmallBudgetGap.covered_le_sum hK f p).trans
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (hbound i _ _ (hp.1 i).1 (hp.1 i).2.1 (hp.1 i).2.2).trans
        (mul_le_mul_of_nonneg_right (hMB i) (sub_nonneg.mpr (hp.1 i).2.1))))
  rw [← Finset.mul_sum,hsum,he] at hu
  apply (div_le_iff₀ hV).mpr
  have hh : budget K f p*(2*(volume K).toReal-B-budget K f p*(volume K).toReal) ≤ 0 := by
    nlinarith only [hu]
  have hz := nonpos_of_mul_nonpos_right hh hR
  linarith only [hz]

end Quant.CrossedQuadrilateralSectionGap

/-- info: 'Quant.CrossedQuadrilateralSectionGap.positive_budget_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSectionGap.positive_budget_gap
