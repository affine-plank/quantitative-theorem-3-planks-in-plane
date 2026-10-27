/- An integral Euler bound for actual stationary planar window charts.
The argument uses concavity and stationarity, but no second variation. -/
module

public import Plank.Proofs.Quant.ActualConcaveWindows
public import Plank.Proofs.Quant.CanonicalWindowMotion
public import Plank.Proofs.Quant.FiniteDimensionalCapFirstVariation
public import Plank.Proofs.Quant.PlanarCapChart

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.StationaryInteractionBalance

open Set MeasureTheory PlanarQuantitative PlanarPolygonCharts PlanarPositiveChart
open PlanarBodySectionDensity PlanarSeparableChart PlanarSevenCellSections
open PlanarGapCells
open QuadraticChartCalculus SupportAnchorBudget ActualSupportAnchor
open ActualConcaveWindows ConcaveDensity intervalIntegral
open PlanarParameterDomain (Endpoints budget)
open Plank.Convex.DeficientHeightTilt

/-- The section object identifies the derivative used in the cap inequality.
Only continuity and the actual section integral are needed here. -/
theorem coveredArea_hasDerivAt_canonical {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (D : BodySectionDensity K f)
    {c r : ℝ} (hc : c ∈ Icc 0 1) (hr : r ∈ Ioo 0 1) :
    HasDerivAt (fun s : ℝ => coveredArea K f ((1-s)*c) (c+(1-c)*s))
      (canonicalDensity D.density c r) r := by
  have hcont := continuous_canonicalDensity D.density D.continuous c
  have hd := integral_hasDerivAt_right (hcont.intervalIntegrable 0 r)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
  rw [integral_canonicalDensity D.density D.continuous]
  exact coveredArea_eq_integral hK f hf D
    (mul_nonneg (sub_pos.mpr hs.2).le hc.1) (by linarith only [hs.1])

/-- The finite cap ratio retains the weighted actual one-window surplus in
the stationary area estimate; no section concavity calculation is used. -/
theorem coveredArea_balance_with_weighted_excess {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (D : BodySectionDensity K f)
    (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) (hunit : rangeWidth K f = 1)
    {c r : ℝ} (hc : c ∈ Icc 0 1) (hr : r ∈ Ioo 0 1) :
    2*coveredArea K f ((1-r)*c) (c+(1-c)*r)+
      2/(2-r)*(FiniteDimensionalCapWindowScaling.gap K f c r-
        (1-r)^2*(volume K).toReal) ≤
      r*canonicalDensity D.density c r+2*r*(volume K).toReal := by
  have hf : f.linear ≠ 0 := linear_ne_zero_of_rangeWidth_pos hne f (by rw [hunit]; norm_num)
  have him := image_eq_unitInterval hK hconv hne f hnorm hunit
  have hzero : ∃ x ∈ K, f x=0 := by
    have h : (0 : ℝ) ∈ f '' K := by rw [him]; exact ⟨le_rfl,zero_le_one⟩
    exact h
  have hone : ∃ x ∈ K, f x=1 := by
    have h : (1 : ℝ) ∈ f '' K := by rw [him]; exact ⟨zero_le_one,le_rfl⟩
    exact h
  exact FiniteDimensionalCapFirstVariation.planar_balance_with_excess hK hconv f hf
    hzero hone hc hr (coveredArea_hasDerivAt_canonical hK f hf D hc hr)

/-- The actual area of one window is controlled by its canonical width
derivative and the total body area. The section density need not be smooth. -/
theorem coveredArea_balance {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (D : BodySectionDensity K f)
    (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) (hunit : rangeWidth K f = 1)
    {c r : ℝ} (hc : c ∈ Icc 0 1) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2*coveredArea K f ((1-r)*c) (c+(1-c)*r) ≤
      r*canonicalDensity D.density c r+2*r*(volume K).toReal := by
  have hf : f.linear ≠ 0 := linear_ne_zero_of_rangeWidth_pos hne f (by
    rw [hunit]; norm_num)
  rcases eq_or_lt_of_le hr0 with rfl | hr0
  · simp only [sub_zero,one_mul,mul_zero,add_zero,zero_mul]
    rw [coveredArea_eq_integral hK f hf D hc.1 le_rfl]
    simp
  have hh := coveredArea_balance_with_weighted_excess hK hconv hne f D hnorm hunit
    hc ⟨hr0,hr1⟩
  have him := image_eq_unitInterval hK hconv hne f hnorm hunit
  have hzero : ∃ x ∈ K, f x=0 := by
    have h : (0 : ℝ) ∈ f '' K := by rw [him]; exact ⟨le_rfl,zero_le_one⟩
    exact h
  have hone : ∃ x ∈ K, f x=1 := by
    have h : (1 : ℝ) ∈ f '' K := by rw [him]; exact ⟨zero_le_one,le_rfl⟩
    exact h
  have hE := FiniteDimensionalCapWindowScaling.gap_excess_nonneg (d := 1)
    hK hconv f hf hzero hone hc ⟨hr0.le,hr1.le⟩
  have hn := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (show 0 ≤ 2-r by linarith only [hr1])) hE
  norm_num only at hn
  linarith only [hh,hn]

/-- Continuity of actual covered area extends the identity to the chart limit.
The original density and endpoint hypotheses are retained for compatibility. -/
theorem identity_at_closure {m : ℕ} {K : Set Point} (hK : IsCompact K)
    {f : Fin m → Point →ᵃ[ℝ] ℝ} (hf : ∀ i, (f i).linear ≠ 0)
    (D : ∀ i, BodySectionDensity K (f i)) (S : SeparableAreaChart K f)
    (hlo : ∀ e ∈ S.region, ∀ i, 0 ≤ e.1 i)
    (e : Endpoints m) (he : e ∈ closure S.region)
    (he0 : ∀ i, 0 ≤ e.1 i) (heorder : ∀ i, e.1 i ≤ e.2 i) :
    S.formula.eval e = S.constant-∑ i, coveredArea K (f i) (e.1 i) (e.2 i) := by
  exact Set.EqOn.closure S.area_identity S.formula.continuous_eval (continuous_const.sub
    (continuous_finsetSum _ fun i _ =>
      PlanarCapChart.continuous_coveredArea_endpoints hK (f i) (hf i) i)) he

/-- The stationary argument retains any proved contribution to the
one-window section slack. No sign or curvature assumption on it is needed. -/
theorem margin_lower_bound_of_area_bounds {m : ℕ} {K : Set Point}
    {f : Fin m → Point →ᵃ[ℝ] ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (B : ℝ)
    (ch : PositiveMarginChart K f (PlanarShiftedDomain.domain K f B)
      (volume K).toReal (PlanarShiftedDomain.deficit K f B))
    (D : ∀ i, BodySectionDensity K (f i))
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (P : QuadraticFormula (Endpoints m))
    (hgap : ∀ e ∈ ch.region, e ∈ interior (PlanarShiftedDomain.domain K f B) →
      ch.gapFormula.eval e = (volume K).toReal-
        ∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+P.eval e)
    (J : Fin m → ℝ)
    (harea : ∀ i, 2*coveredArea K (f i) (ch.point.1 i) (ch.point.2 i)+J i ≤
      width ch.point i*canonicalDensity (D i).density (lowerWeight ch.point i) (width ch.point i)+
        2*width ch.point i*(volume K).toReal) :
    (volume K).toReal*(1-B)*(1+B-∑ i, width ch.point i)+P.eval ch.point-
        derivative P ch.point (∑ i, width ch.point i • velocity ch.point i)/2+(∑ i, J i)/2 ≤
      ch.marginFormula.eval ch.point := by
  let S : SeparableAreaChart K f := {
    region := ch.region ∩ interior (PlanarShiftedDomain.domain K f B)
    open_region := ch.open_region.inter isOpen_interior
    ordered := fun _ he => PlanarShiftedDomain.strict_windows_of_interior K f B he.2
    formula := subtractFormula ch.gapFormula P
    constant := (volume K).toReal
    area_identity := by
      intro e he
      rw [eval_subtractFormula, hgap e he.1 he.2]
      ring }
  have hc : ch.point ∈ closure S.region :=
    isOpen_interior.closure_inter ⟨ch.closure_point, ch.interior_point⟩
  have hends (i) : 0 < ch.point.1 i ∧ ch.point.2 i < 1 := by
    have h := endpoint_bounds_of_interior K f B ch.interior_point i
    exact ⟨h.1.1, h.2.2⟩
  have hs (i) : ch.point.1 i+(1-ch.point.2 i) ≠ 0 := ne_of_gt
    (add_pos (hends i).1 (sub_pos.mpr (hends i).2))
  let g (i) := canonicalDensity (D i).density (lowerWeight ch.point i) (width ch.point i)
  have hd (i) : g i = 2*(volume K).toReal*(B-∑ j, width ch.point j)+
      derivative P ch.point (velocity ch.point i) := by
    have hl := S.derivative_lower_at_closure D ch.point hc i
    have hu := S.derivative_upper_at_closure D ch.point hc i
    have hv := derivative_velocity S.formula ch.point ch.point i
    rw [hl, hu] at hv
    have hg : g i = lowerWeight ch.point i*(D i).density (ch.point.1 i)+
        upperWeight ch.point i*(D i).density (ch.point.2 i) := by
      dsimp only [g, canonicalDensity]
      rw [(ConcurrentAnchorFinish.canonical_endpoints ch.point hends i).1,
        (ConcurrentAnchorFinish.canonical_endpoints ch.point hends i).2,
        show 1-lowerWeight ch.point i = upperWeight ch.point i by
          linarith only [weights_add ch.point hs i]]
    change derivative (subtractFormula ch.gapFormula P) ch.point _ = _ at hv
    rw [derivative_subtractFormula] at hv
    have ht := congrArg (fun L : Endpoints m →L[ℝ] ℝ => L (velocity ch.point i))
      ch.stationary_gap
    change derivative ch.gapFormula ch.point (velocity ch.point i) =
      2*(volume K).toReal*(PlanarShiftedDomain.deficit K f B ch.point)*
        (PlanarShiftedDomain.deficit K f B).linear (velocity ch.point i) at ht
    rw [deficit_velocity B hunit ch.point hs, PlanarShiftedDomain.deficit_apply] at ht
    simp only [budget, hunit, div_one, sub_apply] at ht hv
    change derivative ch.gapFormula ch.point (velocity ch.point i) =
      2*(volume K).toReal*(B-∑ j, width ch.point j)*(-1) at ht
    linarith only [hg, hv, ht]
  have hi := harea
  change ∀ i, 2*coveredArea K (f i) (ch.point.1 i) (ch.point.2 i)+J i ≤
    width ch.point i*g i+2*width ch.point i*(volume K).toReal at hi
  simp_rw [hd] at hi
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  have hpoly := identity_at_closure hK
    (fun i => linear_ne_zero_of_rangeWidth_pos hne (f i) (by rw [hunit]; norm_num)) D S
    (fun e he i => (endpoint_bounds_of_interior K f B he.2 i).1.1.le) ch.point hc
    (fun i => (hends i).1.le) (fun i => (ch.strict_windows i).le)
  change (subtractFormula ch.gapFormula P).eval ch.point =
    (volume K).toReal-∑ i, coveredArea K (f i) (ch.point.1 i) (ch.point.2 i) at hpoly
  rw [eval_subtractFormula] at hpoly
  have hm := ch.margin_identity ch.point
  rw [PlanarShiftedDomain.deficit_apply] at hm
  simp only [budget, hunit, div_one] at hm
  change ch.marginFormula.eval ch.point = ch.gapFormula.eval ch.point-
    (volume K).toReal*(B-∑ j, width ch.point j)^2 at hm
  simp only [map_sum, map_smul, smul_eq_mul]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul] at hsum
  nlinarith only [hsum, hpoly, hm]

/-- Any finite family with an actual interaction polynomial satisfies this
stationary margin bound. The interaction is evaluated on the simultaneous
canonical width motion; no curvature or qualitative covering input is used. -/
theorem margin_lower_bound {m : ℕ} {K : Set Point} {f : Fin m → Point →ᵃ[ℝ] ℝ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) (B : ℝ)
    (ch : PositiveMarginChart K f (PlanarShiftedDomain.domain K f B)
      (volume K).toReal (PlanarShiftedDomain.deficit K f B))
    (D : ∀ i, BodySectionDensity K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (P : QuadraticFormula (Endpoints m))
    (hgap : ∀ e ∈ ch.region, e ∈ interior (PlanarShiftedDomain.domain K f B) →
      ch.gapFormula.eval e = (volume K).toReal-
        ∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+P.eval e) :
    (volume K).toReal*(1-B)*(1+B-∑ i, width ch.point i)+P.eval ch.point-
        derivative P ch.point (∑ i, width ch.point i • velocity ch.point i)/2 ≤
      ch.marginFormula.eval ch.point := by
  clear D
  exact PlanarCapChart.margin_lower_bound hK hconv hne B ch hnorm hunit P hgap

/-- Every finite stationary family retains its actual width-weighted
single-window surplus. The interaction remainder remains explicit. -/
theorem margin_lower_bound_with_weighted_excess {m : ℕ} {K : Set Point}
    {f : Fin m → Point →ᵃ[ℝ] ℝ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) (B : ℝ)
    (ch : PositiveMarginChart K f (PlanarShiftedDomain.domain K f B)
      (volume K).toReal (PlanarShiftedDomain.deficit K f B))
    (D : ∀ i, BodySectionDensity K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (P : QuadraticFormula (Endpoints m))
    (hgap : ∀ e ∈ ch.region, e ∈ interior (PlanarShiftedDomain.domain K f B) →
      ch.gapFormula.eval e = (volume K).toReal-
        ∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+P.eval e) :
    (volume K).toReal*(1-B)*(1+B-∑ i, width ch.point i)+P.eval ch.point-
      derivative P ch.point (∑ i, width ch.point i • velocity ch.point i)/2+
      (∑ i, 2/(2-width ch.point i)*
        ((volume K).toReal-coveredArea K (f i) (ch.point.1 i) (ch.point.2 i)-
          (1-width ch.point i)^2*(volume K).toReal))/2 ≤
      ch.marginFormula.eval ch.point := by
  clear D
  exact PlanarCapChart.margin_lower_bound_with_weighted_excess hK hconv hne B ch
    hnorm hunit P hgap

end Plank.StationaryInteractionBalance
