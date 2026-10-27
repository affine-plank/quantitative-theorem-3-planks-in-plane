/- Total cap first variation on open charts and their closure points. -/
module
public import Plank.Proofs.Quant.CanonicalWindowMotion
public import Plank.Proofs.Quant.FiniteDimensionalCapFirstVariation

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCapChart

open Set MeasureTheory Filter PlanarQuantitative PlanarPolygonCharts PlanarGapCells
open PlanarBodySectionDensity PlanarSeparableChart QuadraticChartCalculus PlanarSevenCellSections
open SupportAnchorBudget ActualSupportAnchor PlanarPositiveChart
open PlanarParameterDomain (Endpoints budget)
open Plank.Convex.DeficientHeightTilt
open scoped Topology

/-- Continuity of actual covered area follows from null endpoint levels,
without constructing a section density. -/
theorem continuous_coveredArea {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) :
    Continuous (fun p : ℝ × ℝ => coveredArea K f p.1 p.2) := by
  have h := FiniteBandContinuity.continuous_area_uncovered volume hK.measurableSet
    hK.measure_ne_top (f := fun _ : Fin 1 => (f : Point → ℝ))
    (fun _ => (continuous_form f).measurable) (fun _ => measure_level_zero f hf)
  have hp : Continuous (fun p : ℝ × ℝ =>
      ((fun _ : Fin 1 => p.1), (fun _ : Fin 1 => p.2))) := by fun_prop
  have hc := (continuous_const : Continuous (fun _ : ℝ × ℝ => (volume K).toReal)).sub
    (h.comp hp)
  convert hc using 1
  funext p
  have he := measureReal_inter_add_sdiff (μ := volume) (s := K)
    (t := {x | p.1 ≤ f x ∧ f x ≤ p.2})
    ((isClosed_le continuous_const (continuous_form f)).inter
      (isClosed_le (continuous_form f) continuous_const)).measurableSet hK.measure_ne_top
  simpa only [coveredArea, PlanarSevenCellArea.plank, FiniteBandContinuity.uncovered,
    LinearBands.closedBand, iUnion_const, Measure.real, Function.comp_def, Pi.sub_apply]
    using (eq_sub_iff_add_eq.mpr he)

theorem continuous_coveredArea_endpoints {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (i : Fin m) :
    Continuous (fun e : Endpoints m => coveredArea K f (e.1 i) (e.2 i)) :=
  (continuous_coveredArea hK f hf).comp
    (show Continuous (fun e : Endpoints m => (e.1 i, e.2 i)) by fun_prop)

theorem continuousAt_motion {m : ℕ} (e : Endpoints m)
    (hs : ∀ i, e.1 i+(1-e.2 i) ≠ 0) :
    ContinuousAt (fun x : Endpoints m => ∑ i, width x i • velocity x i) e := by
  have heq : (fun x : Endpoints m => ∑ i, width x i • velocity x i) =
      (fun x => ((fun i => -width x i*lowerWeight x i),
        (fun i => width x i*upperWeight x i))) := by
    funext x
    apply Prod.ext <;> funext i
    · exact weighted_velocity_lower x i
    · exact weighted_velocity_upper x i
  rw [heq]
  apply ContinuousAt.prodMk
  · apply continuousAt_pi.mpr
    intro i
    exact (show ContinuousAt (fun x : Endpoints m => -width x i) e by
      unfold width; fun_prop).mul
      (ContinuousAt.div (by fun_prop) (by fun_prop) (hs i))
  · apply continuousAt_pi.mpr
    intro i
    exact (show ContinuousAt (fun x : Endpoints m => width x i) e by
      unfold width; fun_prop).mul
      (ContinuousAt.div (by fun_prop) (by fun_prop) (hs i))

theorem motion_endpoints {m : ℕ} (e : Endpoints m)
    (hends : ∀ i, 0 < e.1 i ∧ e.2 i < 1) (t : ℝ) (i : Fin m) :
    (e+(t-1) • (∑ j, width e j • velocity e j)).1 i =
        (1-t*width e i)*lowerWeight e i ∧
    (e+(t-1) • (∑ j, width e j • velocity e j)).2 i =
        lowerWeight e i+(1-lowerWeight e i)*(t*width e i) := by
  have he := ConcurrentAnchorFinish.canonical_endpoints e hends i
  have hw := weights_add e (fun j => ne_of_gt
    (add_pos (hends j).1 (sub_pos.mpr (hends j).2))) i
  change (e.1 i+(t-1)*(∑ j, width e j • velocity e j).1 i = _) ∧
    (e.2 i+(t-1)*(∑ j, width e j • velocity e j).2 i = _)
  rw [weighted_velocity_lower, weighted_velocity_upper, ← he.1, ← he.2,
    show upperWeight e i=1-lowerWeight e i by linarith only [hw]]
  constructor <;> ring

/-- Inside an open chart, its polynomial supplies the derivative of the
whole covered-area sum. The cap comparison supplies the inequality. -/
theorem total_balance_in_region {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (hzero : ∀ i, ∃ x ∈ K, f i x=0)
    (hone : ∀ i, ∃ x ∈ K, f i x=1)
    (U : Set (Endpoints m)) (hU : IsOpen U) (q : QuadraticFormula (Endpoints m))
    (hidentity : ∀ x ∈ U, q.eval x = (volume K).toReal-
      ∑ i, coveredArea K (f i) (x.1 i) (x.2 i))
    (e : Endpoints m) (he : e ∈ U)
    (hends : ∀ i, 0 < e.1 i ∧ e.2 i < 1) (horder : ∀ i, e.1 i < e.2 i) :
    (∑ i, 2*(1-width e i)/(2-width e i)*coveredArea K (f i) (e.1 i) (e.2 i)) ≤
      -derivative q e (∑ i, width e i • velocity e i) := by
  let W := ∑ i, width e i • velocity e i
  let path (t : ℝ) := e+(t-1) • W
  have hp : HasDerivAt path W 1 := by
    convert! (((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const W).const_add e using 1
    simp
  have hp1 : path 1=e := by simp [path]
  have hq := (hasFDerivAt_eval q e).comp_hasDerivAt_of_eq 1 hp hp1.symm
  have ht : Tendsto path (𝓝 1) (𝓝 e) := by
    have hh : Tendsto path (𝓝 1) (𝓝 (path 1)) := hp.continuousAt
    rwa [hp1] at hh
  have hd : HasDerivAt (fun t : ℝ => ∑ i,
      (volume (K ∩ {x | (1-t*width e i)*lowerWeight e i ≤ f i x ∧
        f i x ≤ lowerWeight e i+(1-lowerWeight e i)*(t*width e i)})).toReal)
      (-derivative q e W) 1 := by
    apply (hq.const_sub (volume K).toReal).congr_of_eventuallyEq
    filter_upwards [ht (hU.mem_nhds he)] with t htu
    have hid := hidentity (path t) htu
    simp only [path, W, (motion_endpoints e hends t _).1,
      (motion_endpoints e hends t _).2, coveredArea, PlanarSevenCellArea.plank] at hid
    dsimp only [Function.comp_def, path, W]
    linarith only [hid]
  have hr (i) : width e i ∈ Ioo (0 : ℝ) 1 := by
    unfold width
    exact ⟨sub_pos.mpr (horder i), by linarith only [(hends i).1,(hends i).2]⟩
  have hc (i) : lowerWeight e i ∈ Icc (0 : ℝ) 1 := by
    have hs := add_pos (hends i).1 (sub_pos.mpr (hends i).2)
    exact ⟨(div_pos (hends i).1 hs).le,
      (div_le_one hs).mpr (by linarith only [(hends i).2])⟩
  have hb := FiniteDimensionalCapFirstVariation.total_window_derivative_lower_bound
    hK hconv f hf hzero hone (lowerWeight e) (width e) hc hr hd
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_one] at hb
  have hcoef (i) : 2*width e i*(1-width e i)/(1-(1-width e i)^2) =
      2*(1-width e i)/(2-width e i) := by
    rw [show 1-(1-width e i)^2=width e i*(2-width e i) by ring]
    field_simp [ne_of_gt (hr i).1]
  simpa only [hcoef, (ConcurrentAnchorFinish.canonical_endpoints e hends _).1,
    (ConcurrentAnchorFinish.canonical_endpoints e hends _).2,
    coveredArea, PlanarSevenCellArea.plank, W] using hb

/-- The total cap inequality extends to a chart boundary using continuity of
actual areas and of the polynomial derivative. -/
theorem total_balance_at_closure {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (hzero : ∀ i, ∃ x ∈ K, f i x=0)
    (hone : ∀ i, ∃ x ∈ K, f i x=1)
    (U : Set (Endpoints m)) (hU : IsOpen U) (q : QuadraticFormula (Endpoints m))
    (hidentity : ∀ x ∈ U, q.eval x = (volume K).toReal-
      ∑ i, coveredArea K (f i) (x.1 i) (x.2 i))
    (hendsU : ∀ x ∈ U, ∀ i, 0 < x.1 i ∧ x.2 i < 1)
    (horderU : ∀ x ∈ U, ∀ i, x.1 i < x.2 i)
    (e : Endpoints m) (he : e ∈ closure U)
    (hends : ∀ i, 0 < e.1 i ∧ e.2 i < 1) :
    (∑ i, 2*(1-width e i)/(2-width e i)*coveredArea K (f i) (e.1 i) (e.2 i)) ≤
      -derivative q e (∑ i, width e i • velocity e i) := by
  have hleft : ContinuousAt (fun x : Endpoints m =>
      ∑ i, 2*(1-width x i)/(2-width x i)*coveredArea K (f i) (x.1 i) (x.2 i)) e := by
    apply tendsto_finsetSum
    intro i _
    apply ContinuousAt.mul
    · apply ContinuousAt.div
      · unfold width; fun_prop
      · unfold width; fun_prop
      · unfold width; linarith only [(hends i).1,(hends i).2]
    · exact (continuous_coveredArea_endpoints hK (f i) (hf i) i).continuousAt
  have hright : ContinuousAt (fun x : Endpoints m =>
      -derivative q x (∑ i, width x i • velocity x i)) e :=
    ((continuous_derivative q).continuousAt.clm_apply
      (continuousAt_motion e (fun i => ne_of_gt
        (add_pos (hends i).1 (sub_pos.mpr (hends i).2))))).neg
  exact ContinuousWithinAt.closure_le he hleft.continuousWithinAt hright.continuousWithinAt
    (fun x hx => total_balance_in_region hK hconv f hf hzero hone U hU q hidentity x hx
      (hendsU x hx) (horderU x hx))

/-- Actual areas extend the chart identity to its closure without section
primitives or ordered-endpoint assumptions at the limit. -/
theorem identity_at_closure {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (U : Set (Endpoints m)) (q : QuadraticFormula (Endpoints m))
    (hidentity : ∀ x ∈ U, q.eval x = (volume K).toReal-
      ∑ i, coveredArea K (f i) (x.1 i) (x.2 i))
    (e : Endpoints m) (he : e ∈ closure U) :
    q.eval e = (volume K).toReal-∑ i, coveredArea K (f i) (e.1 i) (e.2 i) := by
  exact Set.EqOn.closure hidentity q.continuous_eval (continuous_const.sub
    (continuous_finsetSum _ fun i _ => continuous_coveredArea_endpoints hK (f i) (hf i) i)) he

/-- The actual selected-chart bound uses total covered area, including at
the chart's closure point. Section-density objects are not hypotheses. -/
theorem margin_lower_bound_with_weighted_excess {m : ℕ} {K : Set Point}
    {f : Fin m → Point →ᵃ[ℝ] ℝ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) (B : ℝ)
    (ch : PositiveMarginChart K f (PlanarShiftedDomain.domain K f B)
      (volume K).toReal (PlanarShiftedDomain.deficit K f B))
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
  let U := ch.region ∩ interior (PlanarShiftedDomain.domain K f B)
  let q := subtractFormula ch.gapFormula P
  have hid : ∀ x ∈ U, q.eval x = (volume K).toReal-
      ∑ i, coveredArea K (f i) (x.1 i) (x.2 i) := by
    intro x hx
    dsimp only [q]
    rw [eval_subtractFormula, hgap x hx.1 hx.2]
    ring
  have hc : ch.point ∈ closure U :=
    isOpen_interior.closure_inter ⟨ch.closure_point, ch.interior_point⟩
  have hends (i) : 0 < ch.point.1 i ∧ ch.point.2 i < 1 := by
    have h := endpoint_bounds_of_interior K f B ch.interior_point i
    exact ⟨h.1.1,h.2.2⟩
  have hs (i) : ch.point.1 i+(1-ch.point.2 i) ≠ 0 := ne_of_gt
    (add_pos (hends i).1 (sub_pos.mpr (hends i).2))
  have hf (i) : (f i).linear ≠ 0 :=
    linear_ne_zero_of_rangeWidth_pos hne (f i) (by rw [hunit]; norm_num)
  have him (i) := image_eq_unitInterval hK hconv hne (f i) (hnorm i) (hunit i)
  have hzero (i) : ∃ x ∈ K, f i x=0 := by
    have h : (0 : ℝ) ∈ f i '' K := by rw [him]; exact ⟨le_rfl,zero_le_one⟩
    exact h
  have hone (i) : ∃ x ∈ K, f i x=1 := by
    have h : (1 : ℝ) ∈ f i '' K := by rw [him]; exact ⟨zero_le_one,le_rfl⟩
    exact h
  have hb := total_balance_at_closure hK hconv f hf hzero hone U
    (ch.open_region.inter isOpen_interior) q hid
    (fun x hx i => ⟨(endpoint_bounds_of_interior K f B hx.2 i).1.1,
      (endpoint_bounds_of_interior K f B hx.2 i).2.2⟩)
    (fun x hx => PlanarShiftedDomain.strict_windows_of_interior K f B hx.2)
    ch.point hc hends
  have hpoly := identity_at_closure hK f hf U q hid ch.point hc
  dsimp only [q] at hb hpoly
  rw [derivative_subtractFormula] at hb
  rw [eval_subtractFormula] at hpoly
  let W : Endpoints m := ∑ i, width ch.point i • velocity ch.point i
  have hW : (PlanarShiftedDomain.deficit K f B).linear W =
      -∑ i, width ch.point i := by
    simp only [W, map_sum, map_smul, deficit_velocity B hunit ch.point hs,
      smul_eq_mul, mul_neg_one, Finset.sum_neg_distrib]
  have ht := congrArg (fun L : Endpoints m →L[ℝ] ℝ => L W) ch.stationary_gap
  change derivative ch.gapFormula ch.point W =
    2*(volume K).toReal*(PlanarShiftedDomain.deficit K f B ch.point)*
      (PlanarShiftedDomain.deficit K f B).linear W at ht
  rw [hW, PlanarShiftedDomain.deficit_apply] at ht
  simp only [budget, hunit, div_one] at ht
  change derivative ch.gapFormula ch.point W =
    2*(volume K).toReal*(B-∑ i, width ch.point i)*(-∑ i, width ch.point i) at ht
  have hterm (i) : 2*(1-width ch.point i)/(2-width ch.point i)*
      coveredArea K (f i) (ch.point.1 i) (ch.point.2 i) =
      2*coveredArea K (f i) (ch.point.1 i) (ch.point.2 i)+
      2/(2-width ch.point i)*
        ((volume K).toReal-coveredArea K (f i) (ch.point.1 i) (ch.point.2 i)-
          (1-width ch.point i)^2*(volume K).toReal)-
      2*width ch.point i*(volume K).toReal := by
    have hd : 2-width ch.point i ≠ 0 := by
      unfold width
      linarith only [(hends i).1,(hends i).2]
    field_simp [hd]
    ring
  simp_rw [hterm] at hb
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, sub_apply] at hb
  have hm := ch.margin_identity ch.point
  rw [PlanarShiftedDomain.deficit_apply] at hm
  simp only [budget, hunit, div_one] at hm
  change ch.marginFormula.eval ch.point = ch.gapFormula.eval ch.point-
    (volume K).toReal*(B-∑ i, width ch.point i)^2 at hm
  dsimp only [W] at ht
  nlinarith only [hb,ht,hpoly,hm]

/-- Discarding the nonnegative cap excess gives the basic stationary bound,
still without a section-density hypothesis. -/
theorem margin_lower_bound {m : ℕ} {K : Set Point} {f : Fin m → Point →ᵃ[ℝ] ℝ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) (B : ℝ)
    (ch : PositiveMarginChart K f (PlanarShiftedDomain.domain K f B)
      (volume K).toReal (PlanarShiftedDomain.deficit K f B))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (P : QuadraticFormula (Endpoints m))
    (hgap : ∀ e ∈ ch.region, e ∈ interior (PlanarShiftedDomain.domain K f B) →
      ch.gapFormula.eval e = (volume K).toReal-
        ∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+P.eval e) :
    (volume K).toReal*(1-B)*(1+B-∑ i, width ch.point i)+P.eval ch.point-
        derivative P ch.point (∑ i, width ch.point i • velocity ch.point i)/2 ≤
      ch.marginFormula.eval ch.point := by
  have h := margin_lower_bound_with_weighted_excess hK hconv hne B ch hnorm hunit P hgap
  have hends (i) : 0 < ch.point.1 i ∧ ch.point.2 i < 1 := by
    have hi := endpoint_bounds_of_interior K f B ch.interior_point i
    exact ⟨hi.1.1,hi.2.2⟩
  have hsum : 0 ≤ ∑ i, 2/(2-width ch.point i)*
      ((volume K).toReal-coveredArea K (f i) (ch.point.1 i) (ch.point.2 i)-
        (1-width ch.point i)^2*(volume K).toReal) := by
    apply Finset.sum_nonneg
    intro i _
    have hr : width ch.point i ∈ Icc (0 : ℝ) 1 := by
      unfold width
      exact ⟨(sub_pos.mpr (ch.strict_windows i)).le,
        by linarith only [(hends i).1,(hends i).2]⟩
    apply mul_nonneg (div_nonneg (by norm_num) (by linarith only [hr.2]))
    have him := image_eq_unitInterval hK hconv hne (f i) (hnorm i) (hunit i)
    have hzero : ∃ x ∈ K, f i x=0 := by
      have hz : (0 : ℝ) ∈ f i '' K := by rw [him]; exact ⟨le_rfl,zero_le_one⟩
      exact hz
    have hone : ∃ x ∈ K, f i x=1 := by
      have ho : (1 : ℝ) ∈ f i '' K := by rw [him]; exact ⟨zero_le_one,le_rfl⟩
      exact ho
    have hc : lowerWeight ch.point i ∈ Icc (0 : ℝ) 1 := by
      have hp := add_pos (hends i).1 (sub_pos.mpr (hends i).2)
      exact ⟨(div_pos (hends i).1 hp).le,
        (div_le_one hp).mpr (by linarith only [(hends i).2])⟩
    have he := FiniteDimensionalCapWindowScaling.gap_excess_nonneg (d := 1)
      hK hconv (f i) (linear_ne_zero_of_rangeWidth_pos hne (f i)
        (by rw [hunit]; norm_num)) hzero hone hc hr
    simpa only [FiniteDimensionalCapWindowScaling.gap_eq_sub_window hK,
      (ConcurrentAnchorFinish.canonical_endpoints ch.point hends i).1,
      (ConcurrentAnchorFinish.canonical_endpoints ch.point hends i).2,
      coveredArea, PlanarSevenCellArea.plank] using he
  linarith only [h,hsum]

end Plank.PlanarCapChart
