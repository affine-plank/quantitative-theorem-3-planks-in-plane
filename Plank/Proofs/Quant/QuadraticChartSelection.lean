/- Select positive-definite quadratic charts by small linear perturbations. -/
module

public import Plank.Proofs.Quant.QuadraticChartPerturbations
public import Plank.Proofs.Quant.PlanarChartRegularity
public import Mathlib.Topology.MetricSpace.Sequences

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.QuadraticChartSelection

open Set Filter PlanarPolygonCharts QuadraticChartCalculus QuadraticChartPerturbations
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- C1 regularity identifies a chart derivative on its closure, including
points where more than one quadratic formula meets. -/
theorem derivative_eq_on_closure (G : E → ℝ) (U C : Set E)
    (hU : IsOpen U) (hC : IsOpen C) (hG : ContDiffOn ℝ 1 G U)
    (q : QuadraticFormula E) (hvalue : ∀ x ∈ closure C ∩ U, G x = q.eval x) :
    ∀ x ∈ closure C ∩ U, fderiv ℝ G x = derivative q x := by
  have heq : EqOn (fderiv ℝ G) (derivative q) (C ∩ U) := by
    intro x hx
    have hlocal : G =ᶠ[nhds x] q.eval := by
      filter_upwards [(hC.inter hU).mem_nhds hx] with y hy
      exact hvalue y ⟨subset_closure hy.1, hy.2⟩
    exact ((hasFDerivAt_eval q x).congr_of_eventuallyEq hlocal).fderiv
  apply heq.of_subset_closure
  · exact (hG.continuousOn_fderiv_of_isOpen hU le_rfl).mono inter_subset_right
  · exact (continuous_derivative q).continuousOn
  · exact fun _ hx => ⟨subset_closure hx.1, hx.2⟩
  · intro x hx
    exact PlanarChartRegularity.mem_closure_inter_of_open hU hx.1 hx.2

/-- Good perturbations force an interior minimum into an open chart with
strictly positive Hessian. The gradient match on an adjacent closure
first rules out every incidence wall. -/
theorem localMin_in_positive_chart {σ τ : Type*} [Finite σ] [Finite τ]
    (G : E → ℝ) (U : Set E) (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (C : σ → Set E) (hC : ∀ i, IsOpen (C i))
    (q : σ → QuadraticFormula E) (F : τ → E →ᵃ[ℝ] ℝ)
    (hcover : (⋃ i, closure (C i)) = univ)
    (hoff : ∀ x, (∀ w, F w ≠ 0 → F w x ≠ 0) → ∃ i, x ∈ C i)
    (hvalue : ∀ i, ∀ x ∈ closure (C i) ∩ U, G x = (q i).eval x)
    (v : E →L[ℝ] ℝ) (hv : Good q F v) (x : E) (hx : x ∈ U)
    (hmin : IsLocalMin (fun y => G y-v y) x) :
    ∃ i, x ∈ C i ∧ derivative (q i) x = v ∧
      ∀ z : E, z ≠ 0 → 0 < hessian (q i) z z := by
  have hd := (((hG x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hstationary : fderiv ℝ G x = v :=
    sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero (hd.sub v.hasFDerivAt))
  have hmem : x ∈ ⋃ i, closure (C i) := by rw [hcover]; trivial
  obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
  have hgrad := derivative_eq_on_closure G U (C j) hU (hC j) hG (q j) (hvalue j) x ⟨hj, hx⟩
  have hgood := hv j x (hgrad.symm.trans hstationary)
  obtain ⟨i, hi⟩ := hoff x hgood.2
  have hqmin : IsLocalMin (tilt (q i) v) x := by
    apply hmin.congr
    filter_upwards [((hC i).inter hU).mem_nhds ⟨hi, hx⟩] with y hy
    exact congrArg (fun t : ℝ => t-v y) (hvalue i y ⟨subset_closure hy.1, hy.2⟩)
  have hs := stationary_of_localMin (q i) v x hqmin
  exact ⟨i, hi, hs, hessian_pos_of_localMin (q i) v x hqmin (hv i x hs).1⟩

omit [FiniteDimensional ℝ E] in
/-- A strict gap between one interior value and the compact boundary
keeps all minimizers of sufficiently small linear perturbations interior. -/
theorem small_perturbations_keep_minima_interior (G : E → ℝ) (D : Set E)
    (hD : IsCompact D) (hG : ContinuousOn G D) (x₀ : E) (hx₀ : x₀ ∈ D)
    (hboundary : ∀ x ∈ D, x ∉ interior D → G x₀ < G x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v : E →L[ℝ] ℝ, ‖v‖ < ε →
      ∀ x ∈ D, IsMinOn (fun y => G y-v y) D x → x ∈ interior D := by
  classical
  by_cases hne : (D \ interior D).Nonempty
  · obtain ⟨b, hb, hminb⟩ := (hD.diff isOpen_interior).exists_isMinOn hne
      (hG.mono sdiff_subset)
    obtain ⟨M, hM, hbound⟩ := hD.isBounded.exists_pos_norm_le
    have hgap : 0 < G b-G x₀ := sub_pos.mpr (hboundary b hb.1 hb.2)
    have hden : 0 < 2*M+1 := by linarith
    refine ⟨(G b-G x₀)/(2*M+1), div_pos hgap hden, ?_⟩
    intro v hv x hx hmin
    by_contra hnot
    have hbnd : G b ≤ G x := hminb ⟨hx, hnot⟩
    have hcmp : G x-v x ≤ G x₀-v x₀ := hmin hx₀
    have hxv : |v x| ≤ ‖v‖*M := by
      exact (v.le_opNorm x).trans (mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg v))
    have h0v : |v x₀| ≤ ‖v‖*M := by
      exact (v.le_opNorm x₀).trans (mul_le_mul_of_nonneg_left (hbound x₀ hx₀) (norm_nonneg v))
    have hsmall := (lt_div_iff₀ hden).mp hv
    have hxup := (abs_le.mp hxv).2
    have h0lo := (abs_le.mp h0v).1
    nlinarith only [hbnd, hcmp, hsmall, hxup, h0lo, norm_nonneg v]
  · refine ⟨1, zero_lt_one, fun _ _ x hx _ => ?_⟩
    by_contra hnot
    exact hne ⟨x, hx, hnot⟩

/-- A compact boundary barrier and a C1 finite quadratic atlas force a
global minimum into the closure of a chart with positive-definite Hessian.
The minimum may lie on incidence walls. Small generic perturbations, a
fixed-chart subsequence and their limiting stationary point are constructed. -/
theorem exists_positive_chart_minimizer {σ τ : Type*} [Finite σ] [Finite τ]
    (G : E → ℝ) (D : Set E) (hD : IsCompact D) (hG : ContinuousOn G D)
    (hreg : ContDiffOn ℝ 1 G (interior D)) (x₀ : E) (hx₀ : x₀ ∈ D)
    (hboundary : ∀ x ∈ D, x ∉ interior D → G x₀ < G x)
    (C : σ → Set E) (hC : ∀ i, IsOpen (C i))
    (q : σ → QuadraticFormula E) (F : τ → E →ᵃ[ℝ] ℝ)
    (hcover : (⋃ i, closure (C i)) = univ)
    (hoff : ∀ x, (∀ w, F w ≠ 0 → F w x ≠ 0) → ∃ i, x ∈ C i)
    (hvalue : ∀ i, ∀ x ∈ closure (C i) ∩ interior D, G x = (q i).eval x) :
    ∃ i x, x ∈ interior D ∧ x ∈ closure (C i) ∧ IsMinOn G D x ∧
      G x = (q i).eval x ∧ derivative (q i) x = 0 ∧
      ∀ z : E, z ≠ 0 → 0 < hessian (q i) z z := by
  classical
  obtain ⟨ε, hε, hprotect⟩ := small_perturbations_keep_minima_interior G D hD hG x₀ hx₀ hboundary
  have hnear : (0 : E →L[ℝ] ℝ) ∈ closure ({v | Good q F v} ∩ Metric.ball 0 ε) :=
    PlanarChartRegularity.mem_closure_inter_of_open Metric.isOpen_ball
      (dense_good q F 0) (Metric.mem_ball_self hε)
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hnear
  have hpoint (n : ℕ) : ∃ (x : E) (i : σ), x ∈ D ∧ x ∈ C i ∧
      derivative (q i) x = v n ∧ (∀ z : E, z ≠ 0 → 0 < hessian (q i) z z) ∧
      IsMinOn (fun y => G y-v n y) D x := by
    obtain ⟨x, hx, hmin⟩ := hD.exists_isMinOn ⟨x₀, hx₀⟩
      (hG.sub (v n).continuous.continuousOn)
    have hvsmall : ‖v n‖ < ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using (hv n).2
    have hinside := hprotect (v n) hvsmall x hx hmin
    obtain ⟨i, hi, hs, hp⟩ := localMin_in_positive_chart G (interior D) isOpen_interior
      hreg C hC q F hcover hoff hvalue (v n) (hv n).1 x hinside
      (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hinside))
    exact ⟨x, i, hx, hi, hs, hp, hmin⟩
  choose x i hxD hxC hs hp hm using hpoint
  have hfreq : ∃ᶠ n : ℕ in atTop, ∃ j : σ, i n = j :=
    Frequently.of_forall (fun n => ⟨i n, rfl⟩)
  obtain ⟨j, hjfreq⟩ := frequently_exists.mp hfreq
  obtain ⟨φ, hφ, hconstant⟩ := extraction_of_frequently_atTop hjfreq
  obtain ⟨xstar, hxstar, ψ, hψ, hlimit⟩ := hD.tendsto_subseq
    (x := fun n => x (φ n)) (fun n => hxD (φ n))
  let χ := φ ∘ ψ
  have hχ : Tendsto χ atTop atTop := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have hxlim : Tendsto (fun n => x (χ n)) atTop (nhds xstar) := by
    simpa only [χ, Function.comp_def] using hlimit
  have hconst (n : ℕ) : i (χ n) = j := hconstant (ψ n)
  have hvlim' : Tendsto (fun n => v (χ n)) atTop (nhds 0) := hvlim.comp hχ
  have hxwithin : Tendsto (fun n => x (χ n)) atTop (nhdsWithin xstar D) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxlim, Eventually.of_forall (fun n => hxD (χ n))⟩
  have hGlim : Tendsto (fun n => G (x (χ n))) atTop (nhds (G xstar)) :=
    (hG xstar hxstar).tendsto.comp hxwithin
  have happ : Continuous (fun p : (E →L[ℝ] ℝ) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hleft : Tendsto (fun n => G (x (χ n))-v (χ n) (x (χ n))) atTop (nhds (G xstar)) := by
    simpa only [zero_apply, sub_zero, Function.comp_def] using
      hGlim.sub ((happ.tendsto (0, xstar)).comp (hvlim'.prodMk_nhds hxlim))
  have hminimum : IsMinOn G D xstar := by
    intro y hy
    have hright : Tendsto (fun n => G y-v (χ n) y) atTop (nhds (G y)) := by
      simpa only [zero_apply, sub_zero, Function.comp_def] using
        tendsto_const_nhds.sub
          ((happ.tendsto (0, y)).comp (hvlim'.prodMk_nhds tendsto_const_nhds))
    exact le_of_tendsto_of_tendsto' hleft hright (fun n => hm (χ n) hy)
  have hinside : xstar ∈ interior D := by
    by_contra hnot
    exact (not_lt_of_ge (hminimum hx₀)) (hboundary xstar hxstar hnot)
  have hinclosure : xstar ∈ closure (C j) := by
    apply isClosed_closure.mem_of_tendsto hxlim
    apply Eventually.of_forall
    intro n
    apply subset_closure
    simpa only [hconst n] using hxC (χ n)
  have hderivseq (n : ℕ) : derivative (q j) (x (χ n)) = v (χ n) := by
    simpa only [hconst n] using hs (χ n)
  have hderivlim : Tendsto (fun n => derivative (q j) (x (χ n))) atTop (nhds 0) := by
    simpa only [hderivseq] using hvlim'
  have hzero : derivative (q j) xstar = 0 :=
    tendsto_nhds_unique (((continuous_derivative (q j)).tendsto xstar).comp hxlim) hderivlim
  refine ⟨j, xstar, hinside, hinclosure, hminimum, hvalue j xstar ⟨hinclosure, hinside⟩,
    hzero, ?_⟩
  simpa only [hconstant 0] using hp (φ 0)

end Plank.QuadraticChartSelection
