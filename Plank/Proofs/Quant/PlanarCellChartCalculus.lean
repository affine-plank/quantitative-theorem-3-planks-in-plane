/- Curvature and zero-cell rigidity on actual open area charts. -/
module

public import Plank.Proofs.Quant.PlanarCounterexampleChart

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellChartCalculus

open Set MeasureTheory PlanarQuantitative PlanarCellArea PlanarGapCells
open PlanarPolygonCharts PlanarPlankCellCharts QuadraticChartCalculus
open scoped Topology

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
/-- Brunn--Minkowski compares the two actual cells at opposite endpoint
motions with the cell at their midpoint. No endpoint ordering is needed. -/
theorem sqrt_area_midpoint {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) (e z : EndpointSpace κ) (t : ℝ)
    (hplus : (signCell K f (e+t • z).1 (e+t • z).2 s).Nonempty)
    (hminus : (signCell K f (e+(-t) • z).1 (e+(-t) • z).2 s).Nonempty) :
    (Real.sqrt (volume (signCell K f (e+t • z).1 (e+t • z).2 s)).toReal +
      Real.sqrt (volume (signCell K f (e+(-t) • z).1 (e+(-t) • z).2 s)).toReal)/2 ≤
      Real.sqrt (volume (signCell K f e.1 e.2 s)).toReal := by
  let u := cutOffsets f e.1 e.2 s
  let v := cutDirection z.1 z.2 s
  have heq (r : ℝ) : signCell K f (e+r • z).1 (e+r • z).2 s =
      cell K (cutForms f s) (u+r • v) := by
    rw [signCell_eq_cell]
    exact congrArg (cell K (cutForms f s)) (cutOffsets_motion f e.1 e.2 z.1 z.2 s r)
  rw [heq] at hplus hminus
  have hm : (1/2 : ℝ) • (u+t • v)+(1/2 : ℝ) • (u+(-t) • v) = u := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hh := (concaveOn_sqrt_area_cell hK hconv (cutForms f s)).2 hplus hminus
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num)
  rw [hm] at hh
  rw [heq, heq, signCell_eq_cell]
  change (Real.sqrt (volume (cell K (cutForms f s) (u+t • v))).toReal +
    Real.sqrt (volume (cell K (cutForms f s) (u+(-t) • v))).toReal)/2 ≤
      Real.sqrt (volume (cell K (cutForms f s) u)).toReal
  dsimp only [smul_eq_mul] at hh
  linarith only [hh]

omit [Fintype κ] in
theorem nonempty_of_area_pos (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ)
    (s : Finset κ) (e : EndpointSpace κ)
    (h : 0 < (volume (signCell K f e.1 e.2 s)).toReal) :
    (signCell K f e.1 e.2 s).Nonempty := by
  by_contra hn
  rw [not_nonempty_iff_eq_empty] at hn
  simp [hn] at h

/-- Curvature is nonpositive on a cell-gradient kernel, including at a
zero-area cell. Positive opposite areas would contradict Brunn--Minkowski. -/
theorem curvature_nonpos_on_kernel {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) (q : QuadraticFormula (EndpointSpace κ))
    {U : Set (EndpointSpace κ)} (hU : IsOpen U)
    (hchart : ∀ e ∈ closure U, (volume (signCell K f e.1 e.2 s)).toReal = q.eval e)
    (e : EndpointSpace κ) (he : e ∈ U) (z : EndpointSpace κ)
    (hgrad : derivative q e z = 0) : hessian q z z ≤ 0 := by
  by_contra hn
  have hH : 0 < hessian q z z := lt_of_not_ge hn
  have hnonneg : 0 ≤ q.eval e := by
    rw [← hchart e (subset_closure he)]
    exact ENNReal.toReal_nonneg
  have hopen : IsOpen {t : ℝ | e+t • z ∈ U} := hU.preimage (by fun_prop)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds (show (0 : ℝ) ∈ {t | e+t • z ∈ U} by simpa using he))
  let t := ε/2
  have ht : 0 < t := by dsimp [t]; linarith
  have hp : e+t • z ∈ U := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]; linarith)
  have hm : e+(-t) • z ∈ U := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_pos ht]
    dsimp [t]; linarith)
  have hstrict : q.eval e < q.eval (e+t • z) := by
    rw [QuadraticChartCalculus.eval_line, hgrad, mul_zero, add_zero]
    exact lt_add_of_pos_right _ (div_pos (mul_pos (sq_pos_of_pos ht) hH) (by norm_num))
  have hequal : q.eval (e+(-t) • z) = q.eval (e+t • z) := by
    rw [QuadraticChartCalculus.eval_line, QuadraticChartCalculus.eval_line, hgrad]
    ring
  have hpos : 0 < q.eval (e+t • z) := hnonneg.trans_lt hstrict
  have hpne := nonempty_of_area_pos K f s (e+t • z)
    (by rwa [hchart _ (subset_closure hp)])
  have hmne := nonempty_of_area_pos K f s (e+(-t) • z)
    (by rwa [hchart _ (subset_closure hm), hequal])
  have hbm := sqrt_area_midpoint hK hconv f s e z t hpne hmne
  rw [hchart _ (subset_closure hp), hchart _ (subset_closure hm),
    hchart _ (subset_closure he), hequal] at hbm
  have hsqrt : Real.sqrt (q.eval (e+t • z)) ≤ Real.sqrt (q.eval e) := by
    linarith only [hbm]
  exact hstrict.not_ge ((Real.sqrt_le_sqrt_iff hnonneg).mp hsqrt)

/-- A cell that has zero area at an interior chart point has the zero
polynomial on the entire parameter space. No combinatorial constancy is assumed. -/
theorem eval_zero_of_zero_at {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) (q : QuadraticFormula (EndpointSpace κ))
    {U : Set (EndpointSpace κ)} (hU : IsOpen U)
    (hchart : ∀ e ∈ closure U, (volume (signCell K f e.1 e.2 s)).toReal = q.eval e)
    (e : EndpointSpace κ) (he : e ∈ U) (hzero : q.eval e = 0) : ∀ x, q.eval x = 0 := by
  have hmin : IsLocalMin (tilt q 0) e := by
    apply Filter.Eventually.mono (hU.mem_nhds he)
    intro x hx
    change tilt q 0 e ≤ tilt q 0 x
    simp only [tilt, zero_apply, sub_zero, hzero]
    rw [← hchart x (subset_closure hx)]
    exact ENNReal.toReal_nonneg
  have hd := stationary_of_localMin q 0 e hmin
  have hH (z : EndpointSpace κ) : hessian q z z = 0 := le_antisymm
    (curvature_nonpos_on_kernel hK hconv f s q hU hchart e he z (by rw [hd]; rfl))
    (hessian_nonneg_of_localMin q 0 e hmin z)
  intro x
  have hh := QuadraticChartCalculus.eval_add q e (x-e)
  simpa only [add_sub_cancel, hzero, hd, zero_apply, hH, zero_div, add_zero] using hh

/-- Every nonzero actual cell polynomial is positive everywhere on its
open chart, even though its boundary values may vanish. -/
theorem eval_pos_of_nonzero {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) (q : QuadraticFormula (EndpointSpace κ))
    {U : Set (EndpointSpace κ)} (hU : IsOpen U)
    (hchart : ∀ e ∈ closure U, (volume (signCell K f e.1 e.2 s)).toReal = q.eval e)
    (hne : ∃ x, q.eval x ≠ 0) (e : EndpointSpace κ) (he : e ∈ U) : 0 < q.eval e := by
  have hnonneg : 0 ≤ q.eval e := by
    rw [← hchart e (subset_closure he)]
    exact ENNReal.toReal_nonneg
  apply lt_of_le_of_ne hnonneg
  intro hz
  obtain ⟨x, hx⟩ := hne
  exact hx (eval_zero_of_zero_at hK hconv f s q hU hchart e he hz.symm x)

/-- The actual positive-cell curvature bound with the already constructed
full derivative and fixed Hessian, rather than existential coefficients. -/
theorem curvature_bound {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) (q : QuadraticFormula (EndpointSpace κ))
    {U : Set (EndpointSpace κ)} (hU : IsOpen U)
    (hchart : ∀ e ∈ closure U, (volume (signCell K f e.1 e.2 s)).toReal = q.eval e)
    (e : EndpointSpace κ) (he : e ∈ U) (hpos : 0 < q.eval e) (z : EndpointSpace κ) :
    hessian q z z ≤ (derivative q e z)^2/(2*q.eval e) := by
  have harea := hchart e (subset_closure he)
  obtain ⟨g, H, hline, hbound⟩ := curvature_on_cell_chart hK hconv f s q hU hchart e he
    (by rwa [harea]) z
  have hp := hline 1
  have hm := hline (-1)
  rw [QuadraticChartCalculus.eval_line, harea] at hp hm
  have hg : g = derivative q e z := by nlinarith only [hp, hm]
  have hH : H = hessian q z z := by nlinarith only [hp, hm]
  rwa [hg, hH, harea] at hbound

end Plank.PlanarCellChartCalculus
