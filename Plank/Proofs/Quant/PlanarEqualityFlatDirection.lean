/- Actual equality motions inside an open two-plank area chart. This is
local rigidity, not yet a global classification across chart boundaries. -/
module

public import Plank.Proofs.Quant.EqualityCellRank
public import Plank.Proofs.Quant.PlanarTwoPlank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarEqualityFlatDirection

open Set MeasureTheory Filter PlanarQuantitative PlanarPolygonCharts PlanarPlankCellCharts
  PlanarParameterDomain PlanarPositiveCellRank QuadraticChartCalculus PlanarPositiveChart
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem derivative_of_square_subtraction (Q M : QuadraticFormula E) (V : ℝ)
    (a : E →ᵃ[ℝ] ℝ) (hM : ∀ e, M.eval e = Q.eval e-V*(a e)^2) (p z : E) :
    derivative Q p z = derivative M p z+2*V*(a p)*(a.linear z) := by
  have hp := hM (p+(1 : ℝ) • z)
  have hm := hM (p+(-1 : ℝ) • z)
  rw [eval_line,eval_line,affine_eval_line] at hp hm
  nlinarith only [hp,hm]

theorem hessian_of_square_subtraction (Q M : QuadraticFormula E) (V : ℝ)
    (a : E →ᵃ[ℝ] ℝ) (hM : ∀ e, M.eval e = Q.eval e-V*(a e)^2) (z : E) :
    hessian Q z z = hessian M z z+2*V*(a.linear z)^2 := by
  have hp := hM ((0 : E)+(1 : ℝ) • z)
  have hm := hM ((0 : E)+(-1 : ℝ) • z)
  have h0 := hM 0
  rw [eval_line,eval_line,affine_eval_line] at hp hm
  nlinarith only [hp,hm,h0]

/-- Actual quadratic formulas on an open endpoint region. Existence of
such a chart at the given point is an explicit geometric premise; no
curvature, stationarity or rank hypothesis is assumed. -/
structure OpenChart (K : Set Point) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) where
  region : Set (Endpoints 2)
  open_region : IsOpen region
  point : Endpoints 2
  point_mem : point ∈ region
  cellFormula : Finset (Fin 2) → QuadraticFormula (Endpoints 2)
  gapFormula : QuadraticFormula (Endpoints 2)
  cell_area : ∀ s e, e ∈ closure region →
    (volume (PlanarGapCells.signCell K f e.1 e.2 s)).toReal = (cellFormula s).eval e
  gap_sum : ∀ e, gapFormula.eval e = ∑ s, (cellFormula s).eval e

namespace OpenChart

variable {K : Set Point} {f : Fin 2 → Point →ᵃ[ℝ] ℝ} (ch : OpenChart K f)

abbrev Cells := ↥(activeCells ch.cellFormula)

theorem gap_sum_active (e : Endpoints 2) :
    ch.gapFormula.eval e = ∑ s : ch.Cells, (ch.cellFormula s).eval e := by
  rw [sum_activeCells,ch.gap_sum]

theorem gap_area (hK : IsCompact K) (hne : K.Nonempty)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (e : Endpoints 2) (he : e ∈ closure ch.region)
    (ho : ∀ i, e.1 i ≤ e.2 i) : gapArea K f e = ch.gapFormula.eval e := by
  rw [gapArea,PlanarGapCells.area_gap_eq_sum_signCells hK hne f hW e.1 e.2 ho,ch.gap_sum]
  exact Finset.sum_congr rfl fun s _ => ch.cell_area s e he

theorem cell_positive (hK : IsCompact K) (hconv : Convex ℝ K) (s : ch.Cells) :
    0 < (ch.cellFormula s).eval ch.point :=
  PlanarCellChartCalculus.eval_pos_of_nonzero hK hconv f s (ch.cellFormula s)
    ch.open_region (ch.cell_area s) ((mem_activeCells _ _).mp s.property) ch.point ch.point_mem

/-- A nonzero line preserves actual equality wherever it stays in the
closed actual-area chart and the windows stay ordered. Its direction has
nonnegative deficit derivative. Curvature and stationarity are derived. -/
theorem exists_flat_equality_line (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hp : ch.point ∈ interior (domain K f)) (hR : budget K f ch.point < 1)
    (heq : gapArea K f ch.point = (1-budget K f ch.point)^2*(volume K).toReal) :
    ∃ z : Endpoints 2, z ≠ 0 ∧ 0 ≤ (deficit K f 1).linear z ∧
      ∀ t : ℝ, ch.point+t • z ∈ closure ch.region →
        (∀ i, (ch.point+t • z).1 i ≤ (ch.point+t • z).2 i) →
        gapArea K f (ch.point+t • z) =
          (1-budget K f (ch.point+t • z))^2*(volume K).toReal := by
  classical
  let V := (volume K).toReal
  let a := deficit K f 1
  let M := subtractSquare ch.gapFormula V a
  have hM (e) : M.eval e = ch.gapFormula.eval e-V*(a e)^2 := eval_subtractSquare _ _ _ _
  have hQ : ch.gapFormula.eval ch.point = V*(a ch.point)^2 := by
    rw [← ch.gap_area hK hne hW ch.point (subset_closure ch.point_mem)
      (fun i => ((interior_subset hp).1 i).2.1),heq]
    simp only [a,deficit_apply,V,mul_comm]
  have hM0 : M.eval ch.point = 0 := by rw [hM,hQ,sub_self]
  have hmin : IsLocalMin (tilt M 0) ch.point := by
    apply Filter.Eventually.mono ((ch.open_region.inter isOpen_interior).mem_nhds
      (show ch.point ∈ ch.region ∩ interior (domain K f) from ⟨ch.point_mem,hp⟩))
    intro e he
    simp only [tilt,zero_apply,sub_zero,hM0]
    rw [hM,← ch.gap_area hK hne hW e (subset_closure he.1)
      (fun i => ((interior_subset he.2).1 i).2.1)]
    apply sub_nonneg.mpr
    have hh := PlanarTwoPlank.sharpPlanarBound_two K hK hconv hne f e.1 e.2
      (fun i => ((interior_subset he.2).1 i).2.1) hW
    change (max 0 (1-budget K f e))^2*V ≤ gapArea K f e at hh
    rw [max_eq_right (sub_nonneg.mpr (interior_subset he.2).2)] at hh
    simpa only [a,deficit_apply,mul_comm] using hh
  have hstat : derivative M ch.point = 0 := stationary_of_localMin M 0 ch.point hmin
  have hnonneg (z) : 0 ≤ hessian M z z := hessian_nonneg_of_localMin M 0 ch.point hmin z
  have hder (z) : (∑ s : ch.Cells, derivative (ch.cellFormula s) ch.point z) =
      2*V*(a ch.point)*(a.linear z) := by
    rw [← sum_apply,← derivative_sum ch.gapFormula (fun s : ch.Cells => ch.cellFormula s)
      ch.gap_sum_active]
    rw [derivative_of_square_subtraction ch.gapFormula M V a hM,hstat,zero_apply,zero_add]
  have hhess (z) : (∑ s : ch.Cells, hessian (ch.cellFormula s) z z) =
      hessian M z z+2*V*(a.linear z)^2 := by
    rw [← hessian_sum ch.gapFormula (fun s : ch.Cells => ch.cellFormula s) ch.gap_sum_active]
    exact hessian_of_square_subtraction ch.gapFormula M V a hM z
  have hmargin (z) : 2*V*(a.linear z)^2 ≤ ∑ s : ch.Cells, hessian (ch.cellFormula s) z z := by
    rw [hhess]
    linarith only [hnonneg z]
  have hcard : Fintype.card ch.Cells ≤ Module.finrank ℝ (Endpoints 2) := by
    have hh := Fintype.card_subtype_le (fun s => s ∈ activeCells ch.cellFormula)
    norm_num only [Cells,Fintype.card_finset,Fintype.card_fin,endpoint_finrank] at hh ⊢
    exact hh
  obtain ⟨z,hzne,hdpos,hflat⟩ := EqualityCellRank.exists_flat_direction
    (fun s : ch.Cells => (ch.cellFormula s).eval ch.point)
    (fun s : ch.Cells => (derivative (ch.cellFormula s) ch.point).toLinearMap)
    (fun s z => hessian (ch.cellFormula s) z z) a.linear V (a ch.point) hV
    (by simpa only [a,deficit_apply] using sub_pos.mpr hR) (ch.cell_positive hK hconv)
    ((ch.gap_sum_active ch.point).symm.trans hQ) hder
    (fun s z => PlanarCellChartCalculus.curvature_bound hK hconv f s (ch.cellFormula s)
      ch.open_region (ch.cell_area s) ch.point ch.point_mem (ch.cell_positive hK hconv s) z)
    hmargin hcard
  have hMzz : hessian M z z = 0 := by rw [hhess] at hflat; linarith only [hflat]
  have hline (t : ℝ) : M.eval (ch.point+t • z) = 0 := by
    rw [eval_line,hM0,hstat,zero_apply,hMzz]
    ring
  refine ⟨z,hzne,hdpos,?_⟩
  intro t ht ho
  rw [ch.gap_area hK hne hW _ ht ho]
  have hh := hM (ch.point+t • z)
  rw [hline] at hh
  simpa only [a,deficit_apply,V,mul_comm] using (sub_eq_zero.mp hh.symm)

/-- A genuine interior two-plank equality on an open actual-area chart
has nearby distinct genuine equality configurations. In the chosen
positive direction the total relative width cannot increase. -/
theorem exists_actual_equality_motion (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hp : ch.point ∈ interior (domain K f)) (hR : budget K f ch.point < 1)
    (heq : gapArea K f ch.point = (1-budget K f ch.point)^2*(volume K).toReal) :
    ∃ z : Endpoints 2, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      ch.point+t • z ∈ ch.region ∧ ch.point+t • z ∈ interior (domain K f) ∧
      gapArea K f (ch.point+t • z) =
        (1-budget K f (ch.point+t • z))^2*(volume K).toReal ∧
      (0 ≤ t → budget K f (ch.point+t • z) ≤ budget K f ch.point) := by
  obtain ⟨z,hzne,hdpos,hline⟩ := ch.exists_flat_equality_line hK hconv hne hV hW hp hR heq
  have hopen : IsOpen {t : ℝ | ch.point+t • z ∈ ch.region ∩ interior (domain K f)} :=
    (ch.open_region.inter isOpen_interior).preimage (by fun_prop)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (0 : ℝ) ∈ {t | ch.point+t • z ∈ ch.region ∩ interior (domain K f)} by
      simpa only [mem_ofPred_eq,zero_smul,add_zero,mem_inter_iff] using And.intro ch.point_mem hp))
  refine ⟨z,hzne,ε,hε,?_⟩
  intro t ht
  have hemem := hball (show t ∈ Metric.ball 0 ε by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using ht)
  refine ⟨hemem.1,hemem.2,?_,?_⟩
  · exact hline t (subset_closure hemem.1) (fun i => ((interior_subset hemem.2).1 i).2.1)
  · intro ht0
    have hh := affine_eval_line (deficit K f 1) ch.point z t
    simp only [deficit_apply] at hh
    have hprod := mul_nonneg ht0 hdpos
    linarith only [hh,hprod]

end OpenChart
end Plank.PlanarEqualityFlatDirection

/-- info: 'Plank.PlanarEqualityFlatDirection.OpenChart.exists_actual_equality_motion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEqualityFlatDirection.OpenChart.exists_actual_equality_motion
