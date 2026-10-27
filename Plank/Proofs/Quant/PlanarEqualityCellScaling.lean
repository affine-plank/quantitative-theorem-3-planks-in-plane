/- A single direction scales all four uncovered cell areas at equality. -/
module

public import Plank.Proofs.Quant.EqualityCellScaling
public import Plank.Proofs.Quant.PlanarEqualityFlatDirection

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarEqualityCellScaling

open Set MeasureTheory PlanarQuantitative PlanarPolygonCharts PlanarPlankCellCharts
  PlanarParameterDomain PlanarPositiveCellRank QuadraticChartCalculus PlanarPositiveChart
  PlanarEqualityFlatDirection
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

/-- If all four cells have positive area, their actual areas have the same
relative square scaling along one nonzero motion. No injectivity of the
gradient map is assumed. The formulas hold throughout the closed chart. -/
theorem exists_common_scaling {K : Set Point} {f : Fin 2 → Point →ᵃ[ℝ] ℝ}
    (ch : OpenChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hp : ch.point ∈ interior (domain K f)) (hR : budget K f ch.point < 1)
    (hpos : ∀ s, 0 < (ch.cellFormula s).eval ch.point)
    (heq : gapArea K f ch.point = (1-budget K f ch.point)^2*(volume K).toReal) :
    ∃ z : Endpoints 2, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      (deficit K f 1).linear z = (1-budget K f ch.point)*c ∧
      ∀ s t, ch.point+t • z ∈ closure ch.region →
        (volume (PlanarGapCells.signCell K f (ch.point+t • z).1 (ch.point+t • z).2 s)).toReal =
          (ch.cellFormula s).eval ch.point*(1+t*c)^2 := by
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
  have hder (z) : (∑ s, derivative (ch.cellFormula s) ch.point z) =
      2*V*(a ch.point)*(a.linear z) := by
    rw [← sum_apply,← derivative_sum ch.gapFormula ch.cellFormula ch.gap_sum]
    rw [derivative_of_square_subtraction ch.gapFormula M V a hM,hstat,zero_apply,zero_add]
  have hmargin (z) : 2*V*(a.linear z)^2 ≤ ∑ s, hessian (ch.cellFormula s) z z := by
    rw [← hessian_sum ch.gapFormula ch.cellFormula ch.gap_sum,
      hessian_of_square_subtraction ch.gapFormula M V a hM]
    linarith only [hessian_nonneg_of_localMin M 0 ch.point hmin z]
  have hsum : (∑ s, (ch.cellFormula s).eval ch.point) = V*(a ch.point)^2 :=
    (ch.gap_sum ch.point).symm.trans hQ
  obtain ⟨z,hzne,c,hc,hd,hg⟩ := EqualityCellScaling.exists_proportional_direction
    (fun s => (ch.cellFormula s).eval ch.point)
    (fun s => (derivative (ch.cellFormula s) ch.point).toLinearMap)
    a.linear V (a ch.point) hV
    (by simpa only [a,deficit_apply] using sub_pos.mpr hR) hsum hder
    (by simp only [Fintype.card_finset,Fintype.card_fin,endpoint_finrank]; norm_num)
  have hH := EqualityCellScaling.curvature_eq_each
    (fun s => (ch.cellFormula s).eval ch.point)
    (fun s => derivative (ch.cellFormula s) ch.point z)
    (fun s => hessian (ch.cellFormula s) z z) V (a ch.point) c hpos hsum hg
    (fun s => PlanarCellChartCalculus.curvature_bound hK hconv f s (ch.cellFormula s)
      ch.open_region (ch.cell_area s) ch.point ch.point_mem (hpos s) z)
    (by rw [← hd]; exact hmargin z)
  refine ⟨z,hzne,c,hc,by simpa only [a,deficit_apply] using hd,?_⟩
  intro s t ht
  rw [ch.cell_area s _ ht,eval_line,hH s]
  have hgs : derivative (ch.cellFormula s) ch.point z =
      2*(ch.cellFormula s).eval ch.point*c := hg s
  rw [hgs]
  ring

end Plank.PlanarEqualityCellScaling

/-- info: 'Plank.PlanarEqualityCellScaling.exists_common_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEqualityCellScaling.exists_common_scaling
