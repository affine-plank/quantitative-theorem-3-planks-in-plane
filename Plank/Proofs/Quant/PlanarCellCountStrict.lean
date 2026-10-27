/- One scaling coordinate gives the strict cell count directly. -/
module

public import Plank.Proofs.Quant.PlanarPositiveCellRank
public import Plank.Proofs.Quant.HomogeneousCellRank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellCountStrict

open Set MeasureTheory Filter PlanarQuantitative PlanarCounterexampleChart
open PlanarParameterDomain (Endpoints)
open PlanarShiftedDomain (deficit)
open PlanarPositiveCellRank QuadraticChartCalculus
open scoped Topology

variable {m : ℕ} {K : Set Point} {f : Fin m → Point →ᵃ[ℝ] ℝ}

/-- When the actual positive-cell count equals the endpoint dimension, the
gradient map is onto. Solving it against the cell areas gives the required
total derivative identity and curvature estimate, at every open-chart point. -/
theorem exists_area_direction (ch : CounterexampleChart K f) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hcard : Fintype.card (Cells ch) = 2*m)
    (e : Endpoints m) (he : e ∈ ch.chart.region) :
    ∃ z : Endpoints m,
      derivative ch.chart.gapFormula e z = ch.chart.gapFormula.eval e ∧
      hessian ch.chart.gapFormula z z ≤ ch.chart.gapFormula.eval e/2 := by
  have hdim : Module.finrank ℝ (Endpoints m) = Module.finrank ℝ (Cells ch → ℝ) := by
    rw [endpoint_finrank, Module.finrank_pi, hcard]
  have hsurj : Function.Surjective (gradientMap ch e) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
      (gradientMap_injective ch hK hconv e he)
  obtain ⟨z, hz⟩ := hsurj (fun s : Cells ch => (ch.chart.cellFormula s).eval e)
  have hder (s : Cells ch) : derivative (ch.chart.cellFormula s) e z =
      (ch.chart.cellFormula s).eval e := congrFun hz s
  refine ⟨z, ?_, ?_⟩
  · rw [derivative_sum ch.chart.gapFormula (fun s : Cells ch => ch.chart.cellFormula s)
      (gap_sum_active ch), gap_sum_active ch]
    simp only [sum_apply, hder]
  · rw [hessian_sum ch.chart.gapFormula (fun s : Cells ch => ch.chart.cellFormula s)
      (gap_sum_active ch), gap_sum_active ch, Finset.sum_div]
    apply Finset.sum_le_sum
    intro s _
    have hpos := cell_positive ch hK hconv s e he
    have hb := PlanarCellChartCalculus.curvature_bound hK hconv f s (ch.chart.cellFormula s)
      ch.chart.open_region (ch.chart.cell_area s) e he hpos z
    rw [hder] at hb
    have hcancel : (ch.chart.cellFormula s).eval e^2/(2*(ch.chart.cellFormula s).eval e) =
        (ch.chart.cellFormula s).eval e/2 := by
      field_simp
    exact hb.trans_eq hcancel

/-- One open-chart point suffices. The area direction extrapolates the gap
polynomial to a nonpositive value, contradicting its global positivity.
Cells may vanish at the selected stationary point; no limit is required. -/
theorem cell_count_ne_endpoint_dimension (ch : CounterexampleChart K f)
    (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal) (hm : 0 < m) :
    Fintype.card (Cells ch) ≠ 2*m := by
  have _ := hm
  intro hcard
  have hne : ch.chart.region.Nonempty := Set.Nonempty.of_closure ⟨_, ch.chart.closure_point⟩
  obtain ⟨e, he⟩ := hne
  obtain ⟨z, hd, hH⟩ := exists_area_direction ch hK hconv hcard e he
  exact (ch.gap_formula_pos hV (e+(-2 : ℝ) • z)).not_ge
    (eval_nonpos_of_area_direction ch.chart.gapFormula e z hd hH)

/-- The selected chart of an actual counterexample needs strictly more
than two positive cells per plank. The closure case is fully included. -/
theorem endpoint_count_lt (ch : CounterexampleChart K f) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal) (hm : 0 < m) :
    2*m < Fintype.card (Cells ch) := by
  have _ := hm
  obtain ⟨e, he⟩ := Set.Nonempty.of_closure ⟨_, ch.chart.closure_point⟩
  have hh := HomogeneousCellRank.dimension_lt_components
    (E := Endpoints m) (ι := Cells ch) 2 (by norm_num)
    (fun s => (ch.chart.cellFormula s).eval e)
    (fun s => (derivative (ch.chart.cellFormula s) e).toLinearMap)
    (fun s z => hessian (ch.chart.cellFormula s) z z)
    (fun s => cell_positive ch hK hconv s e he) (by
      intro s z
      have hpos := cell_positive ch hK hconv s e he
      have hc := PlanarCellChartCalculus.curvature_bound hK hconv f s
        (ch.chart.cellFormula s) ch.chart.open_region (ch.chart.cell_area s) e he hpos z
      have hb := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hpos)).mp hc
      simpa only [ContinuousLinearMap.coe_coe,
        show (2 : ℝ)-1=1 by norm_num, one_mul, mul_comm] using hb) (by
      intro w hw
      have hp := positive_homogenization ch.chart.gapFormula e
        (ch.gap_formula_pos hV) ch.positive_gap_hessian w hw
      rw [hessian_sum ch.chart.gapFormula (fun s : Cells ch => ch.chart.cellFormula s)
          (gap_sum_active ch),
        derivative_sum ch.chart.gapFormula (fun s : Cells ch => ch.chart.cellFormula s)
          (gap_sum_active ch), gap_sum_active ch] at hp
      simpa only [HomogeneousCellRank.liftCurvature, ContinuousLinearMap.coe_coe,
        sum_apply, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        show (2 : ℝ)-1=1 by norm_num, mul_one] using hp)
  simpa only [endpoint_finrank] using hh

/-- The strict bound counts actual positive-area exterior sign cells at
any point of the selected open chart. -/
theorem actual_positive_cell_count_lt (ch : CounterexampleChart K f) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal) (hm : 0 < m)
    (e : Endpoints m) (he : e ∈ ch.chart.region) :
    2*m < (Finset.univ.filter (fun s : Finset (Fin m) =>
      0 < (volume (PlanarGapCells.signCell K f e.1 e.2 s)).toReal)).card := by
  rw [← activeCells_eq_positive ch hK hconv e he]
  simpa only [Cells, Fintype.card_coe] using endpoint_count_lt ch hK hconv hV hm

/-- There are only two exterior signs per plank. -/
theorem cell_count_le_pow (ch : CounterexampleChart K f) : Fintype.card (Cells ch) ≤ 2^m := by
  have hh := Fintype.card_subtype_le (fun s => s ∈ activeCells ch.chart.cellFormula)
  simpa only [Cells, Fintype.card_finset, Fintype.card_fin] using hh

/-- The actual-chart contradiction is already complete when the entire
sign cube has at most twice as many vertices as planks. -/
theorem no_counterexample_of_pow_le (ch : CounterexampleChart K f) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal) (hm : 0 < m) (hpow : 2^m ≤ 2*m) :
    False :=
  (endpoint_count_lt ch hK hconv hV hm).not_ge ((cell_count_le_pow ch).trans hpow)

end Plank.PlanarCellCountStrict
