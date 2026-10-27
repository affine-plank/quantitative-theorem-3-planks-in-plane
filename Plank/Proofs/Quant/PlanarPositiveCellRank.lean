/- The actual positive-cell gradients separate endpoint motions. -/
module

public import Plank.Proofs.Quant.PlanarCellChartCalculus
public import Plank.Proofs.Quant.ComponentRank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPositiveCellRank

open Set MeasureTheory PlanarQuantitative PlanarPolygonCharts PlanarPlankCellCharts
open QuadraticChartCalculus PlanarCounterexampleChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Differentiate an exact finite sum of quadratic formulas. -/
theorem derivative_sum {σ : Type*} [Fintype σ] (q : QuadraticFormula E)
    (qc : σ → QuadraticFormula E) (hsum : ∀ x, q.eval x = ∑ i, (qc i).eval x) (x : E) :
    derivative q x = ∑ i, derivative (qc i) x := by
  have hq := hasFDerivAt_eval q x
  have heq : q.eval = fun y => ∑ i, (qc i).eval y := funext hsum
  rw [heq] at hq
  exact hq.unique (HasFDerivAt.fun_sum (fun i _ => hasFDerivAt_eval (qc i) x))

theorem hessian_from_derivatives (q : QuadraticFormula E) (z : E) :
    hessian q z z = derivative q z z-derivative q 0 z := by
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L z) (derivative_add q 0 z)
  simp only [zero_add, add_apply] at hh
  linarith only [hh]

/-- The fixed gap Hessian is the sum of the fixed cell Hessians. -/
theorem hessian_sum {σ : Type*} [Fintype σ] (q : QuadraticFormula E)
    (qc : σ → QuadraticFormula E) (hsum : ∀ x, q.eval x = ∑ i, (qc i).eval x) (z : E) :
    hessian q z z = ∑ i, hessian (qc i) z z := by
  rw [hessian_from_derivatives, derivative_sum q qc hsum, derivative_sum q qc hsum]
  simp only [sum_apply, ← Finset.sum_sub_distrib,
    ← hessian_from_derivatives]

variable {κ : Type*} [Fintype κ]

/-- Nonzero cell polynomials; their actual areas are positive on the open
chart, while limiting cell areas are allowed to vanish. -/
def activeCells (qc : Finset κ → QuadraticFormula (EndpointSpace κ)) : Finset (Finset κ) := by
  classical
  exact Finset.univ.filter (fun s => ∃ x, (qc s).eval x ≠ 0)

theorem mem_activeCells (qc : Finset κ → QuadraticFormula (EndpointSpace κ)) (s : Finset κ) :
    s ∈ activeCells qc ↔ ∃ x, (qc s).eval x ≠ 0 := by
  classical
  simp [activeCells]

theorem eval_zero_of_inactive (qc : Finset κ → QuadraticFormula (EndpointSpace κ))
    (s : Finset κ) (hs : s ∉ activeCells qc) (x : EndpointSpace κ) : (qc s).eval x = 0 := by
  by_contra hn
  exact hs ((mem_activeCells qc s).mpr ⟨x, hn⟩)

/-- Remove identically zero cells from the exact area-polynomial sum. -/
theorem sum_activeCells (qc : Finset κ → QuadraticFormula (EndpointSpace κ))
    (x : EndpointSpace κ) :
    (∑ s : activeCells qc, (qc s).eval x) = ∑ s : Finset κ, (qc s).eval x := by
  classical
  rw [Finset.sum_coe_sort (activeCells qc) (fun s => (qc s).eval x)]
  exact Finset.sum_subset (Finset.subset_univ _) (fun s _ hs => eval_zero_of_inactive qc s hs x)

variable {m : ℕ} {K : Set Point} {f : Fin m → Point →ᵃ[ℝ] ℝ}

abbrev Cells (ch : CounterexampleChart K f) := ↥(activeCells ch.chart.cellFormula)

theorem gap_sum_active (ch : CounterexampleChart K f) (x : PlanarParameterDomain.Endpoints m) :
    ch.chart.gapFormula.eval x = ∑ s : Cells ch, (ch.chart.cellFormula s).eval x := by
  rw [sum_activeCells, ch.chart.gap_sum]

theorem cell_positive (ch : CounterexampleChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (s : Cells ch) (e : PlanarParameterDomain.Endpoints m) (he : e ∈ ch.chart.region) :
    0 < (ch.chart.cellFormula s).eval e :=
  PlanarCellChartCalculus.eval_pos_of_nonzero hK hconv f s (ch.chart.cellFormula s)
    ch.chart.open_region (ch.chart.cell_area s) ((mem_activeCells _ _).mp s.property) e he

/-- The same active index set counts actual positive-area cells at every
open-chart point; this is a derived geometric identification. -/
theorem activeCells_eq_positive (ch : CounterexampleChart K f) (hK : IsCompact K)
    (hconv : Convex ℝ K) (e : PlanarParameterDomain.Endpoints m) (he : e ∈ ch.chart.region) :
    activeCells ch.chart.cellFormula = Finset.univ.filter (fun s : Finset (Fin m) =>
      0 < (volume (PlanarGapCells.signCell K f e.1 e.2 s)).toReal) := by
  classical
  ext s
  simp only [mem_activeCells, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ch.chart.cell_area s e (subset_closure he)]
  constructor
  · intro hn
    exact PlanarCellChartCalculus.eval_pos_of_nonzero hK hconv f s (ch.chart.cellFormula s)
      ch.chart.open_region (ch.chart.cell_area s) hn e he
  · intro hp
    exact ⟨e, ne_of_gt hp⟩

def gradientMap (ch : CounterexampleChart K f) (e : PlanarParameterDomain.Endpoints m) :
    PlanarParameterDomain.Endpoints m →ₗ[ℝ] (Cells ch → ℝ) :=
  LinearMap.pi (fun s => (derivative (ch.chart.cellFormula s) e).toLinearMap)

/-- The actual cell curvature bound makes the gradient map injective at
every open-chart point. No assumed rank or combinatorial constancy is used. -/
theorem gradientMap_injective (ch : CounterexampleChart K f)
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (e : PlanarParameterDomain.Endpoints m) (he : e ∈ ch.chart.region) :
    Function.Injective (gradientMap ch e) := by
  apply ComponentRank.gradient_map_injective
    (fun s : Cells ch => (derivative (ch.chart.cellFormula s) e).toLinearMap)
    (fun s z => hessian (ch.chart.cellFormula s) z z)
  · intro s z hz
    exact PlanarCellChartCalculus.curvature_nonpos_on_kernel hK hconv f s
      (ch.chart.cellFormula s) ch.chart.open_region (ch.chart.cell_area s) e he z hz
  · intro z hz
    rw [← hessian_sum ch.chart.gapFormula (fun s : Cells ch => ch.chart.cellFormula s)
      (gap_sum_active ch)]
    exact ch.positive_gap_hessian z hz

theorem endpoint_finrank (m : ℕ) : Module.finrank ℝ (PlanarParameterDomain.Endpoints m) = 2*m := by
  simp only [PlanarParameterDomain.Endpoints, Module.finrank_prod, Module.finrank_pi,
    Fintype.card_fin, two_mul]

/-- At least twice as many positive cells as planks are required on the
selected open chart. This is the actual geometric rank bound. -/
theorem endpoint_count_le (ch : CounterexampleChart K f) (hK : IsCompact K)
    (hconv : Convex ℝ K) : 2*m ≤ Fintype.card (Cells ch) := by
  have hne : ch.chart.region.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    simpa [hn] using ch.chart.closure_point
  obtain ⟨e, he⟩ := hne
  have hh := LinearMap.finrank_le_finrank_of_injective (gradientMap_injective ch hK hconv e he)
  simpa only [endpoint_finrank, Module.finrank_pi] using hh

end Plank.PlanarPositiveCellRank
