/- Pair interactions and support coordinates for planar endpoint charts. -/
module

public import Plank.Proofs.Quant.PlanarSeparableChart

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenCellSections

open Set MeasureTheory PlanarQuantitative PlanarPlankCellCharts PlanarPolygonCharts
open PlanarCounterexampleChart PlanarBodySectionDensity PlanarSeparableChart
open PlanarDirectionDerivatives PlanarPairArea PlanarSevenCellArea QuadraticChartCalculus
open PlanarParameterDomain (Endpoints)

def widthForm (i : Fin 3) : Endpoints 3 →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj i).comp (LinearMap.snd ℝ (Fin 3 → ℝ) (Fin 3 → ℝ)-
    LinearMap.fst ℝ (Fin 3 → ℝ) (Fin 3 → ℝ))).toAffineMap

@[simp] theorem widthForm_apply (i : Fin 3) (e : Endpoints 3) :
    widthForm i e = e.2 i-e.1 i := rfl

@[simp] theorem widthForm_linear (i : Fin 3) (e : Endpoints 3) :
    (widthForm i).linear e = e.2 i-e.1 i := rfl

def pairFormula (c01 c02 c12 : ℝ) : QuadraticFormula (Endpoints 3) where
  size := 3
  left k := if k=0 then c01 • widthForm 0 else if k=1 then c02 • widthForm 0 else c12 • widthForm 1
  right k := if k=0 then widthForm 1 else widthForm 2

theorem eval_pairFormula (c01 c02 c12 : ℝ) (e : Endpoints 3) :
    (pairFormula c01 c02 c12).eval e =
      c01*(e.2 0-e.1 0)*(e.2 1-e.1 1)+c02*(e.2 0-e.1 0)*(e.2 2-e.1 2)+
      c12*(e.2 1-e.1 1)*(e.2 2-e.1 2) := by
  simp [QuadraticFormula.eval, pairFormula, Finset.sum_range_succ]

theorem derivative_pairFormula (c01 c02 c12 : ℝ) (e z : Endpoints 3) :
    derivative (pairFormula c01 c02 c12) e z =
      c01*((e.2 0-e.1 0)*(z.2 1-z.1 1)+(e.2 1-e.1 1)*(z.2 0-z.1 0))+
      c02*((e.2 0-e.1 0)*(z.2 2-z.1 2)+(e.2 2-e.1 2)*(z.2 0-z.1 0))+
      c12*((e.2 1-e.1 1)*(z.2 2-z.1 2)+(e.2 2-e.1 2)*(z.2 1-z.1 1)) := by
  simp [derivative_apply, pairFormula, Finset.sum_range_succ]
  ring

theorem hessian_pairFormula (c01 c02 c12 : ℝ) (z : Endpoints 3) :
    hessian (pairFormula c01 c02 c12) z z =
      2*(c01*(z.2 0-z.1 0)*(z.2 1-z.1 1)+c02*(z.2 0-z.1 0)*(z.2 2-z.1 2)+
        c12*(z.2 1-z.1 1)*(z.2 2-z.1 2)) := by
  simp [hessian_apply, pairFormula, Finset.sum_range_succ]
  ring

def interactionRow (c01 c02 c12 : ℝ) (e : Endpoints 3) : Fin 3 → ℝ :=
  ![c01*(e.2 1-e.1 1)+c02*(e.2 2-e.1 2),
    c01*(e.2 0-e.1 0)+c12*(e.2 2-e.1 2),
    c02*(e.2 0-e.1 0)+c12*(e.2 1-e.1 1)]

theorem derivative_pair_lower (c01 c02 c12 : ℝ) (e : Endpoints 3) (i : Fin 3) :
    derivative (pairFormula c01 c02 c12) e (lowerDirection i) =
      -interactionRow c01 c02 c12 e i := by
  rw [derivative_pairFormula]
  fin_cases i <;> simp [lowerDirection, interactionRow] <;> ring

theorem derivative_pair_upper (c01 c02 c12 : ℝ) (e : Endpoints 3) (i : Fin 3) :
    derivative (pairFormula c01 c02 c12) e (upperDirection i) =
      interactionRow c01 c02 c12 e i := by
  rw [derivative_pairFormula]
  fin_cases i <;> simp [upperDirection, interactionRow]

def subtractFormula {κ : Type*} (q r : QuadraticFormula (EndpointSpace κ)) :
    QuadraticFormula (EndpointSpace κ) :=
  addFormula q ⟨r.size, fun k => -r.left k, r.right⟩

theorem eval_subtractFormula {κ : Type*} (q r : QuadraticFormula (EndpointSpace κ))
    (e : EndpointSpace κ) : (subtractFormula q r).eval e = q.eval e-r.eval e := by
  rw [subtractFormula, eval_addFormula]
  simp [QuadraticFormula.eval, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem derivative_subtractFormula {κ : Type*} [Fintype κ]
    (q r : QuadraticFormula (EndpointSpace κ)) (e : EndpointSpace κ) :
    derivative (subtractFormula q r) e = derivative q e-derivative r e := by
  apply (hasFDerivAt_eval (subtractFormula q r) e).unique
  apply ((hasFDerivAt_eval q e).sub (hasFDerivAt_eval r e)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun x => eval_subtractFormula q r x)

theorem hessian_subtractFormula {κ : Type*} [Fintype κ]
    (q r : QuadraticFormula (EndpointSpace κ)) (z : EndpointSpace κ) :
    hessian (subtractFormula q r) z z = hessian q z z-hessian r z z := by
  have hp := eval_subtractFormula q r ((0 : EndpointSpace κ)+(1 : ℝ) • z)
  have hm := eval_subtractFormula q r ((0 : EndpointSpace κ)+(-1 : ℝ) • z)
  have h0 := eval_subtractFormula q r 0
  rw [QuadraticChartCalculus.eval_line, QuadraticChartCalculus.eval_line,
    QuadraticChartCalculus.eval_line] at hp hm
  nlinarith only [hp, hm, h0]

/-- Every endpoint lies strictly inside its support interval at an
interior point of the actual shifted endpoint domain. -/
theorem endpoint_bounds_of_interior {m : ℕ} (K : Set Point)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (B : ℝ) {e : Endpoints m}
    (he : e ∈ interior (PlanarShiftedDomain.domain K f B)) (i : Fin m) :
    e.1 i ∈ Ioo 0 1 ∧ e.2 i ∈ Ioo 0 1 := by
  let L : Endpoints m →ₗ[ℝ] ℝ := (LinearMap.proj i).comp (LinearMap.fst ℝ _ _)
  let U : Endpoints m →ₗ[ℝ] ℝ := -((LinearMap.proj i).comp (LinearMap.snd ℝ _ _))
  have hL : Function.Surjective L := fun r => ⟨(fun _ => r, 0), by simp [L]⟩
  have hU : Function.Surjective U := fun r => ⟨(0, fun _ => -r), by simp [U]⟩
  have hlo : 0 < e.1 i := PlanarShiftedDomain.strict_linear_lower_of_interior L hL
    (fun _ h => (h.1.1 i).1) he
  have hneg : -1 < -e.2 i := PlanarShiftedDomain.strict_linear_lower_of_interior U hU
    (fun _ h => neg_le_neg (h.1.1 i).2.2) he
  have horder := PlanarShiftedDomain.strict_windows_of_interior K f B he i
  exact ⟨⟨hlo, horder.trans (neg_lt_neg_iff.mp hneg)⟩,
    ⟨hlo.trans horder, neg_lt_neg_iff.mp hneg⟩⟩

/-- Actual unit directional widths identify the linear part of the deficit
with minus the sum of endpoint-width velocities. -/
theorem deficit_linear_unit {K : Set Point} {f : Fin 3 → Point →ᵃ[ℝ] ℝ}
    (B : ℝ) (hunit : ∀ i, Plank.Convex.DeficientHeightTilt.rangeWidth K (f i) = 1)
    (z : Endpoints 3) :
    (PlanarShiftedDomain.deficit K f B).linear z = -∑ i, (z.2 i-z.1 i) := by
  simp [PlanarShiftedDomain.deficit, PlanarShiftedDomain.budgetLinear, hunit]

end Plank.PlanarSevenCellSections
