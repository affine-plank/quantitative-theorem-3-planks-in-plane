/- An actual generic polygonal counterexample yields a zero-margin positive chart. -/
module

public import Plank.Proofs.Quant.PlanarShiftedDomain
public import Plank.Proofs.Quant.PlanarPositiveChart

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCounterexampleChart

open Set MeasureTheory PlanarQuantitative PlanarPositiveChart PlanarShiftedDomain
open PlanarParameterDomain (Endpoints budget gapArea)
open PlanarParameterDerivatives (area)
open QuadraticChartCalculus
open Plank.Convex.DeficientHeightTilt

theorem area_margin_eq {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (B : ℝ) (p : Endpoints m) :
    area K f p-(volume K).toReal*(deficit K f B p)^2 = margin K f B p := by
  rw [deficit_apply]
  rfl

/-- The actual smaller-domain minimum together with the selected common
cell/gap/margin atlas. Its zero margin and positive deficit are conclusions. -/
structure CounterexampleChart {m : ℕ} (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ) where
  B : ℝ
  positive_budget : 0 < B
  budget_lt_one : B < 1
  chart : PositiveMarginChart K f (domain K f B) (volume K).toReal (deficit K f B)
  nonnegative : ∀ p ∈ domain K f B, 0 ≤ margin K f B p
  zero_margin : margin K f B chart.point = 0
  positive_gap : 0 < gapArea K f chart.point
  positive_deficit : 0 < deficit K f B chart.point

namespace CounterexampleChart

variable {m : ℕ} {K : Set Point} {f : Fin m → Point →ᵃ[ℝ] ℝ}

theorem point_budget_lt (ch : CounterexampleChart K f) : budget K f ch.chart.point < ch.B :=
  sub_pos.mp (by simpa only [deficit_apply] using ch.positive_deficit)

/-- The selected polynomial attains the actual zero-margin identity. -/
theorem gap_value (ch : CounterexampleChart K f) :
    ch.chart.gapFormula.eval ch.chart.point =
      (volume K).toReal*(deficit K f ch.B ch.chart.point)^2 := by
  rw [← ch.chart.gap_area ch.chart.point ch.chart.closure_point
    (fun i => (ch.chart.strict_windows i).le), deficit_apply]
  exact sub_eq_zero.mp ch.zero_margin

theorem margin_value (ch : CounterexampleChart K f) :
    ch.chart.marginFormula.eval ch.chart.point = 0 := by
  rw [ch.chart.margin_identity, ch.gap_value, sub_self]

/-- The total gap formula is stationary up to the exact squared-deficit term. -/
theorem stationary_gap (ch : CounterexampleChart K f) :
    derivative ch.chart.gapFormula ch.chart.point =
      (2*(volume K).toReal*(deficit K f ch.B ch.chart.point)) •
        (deficit K f ch.B).linear.toContinuousLinearMap := ch.chart.stationary_gap

theorem positive_gap_hessian (ch : CounterexampleChart K f) :
    ∀ z : Endpoints m, z ≠ 0 → 0 < hessian ch.chart.gapFormula z z :=
  ch.chart.positive_gap_hessian ENNReal.toReal_nonneg

/-- The selected gap polynomial is positive on the entire parameter space,
even outside the region where it represents geometric area. Its margin is
a strictly positive quadratic away from the stationary zero. -/
theorem gap_formula_pos (ch : CounterexampleChart K f)
    (hV : 0 < (volume K).toReal) (e : Endpoints m) :
    0 < ch.chart.gapFormula.eval e := by
  by_cases he : e = ch.chart.point
  · rw [he, ch.gap_value]
    exact mul_pos hV (sq_pos_of_pos ch.positive_deficit)
  · have hp := eval_lt_of_stationary ch.chart.marginFormula ch.chart.point
      ch.chart.stationary ch.chart.positive he
    rw [ch.margin_value, ch.chart.margin_identity] at hp
    exact (mul_nonneg hV.le (sq_nonneg _)).trans_lt (sub_pos.mp hp)

end CounterexampleChart

/-- A normalized counterexample on a generic polygon constructs the actual
shifted domain, strict boundary barrier and zero-margin positive-definite chart.
Only the previous full quantitative case is used as an induction hypothesis. -/
theorem exists_counterexample_chart {m : ℕ} (hsmall : m+1 ≤ 3) (hm : SharpPlanarBound m)
    {ι : Type*} [Fintype ι] (K : Set Point) (hcompact : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (F : ι → Point →ᵃ[ℝ] ℝ) (c : ι → ℝ) (hK : K = {x | ∀ j, F j x ≤ c j})
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, 0 < rangeWidth K (f i))
    (hbody : ∀ i j, PlanarDirectionDerivatives.cross (f i) (F j) ≠ 0)
    (hpairs : ∀ i j, i ≠ j → PlanarDirectionDerivatives.cross (f i) (f j) ≠ 0)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    {p₀ : Endpoints (m+1)} (hp₀ : p₀ ∈ PlanarParameterDomain.domain K f)
    (hbad : gapArea K f p₀ < (max 0 (1-budget K f p₀))^2 * (volume K).toReal) :
    Nonempty (CounterexampleChart K f) := by
  obtain ⟨B, hBpos, hB, p, hp, hzero, hnonneg, hboundary⟩ := exists_shifted_barrier hsmall hm
    hcompact hconv hne hV f hf hnorm hp₀ hbad
  obtain ⟨ch⟩ := exists_actual_positive_margin_chart K hcompact hne F c hK f hf hbody hpairs
    (domain K f B) (isCompact_domain K f B) (fun _ he i => (he.1.1 i).2.1)
    (fun _ he => strict_windows_of_interior K f B he) (volume K).toReal (deficit K f B)
    p (interior_subset hp) (by
      intro e he hn
      rw [area_margin_eq, area_margin_eq, hzero]
      exact hboundary e he hn)
  have hmem : ch.point ∈ domain K f B := interior_subset ch.interior_point
  have hle : margin K f B ch.point ≤ 0 := by
    have hh := ch.minimum (interior_subset hp)
    change area K f ch.point-(volume K).toReal*(deficit K f B ch.point)^2 ≤
      area K f p-(volume K).toReal*(deficit K f B p)^2 at hh
    rwa [area_margin_eq, area_margin_eq, hzero] at hh
  have hz : margin K f B ch.point = 0 := le_antisymm hle (hnonneg ch.point hmem)
  have hG := PlanarGapPositivity.gapArea_pos_of_le_three hsmall hcompact hconv hne hV f ch.point
    (fun i => (hmem.1.1 i).2.1) hf (hmem.2.trans_lt hB)
  have hd : 0 < deficit K f B ch.point := by
    rw [deficit_apply]
    have hdnonneg : 0 ≤ B-budget K f ch.point := sub_nonneg.mpr hmem.2
    have hdne : B-budget K f ch.point ≠ 0 := by
      intro hh
      have hbadzero : gapArea K f ch.point = 0 := by simpa [margin, hh] using hz
      exact (ne_of_gt hG) hbadzero
    exact lt_of_le_of_ne hdnonneg hdne.symm
  exact ⟨{
    B := B
    positive_budget := hBpos
    budget_lt_one := hB
    chart := ch
    nonnegative := hnonneg
    zero_margin := hz
    positive_gap := hG
    positive_deficit := hd }⟩

end Plank.PlanarCounterexampleChart
