/- A local square-root scaling gives a global forward cell-area bound. -/
module

public import Plank.Proofs.Quant.PlanarCellChartCalculus

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellRayConcavity

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarCellArea PlanarPlankCellCharts
open Plank.Convex.DeficientHeightTilt

variable {κ : Type*}

/-- Concavity compares a forward cell with one known backward cell. This
bound is global in the forward ray, including after chart changes or after
the cell becomes empty. No polynomial formula away from the base is used. -/
theorem forward_area_le {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) (p z : EndpointSpace κ)
    (ε c : ℝ) (hε : 0 < ε)
    (hback : (signCell K f (p+(-ε) • z).1 (p+(-ε) • z).2 s).Nonempty)
    (hscale : Real.sqrt (volume (signCell K f (p+(-ε) • z).1 (p+(-ε) • z).2 s)).toReal =
      (1-ε*c)*Real.sqrt (volume (signCell K f p.1 p.2 s)).toReal)
    (t : ℝ) (ht : 0 ≤ t) :
    (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
  by_cases hne : (signCell K f (p+t • z).1 (p+t • z).2 s).Nonempty
  · let u := cutOffsets f p.1 p.2 s
    let v := cutDirection z.1 z.2 s
    have heq (r : ℝ) : signCell K f (p+r • z).1 (p+r • z).2 s =
        cell K (cutForms f s) (u+r • v) := by
      rw [signCell_eq_cell]
      exact congrArg (cell K (cutForms f s)) (cutOffsets_motion f p.1 p.2 z.1 z.2 s r)
    have hden : 0 < t+ε := add_pos_of_nonneg_of_pos ht hε
    have hweights : t/(t+ε)+ε/(t+ε) = 1 := by rw [← add_div,div_self hden.ne']
    have hmix : (t/(t+ε)) • (u+(-ε) • v)+(ε/(t+ε)) • (u+t • v) = u := by
      ext i
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      field_simp [hden.ne']
      ring
    have hbm := (concaveOn_sqrt_area_cell hK hconv (cutForms f s)).2
      (heq (-ε) ▸ hback) (heq t ▸ hne) (div_nonneg ht hden.le)
      (div_nonneg hε.le hden.le) hweights
    rw [hmix] at hbm
    dsimp only at hbm
    rw [← heq (-ε),← heq t,← signCell_eq_cell] at hbm
    change t/(t+ε)*Real.sqrt (volume (signCell K f (p+(-ε) • z).1 (p+(-ε) • z).2 s)).toReal+
      ε/(t+ε)*Real.sqrt (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
        Real.sqrt (volume (signCell K f p.1 p.2 s)).toReal at hbm
    rw [hscale] at hbm
    have hh := mul_le_mul_of_nonneg_left hbm hden.le
    have halg (x y : ℝ) : (t+ε)*(t/(t+ε)*((1-ε*c)*x)+ε/(t+ε)*y) =
        t*((1-ε*c)*x)+ε*y := by field_simp [hden.ne']
    rw [halg] at hh
    have hroot : Real.sqrt (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
        (1+t*c)*Real.sqrt (volume (signCell K f p.1 p.2 s)).toReal := by
      exact le_of_mul_le_mul_left (by nlinarith only [hh]) hε
    have hsquare := mul_self_le_mul_self (Real.sqrt_nonneg _) hroot
    rw [← sq,← sq,mul_pow,Real.sq_sqrt ENNReal.toReal_nonneg,
      Real.sq_sqrt ENNReal.toReal_nonneg] at hsquare
    simpa only [mul_comm] using hsquare
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne,measure_empty,ENNReal.toReal_zero]
    exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)

end Plank.PlanarCellRayConcavity

/-- info: 'Plank.PlanarCellRayConcavity.forward_area_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCellRayConcavity.forward_area_le
