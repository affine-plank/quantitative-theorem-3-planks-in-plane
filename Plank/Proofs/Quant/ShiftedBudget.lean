/- Scalar and root-minimum steps in the shifted-budget planar proof candidate.
Geometric minimization, chart selection and the cell-curvature limits are not
asserted by this module. -/
module

public import Mathlib.Analysis.Real.Sqrt
public import Plank.Proofs.Quant.CellValueCurvature
import Mathlib.Tactic.Linarith

@[expose] public section
noncomputable section
namespace Plank.ShiftedBudget

/-- Express an area using the square root of its normalized value. -/
theorem root_area_identity (V G : ℝ) (hV : 0 < V) (hG : 0 ≤ G) :
    G = V * (Real.sqrt (G/V))^2 := by
  have hh := (eq_div_iff hV.ne').mp (Real.sq_sqrt (div_nonneg hG hV.le))
  nlinarith only [hh]

/-- A negative minimum of the square-root margin gives a smaller positive
budget whose quadratic margin is nonnegative and vanishes at that minimum.
The index type can be the subtype of a compact endpoint domain; compactness
and attainment are explicit external inputs through the minimizing point. -/
theorem budget_of_root_minimum {X : Type*} (V : ℝ) (R G : X → ℝ) (x : X)
    (hV : 0 < V) (hG : ∀ y, 0 ≤ G y) (hGx : 0 < G x) (hRx : 0 ≤ R x)
    (hbad : Real.sqrt (G x/V) + R x < 1)
    (hmin : ∀ y, Real.sqrt (G x/V) + R x ≤ Real.sqrt (G y/V) + R y) :
    ∃ B : ℝ, 0 < B ∧ B < 1 ∧ R x < B ∧ G x = V*(B-R x)^2 ∧
      ∀ y, R y ≤ B → V*(B-R y)^2 ≤ G y := by
  let B := Real.sqrt (G x/V) + R x
  have hx : 0 < Real.sqrt (G x/V) := Real.sqrt_pos.2 (div_pos hGx hV)
  refine ⟨B, by dsimp [B]; linarith, hbad, by dsimp [B]; linarith, ?_, ?_⟩
  · simpa only [B, add_sub_cancel_right] using root_area_identity V (G x) hV (hG x)
  · intro y hy
    have hl : B-R y ≤ Real.sqrt (G y/V) := by
      have hm := hmin y
      dsimp [B]
      linarith
    have hn : 0 ≤ B-R y := sub_nonneg.mpr hy
    have hs : 0 ≤ Real.sqrt (G y/V) := Real.sqrt_nonneg _
    have hp := mul_nonneg (sub_nonneg.mpr hl) (add_nonneg hs hn)
    have hsq : (B-R y)^2 ≤ (Real.sqrt (G y/V))^2 := by nlinarith only [hp]
    have hm := mul_le_mul_of_nonneg_left hsq hV.le
    rw [← root_area_identity V (G y) hV (hG y)] at hm
    exact hm

/-- On the smaller budget domain, the old endpoint-boundary estimate pays
strictly more than the new target. -/
theorem boundary_target_strict (V B R : ℝ) (hV : 0 < V)
    (hB : B < 1) (hR : R ≤ B) :
    V*(B-R)^2 < V*(1-R)^2 := by
  have hp : 0 < (1-B)*((1-R)+(B-R)) :=
    mul_pos (by linarith) (by linarith)
  have hs : (B-R)^2 < (1-R)^2 := by nlinarith only [hp]
  exact mul_lt_mul_of_pos_left hs hV

/-- The smaller budget strengthens the seven-cell matrix row inequality.
No sign assumptions are needed for this algebraic rearrangement. -/
theorem stationary_row_budget (k V B r s t c d : ℝ)
    (h : k*(1-r) ≤ 2*V*(B-(r+s+t)) + c*s + d*t) :
    k-2*V+2*V*(1-B) ≤ (k-2*V)*r+(c-2*V)*s+(d-2*V)*t := by
  nlinarith only [h]

/-- At zero shifted margin the stationarity/curvature data supplied by the
bounded-direction limit contradict positive margin curvature. -/
theorem no_zero_margin (V delta G velocity curvature : ℝ)
    (hV : 0 < V) (hd : 0 < delta) (hG : 0 < G)
    (hzero : G = V*delta^2)
    (hstationary : G = 2*V*delta*velocity)
    (hconcave : curvature ≤ G/2)
    (hpositive : 2*V*velocity^2 < curvature) : False := by
  exact (ne_of_lt (CellValueCurvature.strict_negative_margin V delta G velocity curvature
    hV hd hG hstationary hconcave hpositive)) hzero

end Plank.ShiftedBudget
