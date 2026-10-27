module
/- First derivatives and an anchor identity for signed positive-part squares. -/
public import Plank.Proofs.Quant.CyclicGapCancellation
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section
noncomputable section

namespace Quant.PositivePartEuler

open Filter CyclicGapCancellation
open scoped Topology

theorem hasDerivAt_squarePos (x : ℝ) :
    HasDerivAt squarePos (2*max 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [max_eq_left hx.le,mul_zero]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [continuousAt_id.eventually_lt_const hx] with y hy
    change y < 0 at hy
    simp [squarePos,max_eq_left hy.le]
  · have hs : HasDerivAt (fun y : ℝ => y^2) 0 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).fun_pow 2
    have hlo := hs.isLittleO
    simp only [sub_zero,zero_pow (by decide : 2 ≠ 0),smul_zero] at hlo
    have hbound : ∀ y : ℝ, ‖squarePos y‖ ≤ ‖y^2‖ := by
      intro y
      change |(max 0 y)^2| ≤ |y^2|
      rw [abs_of_nonneg (sq_nonneg (max 0 y)),abs_of_nonneg (sq_nonneg y)]
      by_cases hy : y ≤ 0
      · simp only [max_eq_left hy,zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg y
      · rw [max_eq_right (le_of_not_ge hy)]
    have hh := (Asymptotics.isBigO_of_le (𝓝 (0 : ℝ)) hbound).trans_isLittleO hlo
    apply HasDerivAt.of_isLittleO
    convert hh using 1 <;> first | rfl | (ext y; simp [squarePos])
  · rw [max_eq_right hx.le]
    have hs : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
      simpa using (hasDerivAt_id x).fun_pow 2
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuousAt_id.eventually_const_lt hx] with y hy
    change 0 < y at hy
    simp only [squarePos,max_eq_right hy.le]

theorem hasDerivAt_squarePos_affine (x v : ℝ) :
    HasDerivAt (fun t : ℝ => squarePos (x+t*v)) (2*max 0 x*v) 0 := by
  have ht : HasDerivAt (fun t : ℝ => x+t*v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add x
  have hh := (hasDerivAt_squarePos (x+0*v)).comp 0 ht
  simpa only [Function.comp_def,zero_mul,add_zero] using hh

theorem mul_posPart (x : ℝ) : x*max 0 x = squarePos x := by
  by_cases hx : x ≤ 0
  · simp [max_eq_left hx,squarePos]
  · simp only [max_eq_right (le_of_not_ge hx),squarePos]
    ring

/-- At a local minimum along a line pointing away from an anchor, the value
of a signed sum of positive-part squares is a sum of linear anchor terms.
Coefficients may have either sign, so the result includes loss penalties. -/
theorem anchor_identity {ι : Type*} [Fintype ι]
    (coefficient value anchor : ι → ℝ) (δ δanchor : ℝ)
    (hmin : IsLocalMin (fun t : ℝ =>
      (∑ i, coefficient i*squarePos (value i+t*(value i-anchor i)))-
        (δ+t*(δ-δanchor))^2) 0) :
    (∑ i, coefficient i*squarePos (value i))-δ^2 =
      (∑ i, coefficient i*anchor i*max 0 (value i))-δ*δanchor := by
  classical
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (hasDerivAt_squarePos_affine (value i) (value i-anchor i)).const_mul (coefficient i))
  have hd : HasDerivAt (fun t : ℝ => (δ+t*(δ-δanchor))^2)
      (2*δ*(δ-δanchor)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (δ-δanchor)).const_add δ).fun_pow 2
  have hz := hmin.hasDerivAt_eq_zero (hs.sub hd)
  have he : (∑ i, coefficient i*(2*max 0 (value i)*(value i-anchor i))) =
      2*((∑ i, coefficient i*squarePos (value i))-
        (∑ i, coefficient i*anchor i*max 0 (value i))) := by
    rw [← Finset.sum_sub_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_posPart]
    ring
  rw [he] at hz
  nlinarith only [hz]

end Quant.PositivePartEuler
