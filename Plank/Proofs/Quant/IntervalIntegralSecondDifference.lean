/- Symmetric finite-difference bounds, valid at corners of a continuous density. -/
module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.IntervalIntegralSecondDifference
open Set MeasureTheory

def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in 0..x, f t

theorem identity {f : ℝ → ℝ} (hf : Continuous f) (x h : ℝ) :
    primitive f (x+h)+primitive f (x-h)-2*primitive f x =
      ∫ t in 0..h, (f (x+t)-f (x-t)) := by
  have hr : (∫ t in 0..h, f (x+t)) = ∫ t in x..x+h, f t := by
    rw [intervalIntegral.integral_comp_add_left]
    simp only [add_zero]
  have hl : (∫ t in 0..h, f (x-t)) = ∫ t in x-h..x, f t := by
    rw [intervalIntegral.integral_comp_sub_left]
    simp only [sub_zero]
  rw [intervalIntegral.integral_sub (f := fun t : ℝ => f (x+t))
    (g := fun t : ℝ => f (x-t))
    ((hf.comp (by fun_prop : Continuous (fun t : ℝ => x+t))).intervalIntegrable _ _)
    ((hf.comp (by fun_prop : Continuous (fun t : ℝ => x-t))).intervalIntegrable _ _),hr,hl]
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 x) (hf.intervalIntegrable x (x+h))
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable 0 (x-h)) (hf.intervalIntegrable (x-h) x)
  unfold primitive
  linarith only [h₁,h₂]

/-- Only a one-sided slope bound is needed; the density need not have a derivative. -/
theorem upper {f : ℝ → ℝ} (hf : Continuous f) {x h L : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ t ∈ Icc 0 h, f (x+t)-f (x-t) ≤ 2*L*t) :
    primitive f (x+h)+primitive f (x-h)-2*primitive f x ≤ L*h^2 := by
  rw [identity hf]
  have hc : Continuous (fun t => f (x+t)-f (x-t)) := by fun_prop
  have hm := intervalIntegral.integral_mono_on (μ := volume) hh
    (hc.intervalIntegrable 0 h)
    ((by fun_prop : Continuous (fun t : ℝ => 2*L*t)).intervalIntegrable 0 h) hbound
  rw [intervalIntegral.integral_const_mul,integral_id] at hm
  nlinarith only [hm]

theorem lower {f : ℝ → ℝ} (hf : Continuous f) {x h L : ℝ} (hh : 0 ≤ h)
    (hbound : ∀ t ∈ Icc 0 h, -2*L*t ≤ f (x+t)-f (x-t)) :
    -L*h^2 ≤ primitive f (x+h)+primitive f (x-h)-2*primitive f x := by
  have hm := upper (f := fun x => -f x) hf.neg hh (L := L) (x := x) (by
    intro t ht
    have hb := hbound t ht
    linarith only [hb])
  simp only [primitive,intervalIntegral.integral_neg] at hm ⊢
  linarith only [hm]

end Quant.IntervalIntegralSecondDifference

/-- info: 'Quant.IntervalIntegralSecondDifference.upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.IntervalIntegralSecondDifference.upper
