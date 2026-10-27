/- The one-window area deficit is controlled by its integral Euler slack. -/
module

public import Plank.Proofs.Quant.ConcaveDensity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ConcaveDensitySlack

open Set MeasureTheory intervalIntegral ConcaveDensity

theorem left_chord_integral (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2*(1-r)*(∫ x in 0..r, h x) ≤ r*(2-r)*h r-r^2*h 1 := by
  have hpoint (x : ℝ) (hx : x ∈ Icc 0 r) :
      (1-r)*h x ≤ (1-x)*h r+(x-r)*h 1 := by
    rcases lt_or_eq_of_le hx.2 with hxr | rfl
    · have ht := hc.slope_anti_adjacent
        (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1,hx.2.trans hr1.le⟩)
        (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hxr hr1
      have hh := (div_le_div_iff₀ (sub_pos.mpr hr1) (sub_pos.mpr hxr)).mp ht
      nlinarith only [hh]
    · ring_nf
      exact le_rfl
  have hh := integral_mono_on (μ := volume) hr0
    ((hcont.const_mul (1-r)).intervalIntegrable 0 r)
    ((by fun_prop : Continuous (fun x : ℝ => (1-x)*h r+(x-r)*h 1)).intervalIntegrable 0 r)
    hpoint
  have he : (fun x : ℝ => (1-x)*h r+(x-r)*h 1) =
      fun x => h r-r*h 1+(h 1-h r)*x := by funext x; ring
  rw [intervalIntegral.integral_const_mul,he,intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous (fun x : ℝ => (h 1-h r)*x)).intervalIntegrable 0 r),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,integral_id] at hh
  simp only [sub_zero,zero_pow (by decide : 2 ≠ 0),smul_eq_mul] at hh
  nlinarith only [hh]

/-- Quantitative rigidity: the nonnegative one-window deficit is bounded
by its Euler slack. This does not assume that the density is affine. -/
theorem excess_le_balance (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) (h1 : 0 ≤ h 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2*excess h r ≤ (2-r)*(r*h r+2*r*mass h-2*(∫ x in 0..r, h x)) := by
  have hh := left_chord_integral h hcont hc hr0 hr1
  have hn := mul_nonneg (sq_nonneg r) h1
  unfold excess
  nlinarith only [hh,hn]

theorem excess_nonneg (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) (h1 : 0 ≤ h 1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : 0 ≤ excess h r := by
  have hh := excess_quadratic_scaling h hcont hc h1 hr
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  simpa only [excess_one,mul_zero,mul_one] using hh

/-- Equality in the first-variation balance already gives equality in
the actual integrated window bound. -/
theorem integral_eq_of_balance_eq (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) (h1 : 0 ≤ h 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (he : 2*(∫ x in 0..r, h x) = r*h r+2*r*mass h) :
    (∫ x in 0..r, h x) = mass h*(2*r-r^2) := by
  have hl := excess_le_balance h hcont hc h1 hr0 hr1
  have hn := excess_nonneg h hcont hc h1 ⟨hr0,hr1.le⟩
  rw [← he,sub_self,mul_zero] at hl
  have hz : excess h r = 0 := by linarith only [hl,hn]
  exact (sub_eq_zero.mp hz).symm

end Plank.ConcaveDensitySlack

/-- info: 'Plank.ConcaveDensitySlack.integral_eq_of_balance_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.ConcaveDensitySlack.integral_eq_of_balance_eq
