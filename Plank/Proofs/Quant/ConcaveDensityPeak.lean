/- Peak rigidity for continuous nonnegative concave section densities. -/
module

public import Plank.Proofs.Quant.ConcaveDensitySlack

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ConcaveDensityPeak

open Set MeasureTheory intervalIntegral ConcaveDensity

/-- The endpoint chord gives this lower bound on every initial integral. -/
theorem initial_integral_lower (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) (h1 : 0 ≤ h 1)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    h 0*(r-r^2/2) ≤ ∫ x in 0..r, h x := by
  have hpoint (x : ℝ) (hx : x ∈ Icc 0 r) : (1-x)*h 0 ≤ h x := by
    have hx1 : x ≤ 1 := hx.2.trans hr.2
    have hh := hc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      (sub_nonneg.mpr hx1) hx.1 (sub_add_cancel 1 x)
    simp only [smul_eq_mul,mul_zero,mul_one,zero_add] at hh
    exact (le_add_of_nonneg_right (mul_nonneg hx.1 h1)).trans hh
  have hh := integral_mono_on (μ := volume) hr.1
    ((by fun_prop : Continuous (fun x : ℝ => (1-x)*h 0)).intervalIntegrable 0 r)
    (hcont.intervalIntegrable 0 r) hpoint
  have he : (fun x : ℝ => (1-x)*h 0) = fun x => h 0-x*h 0 := by
    funext x
    ring
  rw [he,integral_sub (μ := volume) (f := fun _ : ℝ => h 0)
    (g := fun x : ℝ => x*h 0) intervalIntegrable_const
    ((continuous_id.mul_const (h 0)).intervalIntegrable 0 r),
    intervalIntegral.integral_const,intervalIntegral.integral_mul_const,integral_id] at hh
  simp only [sub_zero,zero_pow (by decide : 2 ≠ 0),smul_eq_mul] at hh
  nlinarith only [hh]

/-- No such density can start above twice its total mass. -/
theorem start_le_twice_mass (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) (h1 : 0 ≤ h 1) :
    h 0 ≤ 2*mass h := by
  have hh := initial_integral_lower h hcont hc h1
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  change h 0*(1-1^2/2) ≤ mass h at hh
  linarith only [hh]

/-- Saturation at the initial endpoint forces every canonical window
to attain the quadratic integral bound. Its geometric interpretation
is supplied separately. -/
theorem integral_eq_of_start_eq (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) (h1 : 0 ≤ h 1)
    (he : h 0 = 2*mass h) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    (∫ x in 0..r, h x) = mass h*(2*r-r^2) := by
  have hl := initial_integral_lower h hcont hc h1 hr
  have hu := ConcaveDensitySlack.excess_nonneg h hcont hc h1 hr
  rw [he] at hl
  unfold excess at hu
  linarith only [hl,hu]

end Plank.ConcaveDensityPeak

/-- info: 'Plank.ConcaveDensityPeak.start_le_twice_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.ConcaveDensityPeak.start_le_twice_mass
/-- info: 'Plank.ConcaveDensityPeak.integral_eq_of_start_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.ConcaveDensityPeak.integral_eq_of_start_eq
