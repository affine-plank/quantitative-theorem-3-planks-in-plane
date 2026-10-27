/- Quadratic scaling of the one-window excess for a concave density.
The body-section interpretation and union geometry are external. -/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

open Set intervalIntegral
open MeasureTheory (volume)
open scoped Topology

namespace Plank.ConcaveDensity

private theorem chord_left (h : ℝ → ℝ)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h)
    {r x : ℝ} (hr : r < 1) (hx : x ∈ Icc 0 r) :
    (1-r)*h x ≤ (1-x)*h r+(x-r)*h 1 := by
  rcases lt_or_eq_of_le hx.2 with hxr | rfl
  · have ht := hc.slope_anti_adjacent
      (show x ∈ Icc (0 : ℝ) 1 from ⟨hx.1, hx.2.trans hr.le⟩)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hxr hr
    have ht' := (div_le_div_iff₀ (sub_pos.mpr hr) (sub_pos.mpr hxr)).mp ht
    nlinarith
  · ring_nf
    exact le_rfl

private theorem chord_right (h : ℝ → ℝ)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h)
    {r x : ℝ} (hr : 0 ≤ r) (hx : x ∈ Icc r 1) :
    (1-x)*h r+(x-r)*h 1 ≤ (1-r)*h x := by
  rcases lt_or_eq_of_le hx.1 with hrx | rfl
  · rcases lt_or_eq_of_le hx.2 with hx1 | rfl
    · have ht := hc.slope_anti_adjacent
        (show r ∈ Icc (0 : ℝ) 1 from ⟨hr, hx.1.trans hx.2⟩)
        (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) hrx hx1
      have ht' := (div_le_div_iff₀ (sub_pos.mpr hx1) (sub_pos.mpr hrx)).mp ht
      nlinarith
    · ring_nf
      exact le_rfl
  · ring_nf
    exact le_rfl

private theorem integral_chord (a b r u v : ℝ) :
    (∫ x in a..b, (1-x)*u+(x-r)*v) =
      (b-a)*(u-r*v)+(b^2-a^2)/2*(v-u) := by
  have heq : (fun x : ℝ => (1-x)*u+(x-r)*v) =
      (fun x : ℝ => (u-r*v)+x*(v-u)) := by
    funext x
    ring
  rw [heq, integral_add (μ := volume)
    (f := fun _ : ℝ => u-r*v) (g := fun x : ℝ => x*(v-u)) intervalIntegrable_const
    ((continuous_id.mul_const (v-u)).intervalIntegrable a b),
    integral_const, integral_mul_const, integral_id]
  simp only [smul_eq_mul]

/-- The weighted integral inequality controlling the derivative of the
quadratically normalized excess. No derivative of the density is needed. -/
theorem integral_balance (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2*(∫ x in 0..r, h x)-r*h r-2*r*(∫ x in 0..1, h x) ≤ -r*h 1 := by
  have hl := integral_mono_on (μ := volume) hr0
    ((hcont.const_mul (1-r)).intervalIntegrable 0 r)
    ((show Continuous (fun x : ℝ => (1-x)*h r+(x-r)*h 1) by fun_prop).intervalIntegrable 0 r)
    (fun x hx => chord_left h hc hr1 hx)
  have hu := integral_mono_on (μ := volume) hr1.le
    ((show Continuous (fun x : ℝ => (1-x)*h r+(x-r)*h 1) by fun_prop).intervalIntegrable r 1)
    ((hcont.const_mul (1-r)).intervalIntegrable r 1)
    (fun x hx => chord_right h hc hr0 hx)
  rw [integral_const_mul, integral_chord] at hl
  rw [integral_chord, integral_const_mul] at hu
  have htail : (1-r)/2*(h r+h 1) ≤ ∫ x in r..1, h x := by
    apply (mul_le_mul_iff_right₀ (sub_pos.mpr hr1)).mp
    nlinarith [hu]
  have hm := mul_le_mul_of_nonneg_left htail (show 0 ≤ 2*r by positivity)
  have hadd := integral_add_adjacent_intervals (μ := volume)
    (hcont.intervalIntegrable 0 r) (hcont.intervalIntegrable r 1)
  nlinarith

def mass (h : ℝ → ℝ) : ℝ := ∫ x in 0..1, h x

def excess (h : ℝ → ℝ) (r : ℝ) : ℝ :=
  mass h*(2*r-r^2)-(∫ x in 0..r, h x)

theorem excess_zero (h : ℝ → ℝ) : excess h 0 = 0 := by simp [excess]

theorem excess_one (h : ℝ → ℝ) : excess h 1 = 0 := by norm_num [excess, mass]

theorem hasDerivAt_excess (h : ℝ → ℝ) (hcont : Continuous h) (r : ℝ) :
    HasDerivAt (excess h) (mass h*(2-2*r)-h r) r := by
  have hi := integral_hasDerivAt_right (hcont.intervalIntegrable 0 r)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hp : HasDerivAt (fun x : ℝ => mass h*(2*x-x^2)) (mass h*(2-2*r)) r := by
    simpa using (((hasDerivAt_id r).const_mul 2).sub
      ((hasDerivAt_id r).pow 2)).const_mul (mass h)
  exact hp.sub hi

theorem continuous_excess (h : ℝ → ℝ) (hcont : Continuous h) :
    Continuous (excess h) :=
  (show Differentiable ℝ (excess h) from
    fun r => (hasDerivAt_excess h hcont r).differentiableAt).continuous

private theorem ratio_deriv (h : ℝ → ℝ) (hcont : Continuous h)
    {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => excess h x/x^2)
      (((mass h*(2-2*r)-h r)*r^2-excess h r*(2*r))/(r^2)^2) r := by
  have hd : HasDerivAt (fun x : ℝ => x^2) (2*r) r := by
    have hd' := (hasDerivAt_id r).pow 2
    have heq : (id ^ (2 : ℕ) : ℝ → ℝ) = (fun x : ℝ => x^2) := by
      funext x
      rfl
    rw [heq] at hd'
    simpa using hd'
  exact (hasDerivAt_excess h hcont r).div hd (pow_ne_zero 2 hr)

/-- For a concave density, the excess divided by the square of the window
width decreases. Only nonnegativity at the final endpoint is required. -/
theorem normalized_excess_antitone (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) (h1 : 0 ≤ h 1) :
    AntitoneOn (fun r : ℝ => excess h r/r^2) (Ioc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
  · exact (continuous_excess h hcont).continuousOn.div
      (continuous_id.pow 2).continuousOn
      (fun r hr => pow_ne_zero 2 (ne_of_gt hr.1))
  · intro r hr
    simp only [interior_Ioc, mem_Ioo] at hr
    exact (ratio_deriv h hcont (ne_of_gt hr.1)).differentiableAt.differentiableWithinAt
  · intro r hr
    simp only [interior_Ioc, mem_Ioo] at hr
    rw [(ratio_deriv h hcont (ne_of_gt hr.1)).deriv]
    have hb := integral_balance h hcont hc hr.1.le hr.2
    have hb0 : 2*(∫ x in 0..r, h x)-r*h r-2*r*mass h ≤ 0 := by
      dsimp [mass]
      nlinarith [mul_nonneg hr.1.le h1]
    have hid : (mass h*(2-2*r)-h r)*r^2-excess h r*(2*r) =
        r*(2*(∫ x in 0..r, h x)-r*h r-2*r*mass h) := by
      unfold excess
      ring
    rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hr.1.le hb0) (sq_nonneg _)

/-- The exact contraction estimate used for all the marginal plank gaps. -/
theorem excess_quadratic_scaling (h : ℝ → ℝ) (hcont : Continuous h)
    (hc : ConcaveOn ℝ (Icc (0 : ℝ) 1) h) (h1 : 0 ≤ h 1)
    {t r : ℝ} (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    t^2*excess h r ≤ excess h (t*r) := by
  by_cases ht0 : t = 0
  · simp [ht0, excess_zero]
  by_cases hr0 : r = 0
  · simp [hr0, excess_zero]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  have hprod : t*r ≤ r := mul_le_of_le_one_left hr.1 ht.2
  have ha := normalized_excess_antitone h hcont hc h1
    (show t*r ∈ Ioc (0 : ℝ) 1 from ⟨mul_pos htpos hrpos, hprod.trans hr.2⟩)
    (show r ∈ Ioc (0 : ℝ) 1 from ⟨hrpos, hr.2⟩) hprod
  have hb := (div_le_div_iff₀ (sq_pos_of_pos hrpos)
    (sq_pos_of_pos (mul_pos htpos hrpos))).mp ha
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hrpos)).mp
  convert hb using 1 <;> ring

/-- Density of the width parameter for a window contracted about coordinate `c`. -/
def canonicalDensity (f : ℝ → ℝ) (c r : ℝ) : ℝ :=
  c*f ((1-r)*c)+(1-c)*f (c+(1-c)*r)

theorem continuous_canonicalDensity (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ) :
    Continuous (canonicalDensity f c) := by
  unfold canonicalDensity
  fun_prop

private theorem concave_affine (f : ℝ → ℝ)
    (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (a b : ℝ)
    (hm : ∀ x ∈ Icc (0 : ℝ) 1, a*x+b ∈ Icc (0 : ℝ) 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun x => f (a*x+b)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy u v hu hv huv
  have hh := hf.2 (hm x hx) (hm y hy) hu hv huv
  simp only [smul_eq_mul] at hh ⊢
  have heq : a*(u*x+v*y)+b = u*(a*x+b)+v*(a*y+b) := by
    have hz : b*(u+v-1) = 0 := by rw [huv]; ring
    nlinarith [hz]
  rw [heq]
  exact hh

theorem concaveOn_canonicalDensity (f : ℝ → ℝ)
    (hf : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) {c : ℝ} (hc : c ∈ Icc 0 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (canonicalDensity f c) := by
  have hl := concave_affine f hf (-c) c (by
    intro x hx
    constructor <;> nlinarith [hc.1, hc.2, mul_nonneg hc.1 (sub_nonneg.mpr hx.2),
      mul_nonneg hc.1 hx.1])
  have hr := concave_affine f hf (1-c) c (by
    intro x hx
    constructor <;> nlinarith [hc.1, hc.2, mul_nonneg (sub_nonneg.mpr hc.2) hx.1,
      mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hx.2)])
  have hs := (hl.smul hc.1).add (hr.smul (sub_nonneg.mpr hc.2))
  have heq : (fun x : ℝ => c • f (-c*x+c)) +
      (fun x : ℝ => (1-c) • f ((1-c)*x+c)) = canonicalDensity f c := by
    funext x
    simp only [Pi.add_apply, smul_eq_mul, canonicalDensity]
    congr 2 <;> congr 1 <;> ring
  rw [heq] at hs
  exact hs

theorem canonicalDensity_endpoint_nonneg (f : ℝ → ℝ)
    (hf0 : 0 ≤ f 0) (hf1 : 0 ≤ f 1) {c : ℝ} (hc : c ∈ Icc 0 1) :
    0 ≤ canonicalDensity f c 1 := by
  simp only [canonicalDensity, sub_self, zero_mul, mul_one, add_sub_cancel]
  exact add_nonneg (mul_nonneg hc.1 hf0) (mul_nonneg (sub_nonneg.mpr hc.2) hf1)

/-- The width-parameter integral is exactly the integral on the actual window. -/
theorem integral_canonicalDensity (f : ℝ → ℝ) (hf : Continuous f) (c r : ℝ) :
    (∫ w in 0..r, canonicalDensity f c w) =
      ∫ x in (1-r)*c..c+(1-c)*r, f x := by
  have hl := mul_integral_comp_mul_add (f := f) (a := 0) (b := r) (-c) c
  have hr := mul_integral_comp_mul_add (f := f) (a := 0) (b := r) (1-c) c
  have hel : (fun x : ℝ => f (-c*x+c)) = (fun x : ℝ => f ((1-x)*c)) := by
    funext x
    congr 1
    ring
  have her : (fun x : ℝ => f ((1-c)*x+c)) = (fun x : ℝ => f (c+(1-c)*x)) := by
    funext x
    congr 1
    ring
  rw [hel] at hl
  rw [her] at hr
  simp only [mul_zero, zero_add] at hl hr
  rw [show -c*r+c = (1-r)*c by ring] at hl
  rw [show (1-c)*r+c = c+(1-c)*r by ring] at hr
  have hleft : c*(∫ x in 0..r, f ((1-x)*c)) = ∫ x in (1-r)*c..c, f x := by
    calc
      c*(∫ x in 0..r, f ((1-x)*c)) = -(-c*(∫ x in 0..r, f ((1-x)*c))) := by ring
      _ = -(∫ x in c..(1-r)*c, f x) := by rw [hl]
      _ = ∫ x in (1-r)*c..c, f x := by rw [integral_symm c ((1-r)*c)]
  have hright : (1-c)*(∫ x in 0..r, f (c+(1-c)*x)) =
      ∫ x in c..c+(1-c)*r, f x := by
    exact hr
  unfold canonicalDensity
  rw [integral_add (μ := volume)
    ((show Continuous (fun x : ℝ => c*f ((1-x)*c)) by fun_prop).intervalIntegrable 0 r)
    ((show Continuous (fun x : ℝ => (1-c)*f (c+(1-c)*x)) by fun_prop).intervalIntegrable 0 r),
    integral_const_mul, integral_const_mul, hleft, hright]
  exact integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

theorem mass_canonicalDensity (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ) :
    mass (canonicalDensity f c) = mass f := by
  unfold mass
  rw [integral_canonicalDensity f hf c 1]
  simp

/-- Covered mass of a canonical window obeys the quadratic contraction estimate. -/
theorem canonical_window_scaling (f : ℝ → ℝ) (hf : Continuous f)
    (hfconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) f) (hf0 : 0 ≤ f 0) (hf1 : 0 ≤ f 1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (∫ x in (1-t*r)*c..c+(1-c)*(t*r), f x) ≤
      t^2*(∫ x in (1-r)*c..c+(1-c)*r, f x)+2*t*r*(1-t)*mass f := by
  have hs := excess_quadratic_scaling (canonicalDensity f c)
    (continuous_canonicalDensity f hf c) (concaveOn_canonicalDensity f hfconc hc)
    (canonicalDensity_endpoint_nonneg f hf0 hf1 hc) ht hr
  unfold excess at hs
  rw [mass_canonicalDensity f hf c, integral_canonicalDensity f hf c r,
    integral_canonicalDensity f hf c (t*r)] at hs
  nlinarith [hs]

/-- Assembly from covered-mass and overlap comparisons. The hypotheses here
are scalar inequalities; their planar geometric verification is external. -/
theorem union_gap_scaling {V t Q A₀ A₁ O₀ O₁ : ℝ}
    (hV : 0 ≤ V) (ht : t ∈ Icc 0 1) (hQ : Q ≤ 1)
    (hA : A₀ ≤ t^2*A₁+2*t*(1-t)*V*Q) (hO : t^2*O₁ ≤ O₀) :
    V*(1-t)^2+t^2*(V-A₁+O₁) ≤ V-A₀+O₀ := by
  have hz : 0 ≤ 2*t*(1-t)*V*(1-Q) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht.1)
      (sub_nonneg.mpr ht.2)) hV) (sub_nonneg.mpr hQ)
  nlinarith [hA, hO, hz]

end Plank.ConcaveDensity
