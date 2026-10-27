/- Finite canonical-window scaling from Brunn--Minkowski on the two caps. -/
module

public import Plank.Proofs.Quant.PlanarStatement
public import Plank.Proofs.Quant.FiniteDimensionalCapWindowCore
public import Plank.Proofs.Quant.FiniteDimensionalCapWindowScaling
public import Mathlib.MeasureTheory.Measure.Real

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCapWindowScaling

open Set MeasureTheory PlanarQuantitative
open FiniteDimensionalCapWindowScaling (continuous_form)
open scoped Pointwise

def cap (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) (u : ℝ) : Set Point :=
  K ∩ {x | f x ≤ u}

theorem compact_cap {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (u : ℝ) : IsCompact (cap K f u) :=
  hK.inter_right (isClosed_le (continuous_form f) continuous_const)

/-- The actual cap roots obey the weighted Brunn--Minkowski inequality. -/
theorem sqrt_cap_mix {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) {u v a b : ℝ}
    (hu : (cap K f u).Nonempty) (hv : (cap K f v).Nonempty)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*Real.sqrt (volume (cap K f u)).toReal+
      b*Real.sqrt (volume (cap K f v)).toReal ≤
      Real.sqrt (volume (cap K f (a*u+b*v))).toReal := by
  have h := FiniteDimensionalCapWindowScaling.root_cap_mix (d := 1) hK hc f hu hv ha hb hab
  simpa [cap, FiniteDimensionalCapWindowScaling.cap, FiniteDimensionalCapWindowScaling.volumeRoot,
    Real.sqrt_eq_rpow] using h

/-- A support point supplies the root-area lower bound for a contracted cap. -/
theorem sqrt_cap_contract {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) (hzero : ∃ x ∈ K, f x=0)
    {c r : ℝ} (hc0 : 0 ≤ c) (hr : r ∈ Icc 0 1) :
    (1-r)*Real.sqrt (volume (cap K f c)).toReal ≤
      Real.sqrt (volume (cap K f ((1-r)*c))).toReal := by
  have h := FiniteDimensionalCapWindowScaling.root_cap_contract (d := 1) hK hc f hzero hc0 hr
  simpa [cap, FiniteDimensionalCapWindowScaling.cap, FiniteDimensionalCapWindowScaling.volumeRoot,
    Real.sqrt_eq_rpow] using h

/-- A finite cap inequality; no section density or derivative is needed. -/
theorem cap_contraction {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) (hzero : ∃ x ∈ K, f x=0)
    {c t r : ℝ} (hc0 : 0 ≤ c) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    t^2*(volume (cap K f ((1-r)*c))).toReal+
      (1-t^2-2*t*r*(1-t))*(volume (cap K f c)).toReal ≤
      (volume (cap K f ((1-t*r)*c))).toReal := by
  have h := FiniteDimensionalCapWindowScaling.cap_contraction (d := 1) hK hc f hzero hc0 ht hr
  change t^2*(volume (cap K f ((1-r)*c))).toReal+
    ((1-t*r)^2-t^2*(1-r)^2)*(volume (cap K f c)).toReal ≤
      (volume (cap K f ((1-t*r)*c))).toReal at h
  convert h using 1
  ring

def reflect (f : Point →ᵃ[ℝ] ℝ) : Point →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ Point 1-f

@[simp] theorem reflect_apply (f : Point →ᵃ[ℝ] ℝ) (x : Point) :
    reflect f x = 1-f x := rfl

/-- The two closed caps partition the body up to their null common level. -/
theorem cap_partition {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ) :
    (volume (cap K f c)).toReal+
      (volume (cap K (reflect f) (1-c))).toReal = (volume K).toReal := by
  exact FiniteDimensionalCapWindowScaling.cap_partition (d := 1) hK f hf c

/-- Deleting a window leaves precisely its two exterior caps in area. -/
theorem cap_window_partition {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) {lo hi : ℝ} (ho : lo ≤ hi) :
    (volume (cap K f lo)).toReal+
      (volume (cap K (reflect f) (1-hi))).toReal+
      (volume (K ∩ {x | lo ≤ f x ∧ f x ≤ hi})).toReal = (volume K).toReal := by
  exact FiniteDimensionalCapWindowScaling.cap_window_partition (d := 1) hK f hf ho

/-- Actual covered-area scaling follows directly from the two cap inequalities.
Both support points are explicit; neither a density nor stationarity is assumed. -/
theorem window_contraction {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (volume (K ∩ {x | (1-t*r)*c ≤ f x ∧ f x ≤ c+(1-c)*(t*r)})).toReal ≤
      t^2*(volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal+
        2*t*r*(1-t)*(volume K).toReal := by
  have h := FiniteDimensionalCapWindowScaling.window_contraction (d := 1)
    hK hconv f hf hzero hone hc ht hr
  norm_num only at h
  convert h using 1
  ring

/-- Retaining the actual one-window excess uses only linear cap contraction. -/
theorem window_contraction_with_excess {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (volume (K ∩ {x | (1-t*r)*c ≤ f x ∧ f x ≤ c+(1-c)*(t*r)})).toReal+
      (1-t)*(FiniteDimensionalCapWindowScaling.gap K f c (t*r)-
        (1-t*r)^2*(volume K).toReal) ≤
      t^2*(volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal+
        2*t*r*(1-t)*(volume K).toReal := by
  have h := FiniteDimensionalCapWindowScaling.gap_excess_contraction_linear (d := 1)
    hK hconv f hf hzero hone hc ht hr
  simp only [FiniteDimensionalCapWindowScaling.gap_eq_sub_window hK] at h ⊢
  have hm := mul_le_mul_of_nonneg_left h ht.1
  norm_num only at hm
  nlinarith only [hm]

end Plank.PlanarCapWindowScaling
