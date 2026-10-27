/- Merge two intervals under a continuous unimodal density without losing mass. -/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.UnimodalIntervalMerge
open Set MeasureTheory

/-- One of the two gap-closing translations increases the density at every
point of the interval that moves. Flat parts and zero interval lengths are allowed. -/
theorem pointwise {f : ℝ → ℝ} {m a b c d : ℝ}
    (hin : MonotoneOn f (Iic m)) (hout : AntitoneOn f (Ici m))
    (hbc : b ≤ c) :
    (∀ x ∈ Icc a b, f x ≤ f (x+(c-b))) ∨
      (∀ x ∈ Icc c d, f x ≤ f (x+(b-c))) := by
  by_cases hcm : c ≤ m
  · left
    intro x hx
    exact hin (hx.2.trans (hbc.trans hcm)) (by change x+(c-b) ≤ m; linarith only [hx.2,hcm])
      (by linarith only [hbc])
  by_cases hmb : m ≤ b
  · right
    intro x hx
    exact hout (by change m ≤ x+(b-c); linarith only [hx.1,hmb]) ((hmb.trans hbc).trans hx.1)
      (by linarith only [hbc])
  have hbm : b ≤ m := (lt_of_not_ge hmb).le
  have hmc : m ≤ c := (lt_of_not_ge hcm).le
  rcases le_total (f b) (f c) with hfc | hfc
  · left
    intro x hx
    by_cases hxm : x+(c-b) ≤ m
    · exact hin (hx.2.trans hbm) hxm (by linarith only [hbc])
    · calc
        f x ≤ f b := hin (hx.2.trans hbm) hbm hx.2
        _ ≤ f c := hfc
        _ ≤ f (x+(c-b)) := hout (le_of_not_ge hxm) hmc (by linarith only [hx.2])
  · right
    intro x hx
    by_cases hmx : m ≤ x+(b-c)
    · exact hout hmx (hmc.trans hx.1) (by linarith only [hbc])
    · calc
        f x ≤ f c := hout hmc (hmc.trans hx.1) hx.1
        _ ≤ f b := hfc
        _ ≤ f (x+(b-c)) := hin hbm (le_of_not_ge hmx) (by linarith only [hx.1])

/-- Two disjoint ordered intervals can be replaced by one interval of
exactly the same total length, inside their convex hull, with at least as
much density mass. No concavity or nonnegativity of the density is needed. -/
theorem exists_interval {f : ℝ → ℝ} (hf : Continuous f) {m a b c d : ℝ}
    (hin : MonotoneOn f (Iic m)) (hout : AntitoneOn f (Ici m))
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ∃ l u : ℝ, a ≤ l ∧ u ≤ d ∧ l ≤ u ∧ u-l = (b-a)+(d-c) ∧
      (∫ x in a..b, f x)+(∫ x in c..d, f x) ≤ ∫ x in l..u, f x := by
  rcases pointwise (a := a) (d := d) hin hout hbc with hl | hr
  · have hc : Continuous (fun x => f (x+(c-b))) := hf.comp (by fun_prop)
    have hm := intervalIntegral.integral_mono_on (μ := volume) hab (hf.intervalIntegrable a b)
      (hc.intervalIntegrable a b) hl
    rw [intervalIntegral.integral_comp_add_right] at hm
    have hb : b+(c-b) = c := by ring
    rw [hb] at hm
    refine ⟨a+(c-b),d,by linarith only [hbc],le_rfl,
      by linarith only [hab,hcd],by ring,?_⟩
    calc
      _ ≤ (∫ x in a+(c-b)..c, f x)+(∫ x in c..d, f x) := by linarith only [hm]
      _ = _ := intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  · have hc : Continuous (fun x => f (x+(b-c))) := hf.comp (by fun_prop)
    have hm := intervalIntegral.integral_mono_on (μ := volume) hcd (hf.intervalIntegrable c d)
      (hc.intervalIntegrable c d) hr
    rw [intervalIntegral.integral_comp_add_right] at hm
    have hb : c+(b-c) = b := by ring
    rw [hb] at hm
    refine ⟨a,d+(b-c),le_rfl,by linarith only [hbc],
      by linarith only [hab,hcd],by ring,?_⟩
    calc
      _ ≤ (∫ x in a..b, f x)+(∫ x in b..d+(b-c), f x) := by linarith only [hm]
      _ = _ := intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

end Quant.UnimodalIntervalMerge

/-- info: 'Quant.UnimodalIntervalMerge.exists_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.UnimodalIntervalMerge.exists_interval
