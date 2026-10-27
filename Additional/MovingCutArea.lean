/- Actual endpoint derivatives from product-measure sections. The transverse
measure space is arbitrary; only continuity at the moving cut is required. -/
module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.MovingCutArea

open Set MeasureTheory
open scoped Topology

variable {β : Type*} [MeasurableSpace β] (ν : Measure β) [SFinite ν]

def density (S : Set (ℝ × β)) (t : ℝ) : ℝ := ν.real (Prod.mk t ⁻¹' S)
def window (S : Set (ℝ × β)) (a b : ℝ) : Set (ℝ × β) := S ∩ (Icc a b ×ˢ univ)
def windowArea (S : Set (ℝ × β)) (a b : ℝ) : ℝ := (volume.prod ν).real (window S a b)
def gapArea (S : Set (ℝ × β)) (a b : ℝ) : ℝ :=
  (volume.prod ν).real (S \ (Icc a b ×ˢ univ))

theorem measurable_density {S : Set (ℝ × β)} (hS : MeasurableSet S) :
    Measurable (density ν S) := (measurable_measure_prodMk_left (ν := ν) hS).ennreal_toReal

theorem integrable_density {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) : Integrable (density ν S) :=
  Measure.integrable_measure_prodMk_left hS hfinite

theorem area_eq_integral {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) :
    (volume.prod ν).real S=∫ t : ℝ, density ν S t := by
  symm
  rw [show (fun t => density ν S t)=(fun t => (ν (Prod.mk t ⁻¹' S)).toReal) from rfl,
    integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
      (Measure.ae_measure_lt_top hS hfinite),← Measure.prod_apply hS]
  rfl

omit [SFinite ν] in
theorem density_window (S : Set (ℝ × β)) (a b t : ℝ) :
    density ν (window S a b) t=(Icc a b).indicator (density ν S) t := by
  by_cases ht : t ∈ Icc a b
  · have he : Prod.mk t ⁻¹' window S a b=Prod.mk t ⁻¹' S := by
      ext y
      simp [window,ht]
    rw [density,he,indicator_of_mem ht]
    rfl
  · have he : Prod.mk t ⁻¹' window S a b=∅ := by
      ext y
      simp [window,ht]
    simp [density,he,ht]

theorem windowArea_eq_integral {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a ≤ b) :
    windowArea ν S a b=∫ t in a..b, density ν S t := by
  have hm : MeasurableSet (window S a b) := hS.inter (measurableSet_Icc.prod MeasurableSet.univ)
  have hf : (volume.prod ν) (window S a b) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_left hfinite
  rw [windowArea,area_eq_integral ν hm hf]
  simp_rw [density_window]
  rw [integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]

omit [SFinite ν] in
theorem gapArea_eq (S : Set (ℝ × β)) (hfinite : (volume.prod ν) S ≠ ⊤) (a b : ℝ) :
    gapArea ν S a b=(volume.prod ν).real S-windowArea ν S a b := by
  have h := measureReal_inter_add_sdiff (μ := volume.prod ν) (s := S) (t := Icc a b ×ˢ (univ : Set β))
    (measurableSet_Icc.prod MeasurableSet.univ) hfinite
  exact eq_sub_of_add_eq' h

theorem hasDerivAt_windowArea_upper {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hc : ContinuousAt (density ν S) b) :
    HasDerivAt (windowArea ν S a) (density ν S b) b := by
  apply (intervalIntegral.integral_hasDerivAt_right
    (integrable_density ν hS hfinite).intervalIntegrable
    (measurable_density ν hS).stronglyMeasurable.stronglyMeasurableAtFilter hc).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hab] with t ht
  exact windowArea_eq_integral ν hS hfinite ht.le

theorem hasDerivAt_windowArea_lower {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hc : ContinuousAt (density ν S) a) :
    HasDerivAt (fun t => windowArea ν S t b) (-density ν S a) a := by
  apply (intervalIntegral.integral_hasDerivAt_left
    (integrable_density ν hS hfinite).intervalIntegrable
    (measurable_density ν hS).stronglyMeasurable.stronglyMeasurableAtFilter hc).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hab] with t ht
  exact windowArea_eq_integral ν hS hfinite ht.le

theorem hasDerivAt_gapArea_lower {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hc : ContinuousAt (density ν S) a) :
    HasDerivAt (fun t => gapArea ν S t b) (density ν S a) a := by
  have h := (hasDerivAt_const a ((volume.prod ν).real S)).sub
    (hasDerivAt_windowArea_lower ν hS hfinite hab hc)
  simp only [sub_neg_eq_add,zero_add] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (gapArea_eq ν S hfinite · b))

theorem hasDerivAt_gapArea_upper {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hc : ContinuousAt (density ν S) b) :
    HasDerivAt (gapArea ν S a) (-density ν S b) b := by
  have h := (hasDerivAt_const b ((volume.prod ν).real S)).sub
    (hasDerivAt_windowArea_upper ν hS hfinite hab hc)
  simp only [zero_sub] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall (gapArea_eq ν S hfinite a))

/-- A local minimum forces the measured section equation for any natural
power. Both the transverse measure and the directional width are explicit. -/
theorem stationary_lower_power {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hc : ContinuousAt (density ν S) a) (n : ℕ) (V δ w : ℝ) (hw : w ≠ 0)
    (hmin : IsLocalMin (fun t => gapArea ν S t b-V*(δ+(t-a)/w)^n) a) :
    density ν S a*w=(n:ℝ)*V*δ^(n-1) := by
  have hd : HasDerivAt (fun t : ℝ => δ+(t-a)/w) (1/w) a :=
    (((hasDerivAt_id a).sub_const a).div_const w).const_add δ
  have hz := hmin.hasDerivAt_eq_zero
    ((hasDerivAt_gapArea_lower ν hS hfinite hab hc).sub ((hd.pow n).const_mul V))
  simp only [sub_self,zero_div,add_zero] at hz
  field_simp [hw] at hz
  nlinarith only [hz]

theorem stationary_upper_power {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hc : ContinuousAt (density ν S) b) (n : ℕ) (V δ w : ℝ) (hw : w ≠ 0)
    (hmin : IsLocalMin (fun t => gapArea ν S a t-V*(δ-(t-b)/w)^n) b) :
    density ν S b*w=(n:ℝ)*V*δ^(n-1) := by
  have hd : HasDerivAt (fun t : ℝ => δ-(t-b)/w) (0-1/w) b :=
    (hasDerivAt_const b δ).sub (((hasDerivAt_id b).sub_const b).div_const w)
  have hz := hmin.hasDerivAt_eq_zero
    ((hasDerivAt_gapArea_upper ν hS hfinite hab hc).sub ((hd.pow n).const_mul V))
  simp only [sub_self,zero_div,sub_zero] at hz
  field_simp [hw] at hz
  nlinarith only [hz]

theorem stationary_lower {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hc : ContinuousAt (density ν S) a) (V δ w : ℝ) (hw : w ≠ 0)
    (hmin : IsLocalMin (fun t => gapArea ν S t b-V*(δ+(t-a)/w)^2) a) :
    density ν S a*w=2*V*δ := by
  simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using
    stationary_lower_power ν hS hfinite hab hc 2 V δ w hw hmin

theorem stationary_upper {S : Set (ℝ × β)} (hS : MeasurableSet S)
    (hfinite : (volume.prod ν) S ≠ ⊤) {a b : ℝ} (hab : a < b)
    (hc : ContinuousAt (density ν S) b) (V δ w : ℝ) (hw : w ≠ 0)
    (hmin : IsLocalMin (fun t => gapArea ν S a t-V*(δ-(t-b)/w)^2) b) :
    density ν S b*w=2*V*δ := by
  simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using
    stationary_upper_power ν hS hfinite hab hc 2 V δ w hw hmin

end Plank.MovingCutArea

#print axioms Plank.MovingCutArea.hasDerivAt_gapArea_lower
#print axioms Plank.MovingCutArea.hasDerivAt_gapArea_upper
#print axioms Plank.MovingCutArea.stationary_lower_power
#print axioms Plank.MovingCutArea.stationary_upper_power
#print axioms Plank.MovingCutArea.stationary_lower
#print axioms Plank.MovingCutArea.stationary_upper
