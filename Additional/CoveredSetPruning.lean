/- Removing only uncovered volume decreases the deficient-volume objective. -/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false

namespace Plank.CoveredSetPruning

open Set MeasureTheory

variable {E : Type*} [MeasurableSpace E]

/-- If the covered part stays fixed, uncovered volume changes by the whole volume loss. -/
theorem gap_difference (μ : Measure E) {K C U : Set E} (hK : μ K≠⊤)
    (hCK : C⊆K) (hU : MeasurableSet U) (hcovered : C∩U=K∩U) :
    μ.real (K\U)-μ.real (C\U)=μ.real K-μ.real C := by
  have hk := measureReal_inter_add_sdiff (μ := μ) (s := K) hU hK
  have hc := measureReal_inter_add_sdiff (μ := μ) (s := C) hU
    (measure_ne_top_of_subset hCK hK)
  rw [hcovered] at hc
  linarith only [hk,hc]

/-- Exact change in the objective, with an arbitrary volume coefficient. -/
theorem margin_identity (μ : Measure E) {K C U : Set E} (hK : μ K≠⊤)
    (hCK : C⊆K) (hU : MeasurableSet U) (hcovered : C∩U=K∩U) (q : ℝ) :
    μ.real (C\U)-q*μ.real C =
      (μ.real (K\U)-q*μ.real K)-(1-q)*(μ.real K-μ.real C) := by
  have h := gap_difference μ hK hCK hU hcovered
  nlinarith only [h]

/-- Pruning preserves every strict counterexample with coefficient at most one. -/
theorem bad_transfer (μ : Measure E) {K C U : Set E} (hK : μ K≠⊤)
    (hCK : C⊆K) (hU : MeasurableSet U) (hcovered : C∩U=K∩U)
    {q : ℝ} (hq : q≤1) (hbad : μ.real (K\U)<q*μ.real K) :
    μ.real (C\U)<q*μ.real C := by
  have hid := margin_identity μ hK hCK hU hcovered q
  have hvol := measureReal_mono hCK hK
  have hpay := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hvol)
  linarith only [hid,hpay,hbad]

/-- Positive discarded volume gives strict descent whenever the coefficient is below one. -/
theorem strict_descent (μ : Measure E) {K C U : Set E} (hK : μ K≠⊤)
    (hCK : C⊆K) (hU : MeasurableSet U) (hcovered : C∩U=K∩U)
    {q : ℝ} (hq : q<1) (hvol : μ.real C<μ.real K) :
    μ.real (C\U)-q*μ.real C < μ.real (K\U)-q*μ.real K := by
  rw [margin_identity μ hK hCK hU hcovered q]
  exact sub_lt_self _ (mul_pos (sub_pos.mpr hq) (sub_pos.mpr hvol))

end Plank.CoveredSetPruning

#print axioms Plank.CoveredSetPruning.gap_difference
#print axioms Plank.CoveredSetPruning.margin_identity
#print axioms Plank.CoveredSetPruning.bad_transfer
#print axioms Plank.CoveredSetPruning.strict_descent
