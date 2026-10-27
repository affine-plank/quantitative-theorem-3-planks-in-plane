/- The complete one-plank bound from the common window contraction inequality. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalOnePlankCaps

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalInductionBoundary FiniteDimensionalParameterDomain
  FiniteDimensionalNormalization

variable {d : ℕ}

/-- Window contraction at full expanded width proves the one-plank inequality,
including zero width. The unit-width case has zero target. -/
theorem unitDomainBound_one : FiniteDimensionalNormalization.UnitDomainBound d 1 := by
  intro K hK hc hne f hunit hnorm p hp
  have hbudget : budget K f p = p.2 0-p.1 0 := by
    simp only [budget, hunit, div_one, Fin.sum_univ_one]
  have hr0 : 0 ≤ p.2 0-p.1 0 := sub_nonneg.mpr (hp.1 0).2.1
  have hr1 : p.2 0-p.1 0 ≤ 1 := by rw [← hbudget]; exact hp.2
  rw [hbudget]
  by_cases heq : p.2 0-p.1 0 = 1
  · simp only [heq, sub_self, max_self, zero_pow (Nat.succ_ne_zero d), zero_mul]
    exact ENNReal.toReal_nonneg
  have hlt : p.2 0-p.1 0 < 1 := lt_of_le_of_ne hr1 heq
  let r := p.2 0-p.1 0
  let c := p.1 0/(1-r)
  obtain ⟨hc0,hlo,hhi⟩ : c ∈ Icc (0 : ℝ) 1 ∧
      (1-r)*c=p.1 0 ∧ c+(1-c)*r=p.2 0 :=
    canonical_window (hp.1 0).1 (hp.1 0).2.2 hlt
  obtain ⟨hzero,hone⟩ := unit_realisers hK hne (f 0) (hnorm 0) (hunit 0)
  have hf : (f 0).linear ≠ 0 := linear_ne_zero_of_width_pos hne (f 0)
    (by rw [hunit]; norm_num)
  have hfull : K ∩ {x | (1-(1 : ℝ))*c ≤ f 0 x ∧ f 0 x ≤ c+(1-c)*1} = K := by
    apply inter_eq_left.mpr
    intro x hx
    simpa only [mem_ofPred_eq, sub_self, zero_mul, mul_one, add_sub_cancel] using hnorm 0 x hx
  have h := window_contraction hK hc (f 0) hf hzero hone hc0
    (show r ∈ Icc 0 1 from ⟨hr0, hr1⟩) (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  rw [hfull] at h
  simp only [mul_one, sub_self, zero_pow (Nat.succ_ne_zero d), sub_zero] at h
  have hunion : (⋃ i : Fin 1, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) =
      {x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} := by
    ext x
    simp only [mem_iUnion, mem_ofPred_eq, Fin.exists_fin_one]
  have hgap := measureReal_sdiff_add_inter (μ := volume) (s := K)
    (t := {x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0})
    ((isClosed_le continuous_const (continuous_form (f 0))).inter
      (isClosed_le (continuous_form (f 0)) continuous_const)).measurableSet hK.measure_ne_top
  simp only [measureReal_def] at hgap
  simp only [hlo, hhi] at h
  rw [max_eq_right (sub_nonneg.mpr hr1), gapVolume, hunion]
  nlinarith only [h, hgap]

/-- Normalization and clipping include arbitrary ordered windows and all
compact convex bodies, without using the translation proof of one plank. -/
theorem sharpBound_one : SharpBound d 1 :=
  (FiniteDimensionalNormalization.sharpBound_iff_unitDomainBound 1).mpr unitDomainBound_one

end Plank.FiniteDimensionalOnePlankCaps

#print axioms Plank.FiniteDimensionalOnePlankCaps.unitDomainBound_one
#print axioms Plank.FiniteDimensionalOnePlankCaps.sharpBound_one
