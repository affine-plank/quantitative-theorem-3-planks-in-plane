module
/- Linear payments for the zero-cut-anchor Euler remainder. -/
public import Plank.Proofs.Quant.CyclicPaidLossGeometry

@[expose] public section
noncomputable section

namespace Quant.CyclicEulerPayments

open CyclicVertexDescent CyclicWeightedThresholdGeometry CyclicThresholdCaps
  CyclicGapCancellation CyclicPairAreas CyclicExteriorAssembly CyclicExactGap
  CyclicPaidLossGeometry

/-- A weighted comparison passes to positive parts, including both zero hinges. -/
theorem weighted_positivePart_le (p q x y : ℝ) (hq : 0 ≤ q) (h : p*x ≤ q*y) :
    p*max 0 x ≤ q*max 0 y := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_left hx, mul_zero]
    exact mul_nonneg hq (le_max_left _ _)
  · rw [max_eq_right hx]
    exact h.trans (mul_le_mul_of_nonneg_left (le_max_right 0 y) hq)

/-- Two sources pay a refund with the displayed coefficient remainder.
`x` is its argument, `z` the vertex argument, and `y` the loss argument. -/
theorem vertex_payment_lower_bound (d s p q k V U R x y z : ℝ)
    (hd : 0 < d) (hs : 0 < s) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k)
    (hV : 0 ≤ V) (hU : 0 ≤ U) (hxz : x ≤ z) (hxy : q*x ≤ s*y) :
    (k*V/d+U/p-R)/(s*k)*max 0 x ≤
      V*max 0 z/(d*s)+U*max 0 y/(p*q*k)-R*max 0 x/(s*k) := by
  have hv := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (max_le_max (le_refl (0 : ℝ)) hxz) hV) (mul_pos hd hs).le
  have hxy' := weighted_positivePart_le q s x y hs.le hxy
  have hy : q*max 0 x/s ≤ max 0 y := (div_le_iff₀ hs).mpr (by
    simpa only [mul_comm] using hxy')
  have hu := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy hU)
    (mul_pos (mul_pos hp hq) hk).le
  calc
    _ = V*max 0 x/(d*s)+U*(q*max 0 x/s)/(p*q*k)-R*max 0 x/(s*k) := by
      field_simp [hd.ne', hs.ne', hp.ne', hq.ne', hk.ne']
    _ ≤ _ := by linarith only [hv, hu]

theorem vertex_payment_nonneg (d s p q k V U R x y z : ℝ)
    (hd : 0 < d) (hs : 0 < s) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k)
    (hV : 0 ≤ V) (hU : 0 ≤ U) (hxz : x ≤ z) (hxy : q*x ≤ s*y)
    (hpay : R ≤ k*V/d+U/p) :
    0 ≤ V*max 0 z/(d*s)+U*max 0 y/(p*q*k)-R*max 0 x/(s*k) := by
  apply le_trans _ (vertex_payment_lower_bound d s p q k V U R x y z
    hd hs hp hq hk hV hU hxz hxy)
  exact mul_nonneg (div_nonneg (sub_nonneg.mpr hpay) (mul_pos hs hk).le)
    (le_max_left _ _)

theorem weight_cyclic_product (a b c : ℝ) (i : Fin 3) :
    weight a b c i*weight a b c (i+1)*weight a b c (i+2) =
      k0 b c*k1 a c*k2 a b := by
  fin_cases i
  · rfl
  · change k1 a c*k2 a b*k0 b c = _
    ring
  · change k2 a b*k0 b c*k1 a c = _
    ring

private theorem weighted_cap_lt (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : strictCompatible a b c t) (i : Fin 3) :
    weight a b c i*capSize a b c t i <
      direction a b c (i+1)*thresholdSlack a b c t := by
  have hj := ht (i+1)
  have hmod : i+1+1 = i+2 := by fin_cases i <;> rfl
  rw [hmod] at hj
  have hm := mul_pos (weight_pos ha hb hc (i+2)) hj
  have he := capSize_weighted_identity a b c t i
  linarith only [hm, he]

private theorem weighted_lowerCap_lt (a b c : ℝ) (t : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (ht : strictCompatible a b c t) (i : Fin 3) :
    weight a b c (i+1)*lowerCapSize a b c t i <
      (1-direction a b c i)*(-thresholdSlack a b c t) := by
  have hj := ht (i+2)
  have hmod : i+2+1 = i := by fin_cases i <;> rfl
  rw [hmod] at hj
  have hm := mul_pos (weight_pos ha hb hc (i+2)) hj
  have he := lowerCapSize_weighted_identity a b c t i
  linarith only [hm, he]

/-- Strict endpoint compatibility gives all four weighted refund comparisons.
The refund order is `(b1,b2,c1,c2)`. -/
theorem refund_weighted_bounds (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) :
    weight a b c i*refundArgument a b c l h i 0 < direction a b c (i+1)*
      (weight a b c i*windowWidth l h i+thresholdSlack a b c h) ∧
    weight a b c i*refundArgument a b c l h i 1 < direction a b c (i+1)*
      (weight a b c (i+1)*windowWidth l h (i+1)+thresholdSlack a b c h) ∧
    weight a b c (i+1)*refundArgument a b c l h i 2 < (1-direction a b c i)*
      (weight a b c (i+1)*windowWidth l h (i+1)-thresholdSlack a b c l) ∧
    weight a b c (i+1)*refundArgument a b c l h i 3 < (1-direction a b c i)*
      (weight a b c i*windowWidth l h i-thresholdSlack a b c l) := by
  have hmod0 : i+1+2 = i := by fin_cases i <;> rfl
  have hmod1 : i+2+2 = i+1 := by fin_cases i <;> rfl
  have hupper (j : Fin 3) : strictCompatible a b c (upperCorrectionLevels l h j) :=
    strictCompatible_of_endpoint_bounds a b c l h _ ha hb hc hend
      (upperCorrectionLevels_between l h hlh j)
  have hlower (j : Fin 3) : strictCompatible a b c (lowerCorrectionLevels l h j) :=
    strictCompatible_of_endpoint_bounds a b c l h _ ha hb hc hend
      (lowerCorrectionLevels_between l h hlh j)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [refundArgument_zero_eq_cap]
    have hh := weighted_cap_lt a b c _ ha hb hc (hupper (i+1)) i
    rw [thresholdSlack_upperCorrection, hmod0] at hh
    linarith only [hh]
  · rw [refundArgument_one_eq_cap]
    have hh := weighted_cap_lt a b c _ ha hb hc (hupper (i+2)) i
    rw [thresholdSlack_upperCorrection, hmod1] at hh
    linarith only [hh]
  · rw [refundArgument_two_eq_lowerCap]
    have hh := weighted_lowerCap_lt a b c _ ha hb hc (hlower (i+2)) i
    rw [thresholdSlack_lowerCorrection, hmod1] at hh
    linarith only [hh]
  · rw [refundArgument_three_eq_lowerCap]
    have hh := weighted_lowerCap_lt a b c _ ha hb hc (hlower (i+1)) i
    rw [thresholdSlack_lowerCorrection, hmod0] at hh
    linarith only [hh]

theorem refund_positivePart_bounds (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) :
    weight a b c i*max 0 (refundArgument a b c l h i 0) ≤ direction a b c (i+1)*
      max 0 (weight a b c i*windowWidth l h i+thresholdSlack a b c h) ∧
    weight a b c i*max 0 (refundArgument a b c l h i 1) ≤ direction a b c (i+1)*
      max 0 (weight a b c (i+1)*windowWidth l h (i+1)+thresholdSlack a b c h) ∧
    weight a b c (i+1)*max 0 (refundArgument a b c l h i 2) ≤ (1-direction a b c i)*
      max 0 (weight a b c (i+1)*windowWidth l h (i+1)-thresholdSlack a b c l) ∧
    weight a b c (i+1)*max 0 (refundArgument a b c l h i 3) ≤ (1-direction a b c i)*
      max 0 (weight a b c i*windowWidth l h i-thresholdSlack a b c l) := by
  obtain ⟨h0, h1, h2, h3⟩ := refund_weighted_bounds a b c l h ha hb hc hlh hend i
  have hd := (direction_bounds ha hb hc (i+1)).1.le
  have he := sub_nonneg.mpr (direction_bounds ha hb hc i).2.le
  exact ⟨weighted_positivePart_le _ _ _ _ hd h0.le,
    weighted_positivePart_le _ _ _ _ hd h1.le,
    weighted_positivePart_le _ _ _ _ he h2.le,
    weighted_positivePart_le _ _ _ _ he h3.le⟩

theorem refund_two_le_lower_vertex (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (i : Fin 3) (hh : h (i+1) ≤ 1) :
    refundArgument a b c l h i 2 ≤ l i-direction a b c i := by
  have hmul := mul_nonneg (sub_nonneg.mpr (direction_bounds ha hb hc i).2.le)
    (sub_nonneg.mpr hh)
  change -(-(h i+(1-direction a b c i)*h (i+1)-1))-(h i-l i) ≤ _
  nlinarith only [hmul]

theorem refund_zero_le_upper_vertex (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (i : Fin 3) (hl : 0 ≤ l i) :
    refundArgument a b c l h i 0 ≤ direction a b c (i+1)-h (i+1) := by
  have hmul := mul_nonneg (direction_bounds ha hb hc (i+1)).1.le hl
  simp only [refundArgument,lowPairSlack,capSize,windowWidth,Matrix.cons_val_zero]
  nlinarith only [hmul]

/-- Positive coherent box: the beta loss at `i+1` pays the `b2` refund at `i`.
At the zero-cut anchor, its loss coefficient is `κ_(i+1)*d_(i+1)*R_i`. -/
theorem positive_beta_payment_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ (weight a b c (i+1)*direction a b c (i+1)*R)*
      max 0 (weight a b c (i+1)*windowWidth l h (i+1)+thresholdSlack a b c h)/
        (k0 b c*k1 a c*k2 a b)-
      direction a b c (i+1)*R*max 0 (refundArgument a b c l h i 1)/
        (direction a b c (i+1)*weight a b c (i+2)) := by
  have hh := (refund_positivePart_bounds a b c l h ha hb hc hlh hend i).2.1
  have hi := weight_pos ha hb hc i
  have hj := weight_pos ha hb hc (i+1)
  have hk := weight_pos ha hb hc (i+2)
  have hd := (direction_bounds ha hb hc (i+1)).1
  have hn := div_nonneg (mul_nonneg hR (sub_nonneg.mpr hh)) (mul_pos hi hk).le
  rw [← weight_cyclic_product a b c i]
  convert hn using 1 <;> first | rfl | field_simp [hi.ne', hj.ne', hk.ne', hd.ne']

/-- Negative coherent box: the alpha loss at `i` pays the `c2` refund at `i`.
At the zero-cut anchor, its loss coefficient is `κ_i*(1-d_i)*R_(i+1)`. -/
theorem negative_alpha_payment_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ (weight a b c i*(1-direction a b c i)*R)*
      max 0 (weight a b c i*windowWidth l h i-thresholdSlack a b c l)/
        (k0 b c*k1 a c*k2 a b)-
      (1-direction a b c i)*R*max 0 (refundArgument a b c l h i 3)/
        ((1-direction a b c i)*weight a b c (i+2)) := by
  have hh := (refund_positivePart_bounds a b c l h ha hb hc hlh hend i).2.2.2
  have hi := weight_pos ha hb hc i
  have hj := weight_pos ha hb hc (i+1)
  have hk := weight_pos ha hb hc (i+2)
  have hd := sub_pos.mpr (direction_bounds ha hb hc i).2
  have hn := div_nonneg (mul_nonneg hR (sub_nonneg.mpr hh)) (mul_pos hj hk).le
  rw [← weight_cyclic_product a b c i]
  convert hn using 1 <;> first | rfl | field_simp [hi.ne', hj.ne', hk.ne', hd.ne']

/-- Positive coherent box: lower vertex `i` and alpha loss `i+1` pay `c1_i`.
The exact anchor identity supplies `hpay`; no middle-window condition is used. -/
theorem positive_vertex_payment_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) (hh : h (i+1) ≤ 1)
    (V U R : ℝ) (hV : 0 ≤ V) (hU : 0 ≤ U)
    (hpay : R ≤ weight a b c (i+2)*V/direction a b c i+U/weight a b c i) :
    0 ≤ V*max 0 (l i-direction a b c i)/(direction a b c i*(1-direction a b c i))+
      U*max 0 (weight a b c (i+1)*windowWidth l h (i+1)-thresholdSlack a b c l)/
        (k0 b c*k1 a c*k2 a b)-
      R*max 0 (refundArgument a b c l h i 2)/
        ((1-direction a b c i)*weight a b c (i+2)) := by
  have hn := vertex_payment_nonneg (direction a b c i) (1-direction a b c i)
    (weight a b c i) (weight a b c (i+1)) (weight a b c (i+2)) V U R
    (refundArgument a b c l h i 2)
    (weight a b c (i+1)*windowWidth l h (i+1)-thresholdSlack a b c l)
    (l i-direction a b c i) (direction_bounds ha hb hc i).1
    (sub_pos.mpr (direction_bounds ha hb hc i).2)
    (weight_pos ha hb hc i) (weight_pos ha hb hc (i+1)) (weight_pos ha hb hc (i+2))
    hV hU (refund_two_le_lower_vertex a b c l h ha hb hc i hh)
    (refund_weighted_bounds a b c l h ha hb hc hlh hend i).2.2.1.le hpay
  simpa only [weight_cyclic_product] using hn

/-- Negative coherent box: upper vertex `i+1` and beta loss `i` pay `b1_i`.
The exact anchor identity supplies `hpay`; no middle-window condition is used. -/
theorem negative_vertex_payment_nonneg (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hlh : ∀ i, l i ≤ h i)
    (hend : ∀ i, 0 < (1-direction a b c (i+1))*l i-direction a b c i*h (i+1)+
      direction a b c i*direction a b c (i+1)) (i : Fin 3) (hl : 0 ≤ l i)
    (W V R : ℝ) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hpay : R ≤ weight a b c (i+2)*W/(1-direction a b c (i+1))+
      V/weight a b c (i+1)) :
    0 ≤ W*max 0 (direction a b c (i+1)-h (i+1))/
        (direction a b c (i+1)*(1-direction a b c (i+1)))+
      V*max 0 (weight a b c i*windowWidth l h i+thresholdSlack a b c h)/
        (k0 b c*k1 a c*k2 a b)-
      R*max 0 (refundArgument a b c l h i 0)/
        (direction a b c (i+1)*weight a b c (i+2)) := by
  have hn := vertex_payment_nonneg (1-direction a b c (i+1)) (direction a b c (i+1))
    (weight a b c (i+1)) (weight a b c i) (weight a b c (i+2)) W V R
    (refundArgument a b c l h i 0)
    (weight a b c i*windowWidth l h i+thresholdSlack a b c h)
    (direction a b c (i+1)-h (i+1)) (sub_pos.mpr (direction_bounds ha hb hc (i+1)).2)
    (direction_bounds ha hb hc (i+1)).1
    (weight_pos ha hb hc (i+1)) (weight_pos ha hb hc i) (weight_pos ha hb hc (i+2))
    hW hV (refund_zero_le_upper_vertex a b c l h ha hb hc i hl)
    (refund_weighted_bounds a b c l h ha hb hc hlh hend i).1.le hpay
  have hprod : weight a b c (i+1)*weight a b c i*weight a b c (i+2) =
      k0 b c*k1 a c*k2 a b := by
    rw [mul_comm (weight a b c (i+1)) (weight a b c i), weight_cyclic_product]
  simpa only [hprod, mul_comm (1-direction a b c (i+1)) (direction a b c (i+1))] using hn


end Quant.CyclicEulerPayments
