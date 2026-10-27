/- Positive row-C equality forces an axial pair of actual coordinate contacts. -/
module
public import Plank.Convex.RowCCapAlgebra
public import Plank.Convex.RowCCapTransfer
public import Plank.Convex.WeightedSumBounds
public import Mathlib.Tactic.LinearCombination
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.RowCStrictEquality
open RowCCapAlgebra

/-- The repeated row-C budgets make one weighted sum dominate all three coefficients. -/
theorem coefficients_le_total (w : Point) (b Q V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hb : 0 < b) (hQ : 0 ≤ Q) (hQV : Q * V ≤ 1)
    (h0 : 1 ≤ w 0 + (Q / b) * w 1 + (1 / b) * w 2)
    (h1 : 1 ≤ w 1 + V * w 2 + (b * V) * w 0)
    (h2 : 1 ≤ w 2 + b * w 0 + Q * w 1) :
    ∀ i, (![b, Q, 1] : Point) i ≤ ∑ j, w j * (![b, Q, 1] : Point) j := by
  have ht : ∑ j, w j * (![b, Q, 1] : Point) j = b * w 0 + Q * w 1 + w 2 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hbT : b ≤ b * w 0 + Q * w 1 + w 2 := by
    have hh := mul_le_mul_of_nonneg_left h0 hb.le
    have he : b * (w 0 + (Q / b) * w 1 + (1 / b) * w 2) =
        b * w 0 + Q * w 1 + w 2 := by field_simp
    simpa only [mul_one, he] using hh
  have hQT : Q ≤ b * w 0 + Q * w 1 + w 2 := by
    have hh := mul_le_mul_of_nonneg_left h1 hQ
    have hleft := mul_le_mul_of_nonneg_right hQV (mul_nonneg hb.le (hw 0))
    have hright := mul_le_mul_of_nonneg_right hQV (hw 2)
    nlinarith only [hh, hleft, hright]
  intro i
  rw [ht]
  fin_cases i
  · exact hbT
  · exact hQT
  · change 1 ≤ b * w 0 + Q * w 1 + w 2
    simpa only [add_comm, add_left_comm, add_assoc] using h2

/-- A direct width proof for row C, using only a weighted sum. -/
theorem width_bound (w : Point) (b Q V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hb : 0 < b) (hQ : 0 ≤ Q) (hQV : Q * V ≤ 1)
    (h0 : 1 ≤ w 0 + (Q / b) * w 1 + (1 / b) * w 2)
    (h1 : 1 ≤ w 1 + V * w 2 + (b * V) * w 0)
    (h2 : 1 ≤ w 2 + b * w 0 + Q * w 1) : 1 ≤ ∑ i, w i := by
  have ht := coefficients_le_total w b Q V hw hb hQ hQV h0 h1 h2
  exact WeightedSumBounds.one_le_sum w ![b, Q, 1] hw
    (zero_lt_one.trans_le (ht 2)) ht

/-- With positive widths and total one, every row-C transfer coefficient is one. -/
theorem coefficients_eq_one (w : Point) (b Q V : ℝ)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hb : 0 < b) (hQ : 0 ≤ Q) (hQV : Q * V ≤ 1)
    (h0 : 1 ≤ w 0 + (Q / b) * w 1 + (1 / b) * w 2)
    (h1 : 1 ≤ w 1 + V * w 2 + (b * V) * w 0)
    (h2 : 1 ≤ w 2 + b * w 0 + Q * w 1) : b = 1 ∧ Q = 1 ∧ V = 1 := by
  have he := WeightedSumBounds.coeff_eq_of_sum_one w ![b, Q, 1] (fun i => (hw i).le) hsum
    (coefficients_le_total w b Q V (fun i => (hw i).le) hb hQ hQV h0 h1 h2)
  have hb1 : b = 1 := (he 0 (hw 0)).trans (he 2 (hw 2)).symm
  have hQ1 : Q = 1 := (he 1 (hw 1)).trans (he 2 (hw 2)).symm
  have hV1 : V ≤ 1 := by simpa only [hQ1, one_mul] using hQV
  have hs : w 0 + w 1 + w 2 = 1 := by simpa only [Fin.sum_univ_three] using hsum
  rw [hb1, one_mul] at h1
  have hp : 0 < w 0 + w 2 := add_pos (hw 0) (hw 2)
  have hV : 1 ≤ V := by nlinarith only [h1, hs, hp]
  exact ⟨hb1, hQ1, le_antisymm hV1 hV⟩

/-- Adding the lower and upper contact estimates gives the three repeated budgets. -/
theorem budgets_of_numeric_rows (lo hi : Point) (a0 a1 b c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrows : NumericRows lo hi a0 a1 b c d) :
    let w := fun i => hi i - lo i
    let Q := RowCCapTransfer.q a0 a1 b c d
    let V := RowCCapTransfer.v a0 a1 b c d
    (1 ≤ w 0 + (Q / b) * w 1 + (1 / b) * w 2) ∧
    (1 ≤ w 1 + V * w 2 + (b * V) * w 0) ∧
    (1 ≤ w 2 + b * w 0 + Q * w 1) := by
  obtain ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩ := hrows
  have hac : 0 < a0 + c := by positivity
  have had : 0 < 1 + a1 * d := by positivity
  have hdc : 0 < d + b * c := by positivity
  have hdu : 0 < 1 + a0 * a1 * b := by positivity
  have hl0' : lo 0 ≤ ((1 + a1 * d) * (hi 2 - lo 2) + d * (hi 1 - lo 1)) /
      (b * (1 + a1 * d)) :=
    (le_div_iff₀ (mul_pos hb had)).mpr (by simpa only [mul_assoc] using hl0)
  have hu0' := (le_div_iff₀ hac).mpr hu0
  have hl1' := (le_div_iff₀ hdc).mpr hl1
  have hu1' := (le_div_iff₀ hdu).mpr hu1
  have hl2' := (le_div_iff₀ hac).mpr hl2
  have hu2' := (le_div_iff₀ had).mpr hu2
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · have h := add_le_add_left (add_le_add hl0' hu0') (hi 0 - lo 0)
    unfold RowCCapTransfer.q
    convert h using 1 <;> field_simp [ne_of_gt hb, ne_of_gt hac, ne_of_gt had] <;> ring
  · have h := add_le_add_left (add_le_add hl1' hu1') (hi 1 - lo 1)
    unfold RowCCapTransfer.v
    convert h using 1 <;> ring
  · have h := add_le_add_left (add_le_add hl2' hu2') (hi 2 - lo 2)
    unfold RowCCapTransfer.q
    convert h using 1 <;> field_simp [ne_of_gt hac, ne_of_gt had] <;> ring

/-- Positive equality saturates the two middle-coordinate contact estimates. -/
theorem saturation_of_numeric_rows (lo hi : Point) (a0 a1 b c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hrows : NumericRows lo hi a0 a1 b c d)
    (hw : ∀ i, 0 < hi i - lo i) (hsum : ∑ i, (hi i - lo i) = 1) :
    b = 1 ∧ c = a0 * a1 * d ∧
      lo 1 * (d + c) = (hi 0 - lo 0) + (hi 2 - lo 2) ∧
      1 - hi 1 = a1 * d * lo 1 := by
  obtain ⟨h0, h1, h2⟩ := budgets_of_numeric_rows lo hi a0 a1 b c d ha0 ha1 hb hc hd hrows
  have hQ : 0 ≤ RowCCapTransfer.q a0 a1 b c d := by unfold RowCCapTransfer.q; positivity
  obtain ⟨hb1, hQ1, hV1⟩ := coefficients_eq_one (fun i => hi i - lo i) b
    (RowCCapTransfer.q a0 a1 b c d) (RowCCapTransfer.v a0 a1 b c d)
    hw hsum hb hQ (RowCCapTransfer.coefficient_bound a0 a1 b c d ha0 ha1 hb hc hd)
    h0 h1 h2
  have hgap := RowCCapTransfer.coefficient_gap a0 a1 b c d ha0 ha1 hb hc hd
  rw [hQ1, hV1, hb1] at hgap
  have hsq : (a0 * a1 * d - c) ^ 2 = 0 := by simpa using hgap.symm
  have hcEq : c = a0 * a1 * d := (sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)).symm
  obtain ⟨_, _, hl, hu, _, _⟩ := hrows
  rw [hb1, one_mul] at hl
  rw [hb1, mul_one, mul_one] at hu
  rw [RowCCapTransfer.v, hb1, one_mul, mul_one] at hV1
  have hdc : 0 < d + c := add_pos hd hc
  have hdu : 0 < 1 + a0 * a1 := by positivity
  let T := (hi 0 - lo 0) + (hi 2 - lo 2)
  have hl' : lo 1 ≤ T / (d + c) := by
    apply (le_div_iff₀ hdc).mpr
    dsimp only [T]
    linarith only [hl]
  have hu' : 1 - hi 1 ≤ a1 * T / (1 + a0 * a1) := by
    apply (le_div_iff₀ hdu).mpr
    dsimp only [T]
    nlinarith only [hu]
  have hparts : T / (d + c) + a1 * T / (1 + a0 * a1) = T := by
    calc
      _ = (1 / (d + c) + a1 / (1 + a0 * a1)) * T := by ring
      _ = T := by rw [hV1, one_mul]
  have hs : lo 1 + (1 - hi 1) = T := by
    simp only [Fin.sum_univ_three] at hsum
    dsimp only [T]
    linarith only [hsum]
  have hlEq : lo 1 * (d + c) = T :=
    (eq_div_iff hdc.ne').mp (by linarith only [hl', hu', hparts, hs])
  have huEq : (1 - hi 1) * (1 + a0 * a1) = a1 * T :=
    (eq_div_iff hdu.ne').mp (by linarith only [hl', hu', hparts, hs])
  have hmargin : 1 - hi 1 = a1 * d * lo 1 := by
    have hz : (1 + a0 * a1) * ((1 - hi 1) - a1 * d * lo 1) = 0 := by
      rw [hcEq] at hlEq
      linear_combination huEq - a1 * hlEq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hdu.ne')
  exact ⟨hb1, hcEq, hlEq, hmargin⟩

/-- Equality makes a lower and an upper middle-coordinate contact agree in the other coordinates. -/
theorem axial_contacts_of_equality (S : Set Point) (lo hi : Point) (a0 a1 b c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hS : Supports S lo hi a0 a1 b c d)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1)
    (hw : ∀ i, 0 < hi i - lo i) (hsum : ∑ i, (hi i - lo i) = 1) :
    ∃ L ∈ S, ∃ U ∈ S, L 1 = 0 ∧ U 1 = 1 ∧ L 0 = U 0 ∧ L 2 = U 2 := by
  obtain ⟨hb1, hcEq, hlEq, hmargin⟩ := saturation_of_numeric_rows lo hi a0 a1 b c d
    ha0 ha1 hb hc hd (numeric_rows_of_supports S lo hi a0 a1 b c d
      ha0 ha1 hb hc hd hS hL hU) hw hsum
  obtain ⟨L, hLS, hL1⟩ := hL 1
  obtain ⟨U, hUS, hU1⟩ := hU 1
  obtain ⟨_, _, hLb, hLc, hLd⟩ := hS L hLS
  obtain ⟨hUa0, hUa1, hUb, _, _⟩ := hS U hUS
  rw [hb1, one_mul, one_mul] at hLb hUb
  rw [hL1, mul_zero, sub_zero] at hLc hLd
  rw [hU1, mul_one] at hUa0
  rw [hU1] at hUa1
  have hconst : (hi 0 - c * lo 1) + (hi 2 - d * lo 1) = lo 0 + lo 2 := by
    nlinarith only [hlEq]
  have hLm0 : L 0 = hi 0 - c * lo 1 := by linarith only [hLc, hLd, hLb, hconst]
  have hLm2 : L 2 = hi 2 - d * lo 1 := by linarith only [hLc, hLd, hLb, hconst]
  have hshift : a0 * (1 - hi 1) = c * lo 1 := by
    rw [hmargin, hcEq]
    ring
  have hUc : U 0 ≤ hi 0 - c * lo 1 := by nlinarith only [hUa0, hshift]
  have hUd : U 2 ≤ hi 2 - d * lo 1 := by
    apply le_of_mul_le_mul_left (a := a1) _ ha1
    nlinarith only [hUa1, hmargin]
  have hUm0 : U 0 = hi 0 - c * lo 1 := by linarith only [hUc, hUd, hUb, hconst]
  have hUm2 : U 2 = hi 2 - d * lo 1 := by linarith only [hUc, hUd, hUb, hconst]
  exact ⟨L, hLS, U, hUS, hL1, hU1, hLm0.trans hUm0.symm, hLm2.trans hUm2.symm⟩

/-- Row-C equality is impossible on any plane whose middle coefficient is nonzero. -/
theorem ne_one_of_supports (S : Set Point) (lo hi : Point) (a0 a1 b c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hS : Supports S lo hi a0 a1 b c d)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1)
    (hw : ∀ i, 0 < hi i - lo i) (A : Point) (D : ℝ) (hA : A 1 ≠ 0)
    (hplane : ∀ x ∈ S, ∑ i, A i * x i = D) : (∑ i, (hi i - lo i)) ≠ 1 := by
  intro hsum
  obtain ⟨L, hLS, U, hUS, hL1, hU1, h0, h2⟩ := axial_contacts_of_equality S lo hi
    a0 a1 b c d ha0 ha1 hb hc hd hS hL hU hw hsum
  have hLp := hplane L hLS
  have hUp := hplane U hUS
  simp only [Fin.sum_univ_three, hL1, hU1, h0, h2, mul_zero, mul_one] at hLp hUp
  exact hA (by linarith only [hLp, hUp])

/-- The same hypotheses give a strict width bound, without compactness or convexity. -/
theorem one_lt_width_of_supports (S : Set Point) (lo hi : Point) (a0 a1 b c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hS : Supports S lo hi a0 a1 b c d)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1)
    (hw : ∀ i, 0 < hi i - lo i) (A : Point) (D : ℝ) (hA : A 1 ≠ 0)
    (hplane : ∀ x ∈ S, ∑ i, A i * x i = D) : 1 < ∑ i, (hi i - lo i) := by
  obtain ⟨h0, h1, h2⟩ := budgets_of_numeric_rows lo hi a0 a1 b c d ha0 ha1 hb hc hd
    (numeric_rows_of_supports S lo hi a0 a1 b c d ha0 ha1 hb hc hd hS hL hU)
  have hbound := width_bound (fun i => hi i - lo i) b
    (RowCCapTransfer.q a0 a1 b c d) (RowCCapTransfer.v a0 a1 b c d)
    (fun i => (hw i).le) hb (by unfold RowCCapTransfer.q; positivity)
    (RowCCapTransfer.coefficient_bound a0 a1 b c d ha0 ha1 hb hc hd) h0 h1 h2
  exact lt_of_le_of_ne hbound (ne_one_of_supports S lo hi a0 a1 b c d
    ha0 ha1 hb hc hd hS hL hU hw A D hA hplane).symm

/-- The five empty caps provide positive supports on the whole convex set. -/
theorem exists_supports (K : Set Point) (hK : Convex ℝ K) (lo hi : Point)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hcapU12 : ¬ ∃ x ∈ K, hi 1 < x 1 ∧ hi 2 < x 2)
    (hcapL02 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 2 < lo 2)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1)
    (hmix21 : ¬ ∃ x ∈ K, hi 2 < x 2 ∧ x 1 < lo 1) :
    ∃ a0 a1 b c d : ℝ, 0 < a0 ∧ 0 < a1 ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      Supports K lo hi a0 a1 b c d := by
  obtain ⟨a0, ha0, hsa0⟩ := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (hi 1) (hhi 0) (hhi 1)
    (hU 0) (hU 1) hcapU01
  obtain ⟨a1, ha1, hsa1⟩ := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj 1) (AffineMap.proj 2) (hi 1) (hi 2) (hhi 1) (hhi 2)
    (hU 1) (hU 2) hcapU12
  obtain ⟨b, hb, hsb⟩ := ConvexCellSeparation.exists_lower_support K hK
    (AffineMap.proj 2) (AffineMap.proj 0) (lo 2) (lo 0) (hlo 2) (hlo 0)
    (hL 2) (hL 0) (fun ⟨x, hx, h1, h2⟩ => hcapL02 ⟨x, hx, h2, h1⟩)
  obtain ⟨c, hc, hsc⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (lo 1) (hhi 0) (hlo 1)
    (hU 0) (hL 1) hmix01
  obtain ⟨d, hd, hsd⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 2) (AffineMap.proj 1) (hi 2) (lo 1) (hhi 2) (hlo 1)
    (hU 2) (hL 1) hmix21
  exact ⟨a0, a1, b, c, d, ha0, ha1, hb, hc, hd,
    fun x hx => ⟨hsa0 x hx, hsa1 x hx, hsb x hx, hsc x hx, hsd x hx⟩⟩

/-- A strict row-C cover of a plane with nonzero middle coefficient has total width greater than one. -/
theorem one_lt_width_of_caps (K : Set Point) (hK : Convex ℝ K) (lo hi : Point)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (hw : ∀ i, 0 < hi i - lo i) (A : Point) (D : ℝ) (hA : A 1 ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hcapU12 : ¬ ∃ x ∈ K, hi 1 < x 1 ∧ hi 2 < x 2)
    (hcapL02 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 2 < lo 2)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1)
    (hmix21 : ¬ ∃ x ∈ K, hi 2 < x 2 ∧ x 1 < lo 1) : 1 < ∑ i, (hi i - lo i) := by
  obtain ⟨a0, a1, b, c, d, ha0, ha1, hb, hc, hd, hS⟩ :=
    exists_supports K hK lo hi hlo hhi hL hU hcapU01 hcapU12 hcapL02 hmix01 hmix21
  exact one_lt_width_of_supports K lo hi a0 a1 b c d ha0 ha1 hb hc hd hS hL hU hw A D hA hplane

end Plank.Convex.RowCStrictEquality

/-- info: 'Plank.Convex.RowCStrictEquality.coefficients_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowCStrictEquality.coefficients_eq_one

/-- info: 'Plank.Convex.RowCStrictEquality.axial_contacts_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowCStrictEquality.axial_contacts_of_equality

/-- info: 'Plank.Convex.RowCStrictEquality.one_lt_width_of_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowCStrictEquality.one_lt_width_of_caps
