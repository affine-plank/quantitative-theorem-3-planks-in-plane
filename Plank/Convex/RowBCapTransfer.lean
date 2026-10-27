/- A universal transfer-budget bound for four singleton caps and one mixed cap.
The coefficient gaps are squares or positive monomials; no plane relation or
endpoint-polynomial enumeration is needed. -/
module
public import Plank.Convex.SameSignCapAlgebra
public import Plank.Convex.WidthBudgets
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowBCapTransfer
open scoped BigOperators
open SameSignCapAlgebra

def forward (a0 a1 b0 b2 c : ℝ) : Point :=
  ![b0 / (1 + b0 * a1 * b2) + a0 * c / (a0 + c),
    a1 / (1 + a0 * a1 * b2), b2 + 1 / (a1 * (b0 + c))]

def reverse (a0 a1 b0 b2 c : ℝ) : Point :=
  ![b0 * a1 / (1 + b0 * a1 * b2),
    1 / (b0 + c) + a1 * b2 / (1 + a0 * a1 * b2),
    b2 * (a0 * c / (a0 + c)) + 1 / a1]

def denominator (a0 a1 b0 b2 c : ℝ) : ℝ :=
  (a0 + c) * (b0 + c) * (1 + a0 * a1 * b2) * (1 + b0 * a1 * b2)

theorem denominator_pos (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c) :
    0 < denominator a0 a1 b0 b2 c := by
  unfold denominator
  positivity

theorem pair_gap_zero (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c) :
    (1 - forward a0 a1 b0 b2 c 0 * reverse a0 a1 b0 b2 c 1) *
      denominator a0 a1 b0 b2 c = (c - a0 * b0 * (a1 * b2)) ^ 2 := by
  have hac : a0 + c ≠ 0 := ne_of_gt (add_pos ha0 hc)
  have hbc : b0 + c ≠ 0 := ne_of_gt (add_pos hb0 hc)
  have hd0 : 1 + b0 * a1 * b2 ≠ 0 := ne_of_gt (by positivity)
  have hd1 : 1 + a0 * a1 * b2 ≠ 0 := ne_of_gt (by positivity)
  simp only [forward, reverse, denominator, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

theorem pair_gap_one (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (_hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c) :
    (1 - forward a0 a1 b0 b2 c 1 * reverse a0 a1 b0 b2 c 2) *
      ((a0 + c) * (1 + a0 * a1 * b2)) = a0 ^ 2 * a1 * b2 := by
  have hac : a0 + c ≠ 0 := ne_of_gt (add_pos ha0 hc)
  have hd1 : 1 + a0 * a1 * b2 ≠ 0 := ne_of_gt (by positivity)
  have hav : a1 ≠ 0 := ne_of_gt ha1
  simp only [forward, reverse, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp
  ring

theorem pair_gap_two (a0 a1 b0 b2 c : ℝ)
    (_ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c) :
    (1 - forward a0 a1 b0 b2 c 2 * reverse a0 a1 b0 b2 c 0) *
      ((b0 + c) * (1 + b0 * a1 * b2)) = c := by
  have hbc : b0 + c ≠ 0 := ne_of_gt (add_pos hb0 hc)
  have hd0 : 1 + b0 * a1 * b2 ≠ 0 := ne_of_gt (by positivity)
  have hav : a1 ≠ 0 := ne_of_gt ha1
  simp only [forward, reverse, Matrix.cons_val_zero, Matrix.cons_val]
  field_simp
  ring

/-- The two path bounds follow from two positive rational gaps. -/
theorem path_bounds (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c) :
    forward a0 a1 b0 b2 c 1 * forward a0 a1 b0 b2 c 2 ≤ reverse a0 a1 b0 b2 c 1 ∧
      reverse a0 a1 b0 b2 c 0 * reverse a0 a1 b0 b2 c 2 ≤ forward a0 a1 b0 b2 c 0 := by
  have hac : 0 < a0 + c := by positivity
  have hbc : 0 < b0 + c := by positivity
  have hdl : 0 < 1 + b0 * a1 * b2 := by positivity
  have hdu : 0 < 1 + a0 * a1 * b2 := by positivity
  have hF : (reverse a0 a1 b0 b2 c 1 -
      forward a0 a1 b0 b2 c 1 * forward a0 a1 b0 b2 c 2) *
      ((b0 + c) * (1 + a0 * a1 * b2)) = a0 * a1 * b2 := by
    simp only [forward, reverse, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp
    ring
  have hR : (forward a0 a1 b0 b2 c 0 -
      reverse a0 a1 b0 b2 c 0 * reverse a0 a1 b0 b2 c 2) *
      ((a0 + c) * (1 + b0 * a1 * b2)) = a0 * c := by
    simp only [forward, reverse, Matrix.cons_val_zero, Matrix.cons_val]
    field_simp
    ring
  constructor
  · nlinarith only [hF, mul_pos hbc hdu, mul_pos (mul_pos ha0 ha1) hb2]
  · nlinarith only [hR, mul_pos hac hdl, mul_pos ha0 hc]

theorem coefficient_path_bounds (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c) :
    (∀ i, 0 ≤ forward a0 a1 b0 b2 c i) ∧
    (∀ i, 0 ≤ reverse a0 a1 b0 b2 c i) ∧
    (∀ i, forward a0 a1 b0 b2 c i * reverse a0 a1 b0 b2 c (next i) ≤ 1) ∧
    forward a0 a1 b0 b2 c 1 * forward a0 a1 b0 b2 c 2 ≤ reverse a0 a1 b0 b2 c 1 ∧
    reverse a0 a1 b0 b2 c 0 * reverse a0 a1 b0 b2 c 2 ≤ forward a0 a1 b0 b2 c 0 := by
  have hD := denominator_pos a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
  have h0 := pair_gap_zero a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
  have h1 := pair_gap_one a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
  have h2 := pair_gap_two a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
  have hA : 0 < (a0 + c) * (1 + a0 * a1 * b2) := by positivity
  have hB : 0 < (b0 + c) * (1 + b0 * a1 * b2) := by positivity
  refine ⟨?_, ?_, ?_, path_bounds a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc⟩
  · intro i
    fin_cases i
    · change 0 ≤ b0 / (1 + b0 * a1 * b2) + a0 * c / (a0 + c)
      positivity
    · change 0 ≤ a1 / (1 + a0 * a1 * b2)
      positivity
    · change 0 ≤ b2 + 1 / (a1 * (b0 + c))
      positivity
  · intro i
    fin_cases i
    · change 0 ≤ b0 * a1 / (1 + b0 * a1 * b2)
      positivity
    · change 0 ≤ 1 / (b0 + c) + a1 * b2 / (1 + a0 * a1 * b2)
      positivity
    · change 0 ≤ b2 * (a0 * c / (a0 + c)) + 1 / a1
      positivity
  · intro i
    fin_cases i
    · change forward a0 a1 b0 b2 c 0 * reverse a0 a1 b0 b2 c 1 ≤ 1
      nlinarith only [h0, hD, sq_nonneg (c - a0 * b0 * (a1 * b2))]
    · change forward a0 a1 b0 b2 c 1 * reverse a0 a1 b0 b2 c 2 ≤ 1
      have hp : 0 ≤ a0 ^ 2 * a1 * b2 := by positivity
      nlinarith only [h1, hA, hp]
    · change forward a0 a1 b0 b2 c 2 * reverse a0 a1 b0 b2 c 0 ≤ 1
      nlinarith only [h2, hB, hc]

/-- Compatibility with the cycle-product interface. The main width proof
uses the stronger path bounds directly. -/
theorem coefficient_bounds (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c) :
    (∀ i, 0 ≤ forward a0 a1 b0 b2 c i) ∧
    (∀ i, 0 ≤ reverse a0 a1 b0 b2 c i) ∧
    (∀ i, forward a0 a1 b0 b2 c i * reverse a0 a1 b0 b2 c (next i) ≤ 1) ∧
    (∏ i, forward a0 a1 b0 b2 c i) + (∏ i, reverse a0 a1 b0 b2 c i) ≤ 2 := by
  obtain ⟨hf, hr, hp, hfp, hrp⟩ := coefficient_path_bounds a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
  exact ⟨hf, hr, hp, WidthBudgets.cycle_sum_bound_of_paths _ _ (hf 0) (hr 1) (hp 0) hfp hrp⟩

/-- The six contact inequalities for row B imply the width bound for all
positive separator slopes. No slope balance or strict window margins are needed. -/
theorem width_bound_of_contact_bounds (lo hi : Point) (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c)
    (horder : ∀ i, lo i ≤ hi i)
    (hl0 : lo 0 * (1 + b0 * a1 * b2) ≤ b0 * (hi 1 - lo 1) + b0 * a1 * (hi 2 - lo 2))
    (hu0 : (1 - hi 0) * (a0 + c) ≤ a0 * c * (hi 1 - lo 1))
    (hl1 : lo 1 * (b0 + c) ≤ hi 0 - lo 0)
    (hu1 : (1 - hi 1) * (1 + a0 * a1 * b2) ≤ a1 * (hi 2 - lo 2) + a1 * b2 * (hi 0 - lo 0))
    (hl2 : lo 2 * (a0 + c) ≤ b2 * (a0 + c) * (hi 0 - lo 0) + a0 * b2 * c * (hi 1 - lo 1))
    (hu2 : (1 - hi 2) * a1 * (b0 + c) ≤ (b0 + c) * (hi 1 - lo 1) + (hi 0 - lo 0)) :
    1 ≤ ∑ i, (hi i - lo i) := by
  have hdl : 0 < 1 + b0 * a1 * b2 := by positivity
  have hdu : 0 < 1 + a0 * a1 * b2 := by positivity
  have hac : 0 < a0 + c := add_pos ha0 hc
  have hbc : 0 < b0 + c := add_pos hb0 hc
  have havc : 0 < a1 * (b0 + c) := mul_pos ha1 hbc
  have hl0' := (le_div_iff₀ hdl).mpr hl0
  have hu0' := (le_div_iff₀ hac).mpr hu0
  have hl1' := (le_div_iff₀ hbc).mpr hl1
  have hu1' := (le_div_iff₀ hdu).mpr hu1
  have hl2' := (le_div_iff₀ hac).mpr hl2
  have hu2' : 1 - hi 2 ≤ ((b0 + c) * (hi 1 - lo 1) + (hi 0 - lo 0)) / (a1 * (b0 + c)) :=
    (le_div_iff₀ havc).mpr (by nlinarith only [hu2])
  obtain ⟨hf, hr, hp, hfp, hrp⟩ := coefficient_path_bounds a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
  apply WidthBudgets.width_bound_of_pair_and_path_bounds (fun i => hi i - lo i)
    (forward a0 a1 b0 b2 c) (reverse a0 a1 b0 b2 c)
    (fun i => sub_nonneg.mpr (horder i)) hf hr (hp 0) (hp 1) (hp 2) hfp hrp
  · have h := add_le_add_left (add_le_add hl0' hu0') (hi 0 - lo 0)
    change 1 ≤ (hi 0 - lo 0) +
      (b0 / (1 + b0 * a1 * b2) + a0 * c / (a0 + c)) * (hi 1 - lo 1) +
      (b0 * a1 / (1 + b0 * a1 * b2)) * (hi 2 - lo 2)
    convert h using 1 <;> ring
  · have h := add_le_add_left (add_le_add hl1' hu1') (hi 1 - lo 1)
    change 1 ≤ (hi 1 - lo 1) + (a1 / (1 + a0 * a1 * b2)) * (hi 2 - lo 2) +
      (1 / (b0 + c) + a1 * b2 / (1 + a0 * a1 * b2)) * (hi 0 - lo 0)
    convert h using 1 <;> ring
  · have h := add_le_add_left (add_le_add hl2' hu2') (hi 2 - lo 2)
    change 1 ≤ (hi 2 - lo 2) + (b2 + 1 / (a1 * (b0 + c))) * (hi 0 - lo 0) +
      (b2 * (a0 * c / (a0 + c)) + 1 / a1) * (hi 1 - lo 1)
    convert h using 1 <;> field_simp [ne_of_gt hac, ne_of_gt hbc, ne_of_gt ha1] <;> ring

end Plank.Convex.RowBCapTransfer

/-- info: 'Plank.Convex.RowBCapTransfer.width_bound_of_contact_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowBCapTransfer.width_bound_of_contact_bounds
