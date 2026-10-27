/- A single square gives the pair bounds for row C; the two path comparisons
are equalities. The general bounded-row criterion then gives the width bound. -/
module
public import Plank.Convex.WidthBudgets
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowCCapTransfer
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

def q (a0 a1 b2 c d : ℝ) : ℝ :=
  b2 * (a0 * c / (a0 + c)) + d / (1 + a1 * d)

def v (a0 a1 b2 c d : ℝ) : ℝ :=
  1 / (d + b2 * c) + a1 / (1 + a0 * a1 * b2)

def denominator (a0 a1 b2 c d : ℝ) : ℝ :=
  (a0 + c) * (1 + a1 * d) * (d + b2 * c) * (1 + a0 * a1 * b2)

/-- Clearing positive denominators leaves one square. -/
theorem coefficient_gap (a0 a1 b2 c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb2 : 0 < b2) (hc : 0 < c) (hd : 0 < d) :
    (1 - q a0 a1 b2 c d * v a0 a1 b2 c d) * denominator a0 a1 b2 c d =
      b2 * (a0 * a1 * d - c) ^ 2 := by
  have h1 : a0 + c ≠ 0 := ne_of_gt (by positivity)
  have h2 : 1 + a1 * d ≠ 0 := ne_of_gt (by positivity)
  have h3 : d + b2 * c ≠ 0 := ne_of_gt (by positivity)
  have h4 : 1 + a0 * a1 * b2 ≠ 0 := ne_of_gt (by positivity)
  unfold q v denominator
  field_simp
  ring

theorem coefficient_bound (a0 a1 b2 c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb2 : 0 < b2) (hc : 0 < c) (hd : 0 < d) :
    q a0 a1 b2 c d * v a0 a1 b2 c d ≤ 1 := by
  have h := coefficient_gap a0 a1 b2 c d ha0 ha1 hb2 hc hd
  have hD : 0 < denominator a0 a1 b2 c d := by unfold denominator; positivity
  have hN : 0 ≤ b2 * (a0 * a1 * d - c) ^ 2 := mul_nonneg hb2.le (sq_nonneg _)
  nlinarith only [h, hD, hN]

/-- The repeated row-C coefficients satisfy both path comparisons with
equality. Their pair bounds reduce to one product being at most one. -/
theorem width_bound_of_two_coefficients (w : Point) (b Q V : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hb : 0 < b) (hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (hQV : Q * V ≤ 1)
    (h0 : 1 ≤ w 0 + (Q / b) * w 1 + (1 / b) * w 2)
    (h1 : 1 ≤ w 1 + V * w 2 + (b * V) * w 0)
    (h2 : 1 ≤ w 2 + b * w 0 + Q * w 1) : 1 ≤ ∑ i, w i := by
  apply WidthBudgets.width_bound_of_pair_and_path_bounds w
    ![Q / b, V, b] ![1 / b, b * V, Q] hw
    (by intro i; fin_cases i <;> dsimp <;> positivity)
    (by intro i; fin_cases i <;> dsimp <;> positivity)
  · change (Q / b) * (b * V) ≤ 1
    calc
      _ = Q * V := by field_simp
      _ ≤ 1 := hQV
  · change V * Q ≤ 1
    simpa only [mul_comm] using hQV
  · change b * (1 / b) ≤ 1
    exact le_of_eq (by field_simp)
  · exact le_of_eq (mul_comm V b)
  · exact le_of_eq (by change (1 / b) * Q = Q / b; ring)
  · exact h0
  · exact h1
  · exact h2

/-- All six row-C contact inequalities imply the width bound for arbitrary
positive separator slopes and ordered windows. -/
theorem width_bound_of_contact_bounds (lo hi : Point) (a0 a1 b2 c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb2 : 0 < b2) (hc : 0 < c) (hd : 0 < d)
    (horder : ∀ i, lo i ≤ hi i)
    (hl0 : lo 0 * b2 * (1 + a1 * d) ≤ (1 + a1 * d) * (hi 2 - lo 2) + d * (hi 1 - lo 1))
    (hu0 : (1 - hi 0) * (a0 + c) ≤ a0 * c * (hi 1 - lo 1))
    (hl1 : lo 1 * (d + b2 * c) ≤ (hi 2 - lo 2) + b2 * (hi 0 - lo 0))
    (hu1 : (1 - hi 1) * (1 + a0 * a1 * b2) ≤ a1 * (hi 2 - lo 2) + a1 * b2 * (hi 0 - lo 0))
    (hl2 : lo 2 * (a0 + c) ≤ b2 * (a0 + c) * (hi 0 - lo 0) + a0 * b2 * c * (hi 1 - lo 1))
    (hu2 : (1 - hi 2) * (1 + a1 * d) ≤ d * (hi 1 - lo 1)) :
    1 ≤ ∑ i, (hi i - lo i) := by
  have hac : 0 < a0 + c := by positivity
  have had : 0 < 1 + a1 * d := by positivity
  have hdc : 0 < d + b2 * c := by positivity
  have hdu : 0 < 1 + a0 * a1 * b2 := by positivity
  have hl0' : lo 0 ≤ ((1 + a1 * d) * (hi 2 - lo 2) + d * (hi 1 - lo 1)) / (b2 * (1 + a1 * d)) :=
    (le_div_iff₀ (mul_pos hb2 had)).mpr (by simpa only [mul_assoc] using hl0)
  have hu0' := (le_div_iff₀ hac).mpr hu0
  have hl1' := (le_div_iff₀ hdc).mpr hl1
  have hu1' := (le_div_iff₀ hdu).mpr hu1
  have hl2' := (le_div_iff₀ hac).mpr hl2
  have hu2' := (le_div_iff₀ had).mpr hu2
  have hQ : 0 ≤ q a0 a1 b2 c d := by unfold q; positivity
  have hV : 0 ≤ v a0 a1 b2 c d := by unfold v; positivity
  apply width_bound_of_two_coefficients (fun i => hi i - lo i) b2
    (q a0 a1 b2 c d) (v a0 a1 b2 c d) (fun i => sub_nonneg.mpr (horder i))
    hb2 hQ hV (coefficient_bound a0 a1 b2 c d ha0 ha1 hb2 hc hd)
  · have h := add_le_add_left (add_le_add hl0' hu0') (hi 0 - lo 0)
    unfold q
    convert h using 1 <;> field_simp [ne_of_gt hb2, ne_of_gt hac, ne_of_gt had] <;> ring
  · have h := add_le_add_left (add_le_add hl1' hu1') (hi 1 - lo 1)
    unfold v
    convert h using 1 <;> ring
  · have h := add_le_add_left (add_le_add hl2' hu2') (hi 2 - lo 2)
    unfold q
    convert h using 1 <;> field_simp [ne_of_gt hac, ne_of_gt had] <;> ring

end Plank.Convex.RowCCapTransfer

/-- info: 'Plank.Convex.RowCCapTransfer.width_bound_of_contact_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowCCapTransfer.width_bound_of_contact_bounds
