/- The six contact inequalities of row F imply three contracting budgets.
The centered plane offset is nonnegative for an actual deficient cover. -/
module
public import Plank.Convex.RowFCapAlgebra
public import Plank.Convex.RowFCapCoefficients
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowFCapTransfer
open scoped BigOperators
open RowFCapAlgebra RowFCapCoefficients SameSignCapProduct

theorem budgets_of_contact_bounds (lo hi A : Point) (a c d e P C0 C1 : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hP : 0 ≤ P) (horder : ∀ i, lo i ≤ hi i)
    (hrows : NumericRows lo hi A a c d e P C0 C1) :
    ∀ i, 1 ≤ budget (fun i => hi i - lo i)
      (forward A a c d e C0) (reverse A a c d e C1) i := by
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  have hac : 0 < a + c := add_pos ha hc
  have hae : 0 < 1 + a * e := by positivity
  have hK : 0 < k A d e := by unfold k m; positivity
  have hL : 0 < ell A c d := by unfold ell m; positivity
  obtain ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩ := hrows
  have hl0' : lo 0 ≤ (m A d * (hi 1 - lo 1) - (P - A 2 * (hi 2 - lo 2))) / k A d e :=
    (le_div_iff₀ hK).mpr (by simpa only [kC, mC, k, m, mul_comm] using hl0)
  have hu0' := (le_div_iff₀ hac).mpr hu0
  have hl1' : lo 1 ≤ (A 0 * (hi 0 - lo 0) - (P - A 2 * (hi 2 - lo 2))) / ell A c d :=
    (le_div_iff₀ hL).mpr (by simpa only [lC, mC, ell, m, mul_comm] using hl1)
  have hu1' := (le_div_iff₀ hae).mpr hu1
  have hl2' := (le_div_iff₀ hA2).mpr (by simpa only [mul_comm] using hl2)
  have hu2' : 1 - hi 2 ≤
      (e * d * (P - A 2 * (hi 2 - lo 2)) + A 0 * d * (hi 1 - lo 1)) / k A d e :=
    (le_div_iff₀ hK).mpr (by simpa only [kC, mC, k, m, mul_comm] using hu2)
  intro i
  fin_cases i
  · change 1 ≤ (hi 0 - lo 0) + (t a c + m A d / k A d e) * (hi 1 - lo 1) +
      (A 2 / k A d e) * (hi 2 - lo 2)
    have hid : (m A d * (hi 1 - lo 1) - (P - A 2 * (hi 2 - lo 2))) / k A d e +
        a * c * (hi 1 - lo 1) / (a + c) =
        (t a c + m A d / k A d e) * (hi 1 - lo 1) +
          (A 2 / k A d e) * (hi 2 - lo 2) - P / k A d e := by
      unfold t
      ring
    have hs := add_le_add hl0' hu0'
    rw [hid] at hs
    linarith only [hs, div_nonneg hP hK.le]
  · change 1 ≤ (hi 1 - lo 1) + (A 2 / ell A c d) * (hi 2 - lo 2) +
      (s a e + A 0 / ell A c d) * (hi 0 - lo 0)
    have hid : (A 0 * (hi 0 - lo 0) - (P - A 2 * (hi 2 - lo 2))) / ell A c d +
        e * (hi 0 - lo 0) / (1 + a * e) =
        (A 2 / ell A c d) * (hi 2 - lo 2) +
          (s a e + A 0 / ell A c d) * (hi 0 - lo 0) - P / ell A c d := by
      unfold s
      ring
    have hs := add_le_add hl1' hu1'
    rw [hid] at hs
    linarith only [hs, div_nonneg hP hL.le]
  · change 1 ≤ (hi 2 - lo 2) + (C0 / A 2) * (hi 0 - lo 0) +
      (C1 / A 2 + A 0 * d / k A d e) * (hi 1 - lo 1)
    have hid : (C0 * (hi 0 - lo 0) + C1 * (hi 1 - lo 1) - P) / A 2 +
        (e * d * (P - A 2 * (hi 2 - lo 2)) + A 0 * d * (hi 1 - lo 1)) / k A d e =
        (C0 / A 2) * (hi 0 - lo 0) +
          (C1 / A 2 + A 0 * d / k A d e) * (hi 1 - lo 1) -
          ((A 0 + e * A 1) / (k A d e * A 2)) * P -
          (e * d * A 2 / k A d e) * (hi 2 - lo 2) := by
      field_simp [ne_of_gt hA2, ne_of_gt hK]
      unfold k m
      ring
    have hs := add_le_add hl2' hu2'
    rw [hid] at hs
    have hp : 0 ≤ ((A 0 + e * A 1) / (k A d e * A 2)) * P := by positivity
    have hw : 0 ≤ (e * d * A 2 / k A d e) * (hi 2 - lo 2) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (horder 2))
    linarith only [hs, hp, hw]

theorem width_bound_of_contact_bounds (lo hi A : Point) (a c d e P C0 C1 : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hP : 0 ≤ P) (horder : ∀ i, lo i ≤ hi i)
    (hgood : GoodCoefficients A a c d e C0 C1)
    (hrows : NumericRows lo hi A a c d e P C0 C1) : 1 ≤ ∑ i, (hi i - lo i) := by
  obtain ⟨hC0, hC1, h0b, h0p, h1b, h1p⟩ := hgood
  obtain ⟨hf, hr, hpair, hfp, hrp⟩ := coefficient_path_bounds A a c d e C0 C1
    hA ha hc hd he hC0 hC1 h0b h0p h1b h1p
  have hbudgets := budgets_of_contact_bounds lo hi A a c d e P C0 C1
    hA ha hc hd he hP horder hrows
  exact WidthBudgets.width_bound_of_pair_and_path_bounds (fun i => hi i - lo i)
    (forward A a c d e C0) (reverse A a c d e C1)
    (fun i => sub_nonneg.mpr (horder i)) hf hr (hpair 0) (hpair 1) (hpair 2) hfp hrp
    (hbudgets 0) (hbudgets 1) (hbudgets 2)

theorem numeric_width_bound (lo hi A : Point) (a c d e P : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hP : 0 ≤ P) (horder : ∀ i, lo i ≤ hi i)
    (hrows : CaseRows lo hi A a c d e P) : 1 ≤ ∑ i, (hi i - lo i) := by
  rcases hrows with ⟨_, hrows⟩ | ⟨_, hrows⟩
  · exact width_bound_of_contact_bounds lo hi A a c d e P _ _ hA ha hc hd he hP horder
      (good_left A a c d e hA ha hc hd he) hrows
  · exact width_bound_of_contact_bounds lo hi A a c d e P _ _ hA ha hc hd he hP horder
      (good_right A a c d e hA ha hc hd he) hrows

end Plank.Convex.RowFCapTransfer

/-- info: 'Plank.Convex.RowFCapTransfer.numeric_width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowFCapTransfer.numeric_width_bound
