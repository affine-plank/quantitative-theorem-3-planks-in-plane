/- The one-singleton three-mixed-cap budgets have a positive equality gap. -/
module
public import Plank.Convex.PlanarTight.ProductBudgetEquality
public import Plank.Convex.RowFCapTransfer
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.RowF
open RowFCapAlgebra RowFCapCoefficients SameSignCapProduct

/-- The last row is strict when its window has positive width. The proof
retains the loss discarded by the non-strict transfer bound. -/
theorem third_budget_strict (lo hi A : Point) (a c d e P C0 C1 : ℝ)
    (hA : ∀ i, 0 < A i) (hd : 0 < d) (he : 0 < e)
    (hP : 0 ≤ P) (hwidth : lo 2 < hi 2)
    (hrows : NumericRows lo hi A a c d e P C0 C1) :
    1 < budget (fun i => hi i - lo i)
      (forward A a c d e C0) (reverse A a c d e C1) 2 := by
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  have hK : 0 < k A d e := by unfold k m; positivity
  have hl2 := hrows.2.2.2.2.1
  have hu2 := hrows.2.2.2.2.2
  have hl2' := (le_div_iff₀ hA2).mpr (by simpa only [mul_comm] using hl2)
  have hu2' : 1 - hi 2 ≤
      (e * d * (P - A 2 * (hi 2 - lo 2)) + A 0 * d * (hi 1 - lo 1)) / k A d e :=
    (le_div_iff₀ hK).mpr (by simpa only [kC, mC, k, m, mul_comm] using hu2)
  have hid : (C0 * (hi 0 - lo 0) + C1 * (hi 1 - lo 1) - P) / A 2 +
      (e * d * (P - A 2 * (hi 2 - lo 2)) + A 0 * d * (hi 1 - lo 1)) / k A d e =
      (C0 / A 2) * (hi 0 - lo 0) +
        (C1 / A 2 + A 0 * d / k A d e) * (hi 1 - lo 1) -
        ((A 0 + e * A 1) / (k A d e * A 2)) * P -
        (e * d * A 2 / k A d e) * (hi 2 - lo 2) := by
    field_simp [hA2.ne', hK.ne']
    unfold k m
    ring
  have hs := add_le_add hl2' hu2'
  rw [hid] at hs
  have hp : 0 ≤ ((A 0 + e * A 1) / (k A d e * A 2)) * P := by positivity
  have hw : 0 < (e * d * A 2 / k A d e) * (hi 2 - lo 2) :=
    mul_pos (by positivity) (sub_pos.mpr hwidth)
  change 1 < (hi 2 - lo 2) + (C0 / A 2) * (hi 0 - lo 0) +
    (C1 / A 2 + A 0 * d / k A d e) * (hi 1 - lo 1)
  linarith only [hs, hp, hw]

/-- Good row-F contact data with a nonnegative centered plane offset
cannot have positive widths summing to one. -/
theorem not_tight_of_contact_bounds (lo hi A : Point) (a c d e P C0 C1 : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hP : 0 ≤ P) (hwidth : ∀ i, lo i < hi i)
    (hgood : GoodCoefficients A a c d e C0 C1)
    (hrows : NumericRows lo hi A a c d e P C0 C1) :
    (∑ i, (hi i - lo i)) ≠ 1 := by
  intro hsum
  obtain ⟨hC0, hC1, h0b, h0p, h1b, h1p⟩ := hgood
  obtain ⟨hf, hr, hpair, hfp, hrp⟩ := coefficient_path_bounds A a c d e C0 C1
    hA ha hc hd he hC0 hC1 h0b h0p h1b h1p
  have hbudgets := RowFCapTransfer.budgets_of_contact_bounds lo hi A a c d e P C0 C1
    hA ha hc hd he hP (fun i => (hwidth i).le) hrows
  have hcycle := WidthBudgets.cycle_sum_bound_of_paths _ _ (hf 0) (hr 1) (hpair 0) hfp hrp
  have heq := ProductBudgetEquality.budgets_eq_one (fun i => hi i - lo i)
    (forward A a c d e C0) (reverse A a c d e C1)
    (fun i => sub_pos.mpr (hwidth i)) hf hr hpair hcycle hbudgets hsum 2
  have hstrict := third_budget_strict lo hi A a c d e P C0 C1 hA hd he hP (hwidth 2) hrows
  exact (ne_of_gt hstrict) heq

/-- Both choices of the contact polygon vertex exclude equality. -/
theorem not_tight_of_numeric_rows (lo hi A : Point) (a c d e P : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hP : 0 ≤ P) (hwidth : ∀ i, lo i < hi i)
    (hrows : CaseRows lo hi A a c d e P) : (∑ i, (hi i - lo i)) ≠ 1 := by
  rcases hrows with ⟨_, hrows⟩ | ⟨_, hrows⟩
  · exact not_tight_of_contact_bounds lo hi A a c d e P _ _ hA ha hc hd he hP hwidth
      (good_left A a c d e hA ha hc hd he) hrows
  · exact not_tight_of_contact_bounds lo hi A a c d e P _ _ hA ha hc hd he hP hwidth
      (good_right A a c d e hA ha hc hd he) hrows

/-- Geometric row-F obstruction when the positive plane lies above the
lower window corner. The plane-box condition is explicit; it must not be
borrowed from a deficient-cover lemma at equality. -/
theorem not_tight_of_caps (K : Set Point) (hK : Convex ℝ K)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1) (hwidth : ∀ i, lo i < hi i)
    (hcorner : ∑ i, A i * lo i ≤ D)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1)
    (hmix21 : ¬ ∃ x ∈ K, hi 2 < x 2 ∧ x 1 < lo 1)
    (hmix10 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ hi 1 < x 1) :
    (∑ i, (hi i - lo i)) ≠ 1 := by
  let P := D - ∑ i, A i * lo i
  have hcentered (x : Point) (hx : x ∈ K) : ∑ i, A i * (x i - lo i) = P := by
    simp only [mul_sub, Finset.sum_sub_distrib, hplane x hx, P]
  obtain ⟨a, c, d, e, ha, hc, hd, he, hrows⟩ :=
    exists_numeric_rows K hK lo hi A P hlo hhi hL hU hA hcentered
      hcapU01 hmix01 hmix21 hmix10
  exact not_tight_of_numeric_rows lo hi A a c d e P hA ha hc hd he
    (sub_nonneg.mpr hcorner) hwidth hrows

end Plank.Convex.PlanarTight.RowF

/-- info: 'Plank.Convex.PlanarTight.RowF.third_budget_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowF.third_budget_strict

/-- info: 'Plank.Convex.PlanarTight.RowF.not_tight_of_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowF.not_tight_of_caps
