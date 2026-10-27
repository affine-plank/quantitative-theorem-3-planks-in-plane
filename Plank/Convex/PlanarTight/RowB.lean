/- The strictly positive transfer gaps of row B exclude positive-width equality. -/
module
public import Plank.Convex.RowBCapAlgebra
public import Plank.Convex.RowBCapTransfer
public import Plank.Convex.SameSignCapTightRigidity
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.RowB
open RowBCapAlgebra RowBCapTransfer

theorem not_tight_of_rows (lo hi : Point) (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c)
    (hwidth : ∀ i, lo i < hi i) (hrows : NumericRows lo hi a0 a1 b0 b2 c) :
    (∑ i, (hi i - lo i)) ≠ 1 := by
  intro hsum
  obtain ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩ := hrows
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
  have hbudget (i : Fin 3) : 1 ≤ SameSignCapProduct.budget (fun j => hi j - lo j)
      (forward a0 a1 b0 b2 c) (reverse a0 a1 b0 b2 c) i := by
    fin_cases i
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
      convert h using 1 <;> field_simp [hac.ne', hbc.ne', ha1.ne'] <;> ring
  have hf (i : Fin 3) : 0 < forward a0 a1 b0 b2 c i := by
    fin_cases i <;> dsimp [forward] <;> positivity
  obtain ⟨_, hr, hp, hcycle⟩ := coefficient_bounds a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
  have he := SameSignCapTightRigidity.pair_eq_one_of_tight (fun j => hi j - lo j)
    (forward a0 a1 b0 b2 c) (reverse a0 a1 b0 b2 c)
    (fun j => sub_pos.mpr (hwidth j)) hf hr hp hcycle hbudget hsum 1
  change forward a0 a1 b0 b2 c 1 * reverse a0 a1 b0 b2 c 2 = 1 at he
  have hg := pair_gap_one a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
  rw [he, sub_self, zero_mul] at hg
  have hpos : 0 < a0 ^ 2 * a1 * b2 := by positivity
  linarith only [hg, hpos]

/-- Four same-sign empty caps and the intervening mixed cap cost strictly
more than one when all three windows have positive width. -/
theorem not_tight_of_caps (K : Set Point) (hK : Convex ℝ K)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hwidth : ∀ i, lo i < hi i)
    (hcapL01 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 1 < lo 1)
    (hcapU12 : ¬ ∃ x ∈ K, hi 1 < x 1 ∧ hi 2 < x 2)
    (hcapL02 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 2 < lo 2)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1) :
    (∑ i, (hi i - lo i)) ≠ 1 := by
  obtain ⟨a0, a1, b0, b2, c, ha0, ha1, hb0, hb2, hc, hrows⟩ :=
    exists_numeric_rows K hK lo hi hlo hhi hL hU hcapL01 hcapU12 hcapL02 hcapU01 hmix01
  exact not_tight_of_rows lo hi a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc hwidth hrows

end Plank.Convex.PlanarTight.RowB

/-- info: 'Plank.Convex.PlanarTight.RowB.not_tight_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowB.not_tight_of_rows

/-- info: 'Plank.Convex.PlanarTight.RowB.not_tight_of_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowB.not_tight_of_caps
