/- Row C of the planar cap ledger, pattern (56,3): the three singleton caps (1+,2+), (0−,2−),
(0+,1+) and the two mixed caps (0+,1−), (2+,1−) are empty. Five positive supports at the six
coordinate contacts give six numeric inequalities in the window endpoints and the five slopes. -/
module
public import Plank.Convex.ConvexCellSeparation
public import Plank.Convex.CommonPointUnclipped
public import Plank.Convex.PlanarCapCaseReduction
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowCCapAlgebra
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- The five supports of row C on a set: two upper same-sign supports, one lower same-sign
support and two mixed supports sharing the lower wall of coordinate 1. -/
def Supports (S : Set Point) (lo hi : Point) (a0 a1 b2 c d : ℝ) : Prop :=
  ∀ x ∈ S,
    x 0 + a0 * x 1 ≤ hi 0 + a0 * hi 1 ∧
    x 1 + a1 * x 2 ≤ hi 1 + a1 * hi 2 ∧
    lo 2 + b2 * lo 0 ≤ x 2 + b2 * x 0 ∧
    x 0 - c * x 1 ≤ hi 0 - c * lo 1 ∧
    x 2 - d * x 1 ≤ hi 2 - d * lo 1

/-- The six numeric rows of row C, one per coordinate contact, in the order
`x0 = 0`, `x0 = 1`, `x1 = 0`, `x1 = 1`, `x2 = 0`, `x2 = 1`. -/
def NumericRows (lo hi : Point) (a0 a1 b2 c d : ℝ) : Prop :=
  lo 0 * b2 * (1 + a1 * d) ≤ (1 + a1 * d) * (hi 2 - lo 2) + d * (hi 1 - lo 1) ∧
  (1 - hi 0) * (a0 + c) ≤ a0 * c * (hi 1 - lo 1) ∧
  lo 1 * (d + b2 * c) ≤ (hi 2 - lo 2) + b2 * (hi 0 - lo 0) ∧
  (1 - hi 1) * (1 + a0 * a1 * b2) ≤ a1 * (hi 2 - lo 2) + a1 * b2 * (hi 0 - lo 0) ∧
  lo 2 * (a0 + c) ≤ b2 * (a0 + c) * (hi 0 - lo 0) + a0 * b2 * c * (hi 1 - lo 1) ∧
  (1 - hi 2) * (1 + a1 * d) ≤ d * (hi 1 - lo 1)

/-- Supports at the six coordinate contacts imply the six numeric rows; each row is a
nonnegative combination of the supports at one contact. -/
theorem numeric_rows_of_supports (S : Set Point) (lo hi : Point) (a0 a1 b2 c d : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb2 : 0 < b2) (hc : 0 < c) (hd : 0 < d)
    (hS : Supports S lo hi a0 a1 b2 c d)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1) :
    NumericRows lo hi a0 a1 b2 c d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- contact x0 = 0: L02 bounds z below, M21 and d·U12 bound (1 + a1 d) z above
    obtain ⟨x, hx, h0⟩ := hL 0
    obtain ⟨_, hU12, hL02, _, hM21⟩ := hS x hx
    rw [h0] at hL02
    have h1 := mul_le_mul_of_nonneg_left hL02 (by positivity : (0 : ℝ) ≤ 1 + a1 * d)
    have h2 := mul_le_mul_of_nonneg_left hU12 hd.le
    nlinarith [h1, h2, hM21]
  · -- contact x0 = 1: U01 bounds y above, M01 bounds y below
    obtain ⟨x, hx, h0⟩ := hU 0
    obtain ⟨hU01, _, _, hM01, _⟩ := hS x hx
    rw [h0] at hU01 hM01
    have h1 := mul_le_mul_of_nonneg_left hU01 hc.le
    have h2 := mul_le_mul_of_nonneg_left hM01 ha0.le
    nlinarith [h1, h2]
  · -- contact x1 = 0: b2·M01 and M21 bound z + b2 x above, L02 bounds it below
    obtain ⟨x, hx, h1⟩ := hL 1
    obtain ⟨_, _, hL02, hM01, hM21⟩ := hS x hx
    rw [h1] at hM01 hM21
    have h2 := mul_le_mul_of_nonneg_left hM01 hb2.le
    nlinarith [h2, hM21, hL02]
  · -- contact x1 = 1: U01 bounds x above, U12 bounds z above, L02 bounds z + b2 x below
    obtain ⟨x, hx, h1⟩ := hU 1
    obtain ⟨hU01, hU12, hL02, _, _⟩ := hS x hx
    rw [h1] at hU01 hU12
    have h2 := mul_le_mul_of_nonneg_left hU01 (mul_pos ha1 hb2).le
    have h3 := mul_le_mul_of_nonneg_left hL02 ha1.le
    nlinarith [h2, h3, hU12]
  · -- contact x2 = 0: L02 bounds x below, c·U01 + a0·M01 bounds x above
    obtain ⟨x, hx, h2⟩ := hL 2
    obtain ⟨hU01, _, hL02, hM01, _⟩ := hS x hx
    rw [h2] at hL02
    have h3 := mul_le_mul_of_nonneg_left hU01 hc.le
    have h4 := mul_le_mul_of_nonneg_left hM01 ha0.le
    have hsum : (a0 + c) * x 0 ≤ (a0 + c) * hi 0 + a0 * c * (hi 1 - lo 1) := by linarith
    have h5 := mul_le_mul_of_nonneg_left hL02 (add_pos ha0 hc).le
    have h6 := mul_le_mul_of_nonneg_left hsum hb2.le
    nlinarith [h5, h6]
  · -- contact x2 = 1: U12 bounds y above, M21 bounds y below
    obtain ⟨x, hx, h2⟩ := hU 2
    obtain ⟨_, hU12, _, _, hM21⟩ := hS x hx
    rw [h2] at hU12 hM21
    have h3 := mul_le_mul_of_nonneg_left hU12 hd.le
    nlinarith [h3, hM21]

/-! ### Positive supports from the five empty caps -/

/-- The five empty caps of row C on a convex set with the six coordinate contacts yield positive
slopes whose supports hold on the whole convex set, hence the numeric rows. -/
theorem exists_numeric_rows (K : Set Point) (hK : Convex ℝ K) (lo hi : Point)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hcapU12 : ¬ ∃ x ∈ K, hi 1 < x 1 ∧ hi 2 < x 2)
    (hcapL02 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 2 < lo 2)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1)
    (hmix21 : ¬ ∃ x ∈ K, hi 2 < x 2 ∧ x 1 < lo 1) :
    ∃ a0 a1 b2 c d : ℝ, 0 < a0 ∧ 0 < a1 ∧ 0 < b2 ∧ 0 < c ∧ 0 < d ∧
      NumericRows lo hi a0 a1 b2 c d := by
  obtain ⟨a0, ha0, hsa0⟩ := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (hi 1) (hhi 0) (hhi 1)
    (hU 0) (hU 1) hcapU01
  obtain ⟨a1, ha1, hsa1⟩ := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj 1) (AffineMap.proj 2) (hi 1) (hi 2) (hhi 1) (hhi 2)
    (hU 1) (hU 2) hcapU12
  obtain ⟨b2, hb2, hsb2⟩ := ConvexCellSeparation.exists_lower_support K hK
    (AffineMap.proj 2) (AffineMap.proj 0) (lo 2) (lo 0) (hlo 2) (hlo 0)
    (hL 2) (hL 0) (fun ⟨x, hx, h1, h2⟩ => hcapL02 ⟨x, hx, h2, h1⟩)
  obtain ⟨c, hc, hsc⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (lo 1) (hhi 0) (hlo 1)
    (hU 0) (hL 1) hmix01
  obtain ⟨d, hd, hsd⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 2) (AffineMap.proj 1) (hi 2) (lo 1) (hhi 2) (hlo 1)
    (hU 2) (hL 1) hmix21
  refine ⟨a0, a1, b2, c, d, ha0, ha1, hb2, hc, hd, ?_⟩
  exact numeric_rows_of_supports K lo hi a0 a1 b2 c d ha0 ha1 hb2 hc hd
    (fun x hx => ⟨hsa0 x hx, hsa1 x hx, hsb2 x hx, hsc x hx, hsd x hx⟩) hL hU

/-! ### The ledger interface -/

open PlanarCapCaseReduction PlanarCapPatterns in
/-- An actual normalized cover realizing the row C pattern (56,3) has strictly interior windows and
positive slopes satisfying the six numeric rows. -/
theorem deficit_obstruction (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1)
    (hh : Holds (SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (EdgeEmpty K (fun i => AffineMap.proj i) lo hi) ⟨56, 3⟩) :
    (∀ i, 0 < lo i ∧ hi i < 1) ∧
      ∃ a0 a1 b2 c d : ℝ, 0 < a0 ∧ 0 < a1 ∧ 0 < b2 ∧ 0 < c ∧ 0 < d ∧
        NumericRows lo hi a0 a1 b2 c d := by
  have hm := CommonPointUnclipped.windows_strict_of_deficit K hK hbox hL hU lo hi horder hcover hdef
  refine ⟨hm, ?_⟩
  have hs3 := hh.1 3 (by decide)
  have hs4 := hh.1 4 (by decide)
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  have he1 := hh.2 1 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev] at hs3 hs4 hs5 he0 he1
  simp at hs3 hs4 hs5 he0 he1
  apply exists_numeric_rows K hK lo hi (fun i => (hm i).1) (fun i => (hm i).2) hL hU
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs5 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs3 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs4 x hx h2) (not_le.2 h1)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he0 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he1 x hx h2) (not_le.2 h1)

end Plank.Convex.RowCCapAlgebra

/-- info: 'Plank.Convex.RowCCapAlgebra.numeric_rows_of_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowCCapAlgebra.numeric_rows_of_supports

/-- info: 'Plank.Convex.RowCCapAlgebra.exists_numeric_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowCCapAlgebra.exists_numeric_rows

/-- info: 'Plank.Convex.RowCCapAlgebra.deficit_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowCCapAlgebra.deficit_obstruction
