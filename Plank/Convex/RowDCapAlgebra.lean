/- Row D of the planar cap ledger, pattern (48,5): the two singleton caps (0−,2−), (0+,1+) and the
two mixed caps (0+,1−), (2+,0−) are empty. Four positive supports at the six coordinate contacts
give six numeric inequalities in the window endpoints and the four slopes. -/
module
public import Plank.Convex.ConvexCellSeparation
public import Plank.Convex.CommonPointUnclipped
public import Plank.Convex.PlanarCapCaseReduction
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowDCapAlgebra
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- The four supports of row D on a set: one upper same-sign support, one lower same-sign
support and two mixed supports. -/
def Supports (S : Set Point) (lo hi : Point) (a b c d : ℝ) : Prop :=
  ∀ x ∈ S,
    x 0 + a * x 1 ≤ hi 0 + a * hi 1 ∧
    lo 2 + b * lo 0 ≤ x 2 + b * x 0 ∧
    x 0 - c * x 1 ≤ hi 0 - c * lo 1 ∧
    x 2 - d * x 0 ≤ hi 2 - d * lo 0

/-- The six numeric rows of row D, one per coordinate contact, in the order
`x0 = 0`, `x0 = 1`, `x1 = 0`, `x1 = 1`, `x2 = 0`, `x2 = 1`. -/
def NumericRows (lo hi : Point) (a b c d : ℝ) : Prop :=
  lo 0 * (b + d) ≤ hi 2 - lo 2 ∧
  (1 - hi 0) * (a + c) ≤ a * c * (hi 1 - lo 1) ∧
  lo 1 * c * (b + d) ≤ (b + d) * (hi 0 - lo 0) + (hi 2 - lo 2) ∧
  (1 - hi 1) * a * (b + d) ≤ (b + d) * (hi 0 - lo 0) + (hi 2 - lo 2) ∧
  lo 2 * (a + c) ≤ b * (a + c) * (hi 0 - lo 0) + a * b * c * (hi 1 - lo 1) ∧
  (1 - hi 2) * (a + c) ≤ d * (a + c) * (hi 0 - lo 0) + a * c * d * (hi 1 - lo 1)

/-- Supports at the six coordinate contacts imply the six numeric rows; each row is a
nonnegative combination of the supports at one contact. -/
theorem numeric_rows_of_supports (S : Set Point) (lo hi : Point) (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hS : Supports S lo hi a b c d)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1) :
    NumericRows lo hi a b c d := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- contact x0 = 0: L02 bounds z below, M20 bounds z above
    obtain ⟨x, hx, h0⟩ := hL 0
    obtain ⟨_, hL02, _, hM20⟩ := hS x hx
    rw [h0] at hL02 hM20
    nlinarith [hL02, hM20]
  · -- contact x0 = 1: U01 bounds y above, M01 bounds y below
    obtain ⟨x, hx, h0⟩ := hU 0
    obtain ⟨hU01, _, hM01, _⟩ := hS x hx
    rw [h0] at hU01 hM01
    have h1 := mul_le_mul_of_nonneg_left hU01 hc.le
    have h2 := mul_le_mul_of_nonneg_left hM01 ha.le
    nlinarith [h1, h2]
  · -- contact x1 = 0: L02 and M20 bound (b + d) x below, M01 bounds x above
    obtain ⟨x, hx, h1⟩ := hL 1
    obtain ⟨_, hL02, hM01, hM20⟩ := hS x hx
    rw [h1] at hM01
    have h2 := mul_le_mul_of_nonneg_left hM01 (add_pos hb hd).le
    nlinarith [h2, hL02, hM20]
  · -- contact x1 = 1: L02 and M20 bound (b + d) x below, U01 bounds x above
    obtain ⟨x, hx, h1⟩ := hU 1
    obtain ⟨hU01, hL02, _, hM20⟩ := hS x hx
    rw [h1] at hU01
    have h2 := mul_le_mul_of_nonneg_left hU01 (add_pos hb hd).le
    nlinarith [h2, hL02, hM20]
  · -- contact x2 = 0: L02 bounds x below, c·U01 + a·M01 bounds x above
    obtain ⟨x, hx, h2⟩ := hL 2
    obtain ⟨hU01, hL02, hM01, _⟩ := hS x hx
    rw [h2] at hL02
    have h3 := mul_le_mul_of_nonneg_left hU01 hc.le
    have h4 := mul_le_mul_of_nonneg_left hM01 ha.le
    have hsum : (a + c) * x 0 ≤ (a + c) * hi 0 + a * c * (hi 1 - lo 1) := by linarith
    have h5 := mul_le_mul_of_nonneg_left hL02 (add_pos ha hc).le
    have h6 := mul_le_mul_of_nonneg_left hsum hb.le
    nlinarith [h5, h6]
  · -- contact x2 = 1: M20 bounds x below, c·U01 + a·M01 bounds x above
    obtain ⟨x, hx, h2⟩ := hU 2
    obtain ⟨hU01, _, hM01, hM20⟩ := hS x hx
    rw [h2] at hM20
    have h3 := mul_le_mul_of_nonneg_left hU01 hc.le
    have h4 := mul_le_mul_of_nonneg_left hM01 ha.le
    have hsum : (a + c) * x 0 ≤ (a + c) * hi 0 + a * c * (hi 1 - lo 1) := by linarith
    have h5 := mul_le_mul_of_nonneg_left hM20 (add_pos ha hc).le
    have h6 := mul_le_mul_of_nonneg_left hsum hd.le
    nlinarith [h5, h6]

/-! ### Positive supports from the four empty caps -/

/-- The four empty caps of row D on a convex set with the six coordinate contacts yield positive
slopes whose supports hold on the whole convex set, hence the numeric rows. -/
theorem exists_numeric_rows (K : Set Point) (hK : Convex ℝ K) (lo hi : Point)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hcapL02 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 2 < lo 2)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1)
    (hmix20 : ¬ ∃ x ∈ K, hi 2 < x 2 ∧ x 0 < lo 0) :
    ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ NumericRows lo hi a b c d := by
  obtain ⟨a, ha, hsa⟩ := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (hi 1) (hhi 0) (hhi 1)
    (hU 0) (hU 1) hcapU01
  obtain ⟨b, hb, hsb⟩ := ConvexCellSeparation.exists_lower_support K hK
    (AffineMap.proj 2) (AffineMap.proj 0) (lo 2) (lo 0) (hlo 2) (hlo 0)
    (hL 2) (hL 0) (fun ⟨x, hx, h1, h2⟩ => hcapL02 ⟨x, hx, h2, h1⟩)
  obtain ⟨c, hc, hsc⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (lo 1) (hhi 0) (hlo 1)
    (hU 0) (hL 1) hmix01
  obtain ⟨d, hd, hsd⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 2) (AffineMap.proj 0) (hi 2) (lo 0) (hhi 2) (hlo 0)
    (hU 2) (hL 0) hmix20
  refine ⟨a, b, c, d, ha, hb, hc, hd, ?_⟩
  exact numeric_rows_of_supports K lo hi a b c d ha hb hc hd
    (fun x hx => ⟨hsa x hx, hsb x hx, hsc x hx, hsd x hx⟩) hL hU

/-! ### The ledger interface -/

open PlanarCapCaseReduction PlanarCapPatterns in
/-- An actual normalized cover realizing the row D pattern (48,5) has strictly interior windows and
positive slopes satisfying the six numeric rows. -/
theorem deficit_obstruction (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1)
    (hh : Holds (SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (EdgeEmpty K (fun i => AffineMap.proj i) lo hi) ⟨48, 5⟩) :
    (∀ i, 0 < lo i ∧ hi i < 1) ∧
      ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ NumericRows lo hi a b c d := by
  have hm := CommonPointUnclipped.windows_strict_of_deficit K hK hbox hL hU lo hi horder hcover hdef
  refine ⟨hm, ?_⟩
  have hs4 := hh.1 4 (by decide)
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  have he2 := hh.2 2 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev] at hs4 hs5 he0 he2
  simp at hs4 hs5 he0 he2
  apply exists_numeric_rows K hK lo hi (fun i => (hm i).1) (fun i => (hm i).2) hL hU
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs5 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs4 x hx h2) (not_le.2 h1)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he0 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he2 x hx h1) (not_le.2 h2)

end Plank.Convex.RowDCapAlgebra

/-- info: 'Plank.Convex.RowDCapAlgebra.numeric_rows_of_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowDCapAlgebra.numeric_rows_of_supports

/-- info: 'Plank.Convex.RowDCapAlgebra.exists_numeric_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowDCapAlgebra.exists_numeric_rows

/-- info: 'Plank.Convex.RowDCapAlgebra.deficit_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowDCapAlgebra.deficit_obstruction
