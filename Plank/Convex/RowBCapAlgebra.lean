/- Row B of the planar cap ledger, pattern (60,1): the four singleton caps (0−,1−), (1+,2+), (0−,2−),
(0+,1+) and the mixed cap (0+,1−) are empty. Five positive supports at the six coordinate contacts
give six numeric inequalities in the window endpoints and the five slopes. -/
module
public import Plank.Convex.ConvexCellSeparation
public import Plank.Convex.CommonPointUnclipped
public import Plank.Convex.PlanarCapCaseReduction
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowBCapAlgebra
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- The five supports of row B on a set: two upper same-sign supports, two lower same-sign
supports and one mixed support. -/
def Supports (S : Set Point) (lo hi : Point) (a0 a1 b0 b2 c : ℝ) : Prop :=
  ∀ x ∈ S,
    x 0 + a0 * x 1 ≤ hi 0 + a0 * hi 1 ∧
    x 1 + a1 * x 2 ≤ hi 1 + a1 * hi 2 ∧
    lo 0 + b0 * lo 1 ≤ x 0 + b0 * x 1 ∧
    lo 2 + b2 * lo 0 ≤ x 2 + b2 * x 0 ∧
    x 0 - c * x 1 ≤ hi 0 - c * lo 1

/-- The six numeric rows of row B, one per coordinate contact, in the order
`x0 = 0`, `x0 = 1`, `x1 = 0`, `x1 = 1`, `x2 = 0`, `x2 = 1`. -/
def NumericRows (lo hi : Point) (a0 a1 b0 b2 c : ℝ) : Prop :=
  lo 0 * (1 + b0 * a1 * b2) ≤ b0 * (hi 1 - lo 1) + b0 * a1 * (hi 2 - lo 2) ∧
  (1 - hi 0) * (a0 + c) ≤ a0 * c * (hi 1 - lo 1) ∧
  lo 1 * (b0 + c) ≤ hi 0 - lo 0 ∧
  (1 - hi 1) * (1 + a0 * a1 * b2) ≤ a1 * (hi 2 - lo 2) + a1 * b2 * (hi 0 - lo 0) ∧
  lo 2 * (a0 + c) ≤ b2 * (a0 + c) * (hi 0 - lo 0) + a0 * b2 * c * (hi 1 - lo 1) ∧
  (1 - hi 2) * a1 * (b0 + c) ≤ (b0 + c) * (hi 1 - lo 1) + (hi 0 - lo 0)

/-- Supports at the six coordinate contacts imply the six numeric rows; each row is a
nonnegative combination of the supports at one contact. -/
theorem numeric_rows_of_supports (S : Set Point) (lo hi : Point) (a0 a1 b0 b2 c : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (hb0 : 0 < b0) (hb2 : 0 < b2) (hc : 0 < c)
    (hS : Supports S lo hi a0 a1 b0 b2 c)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1) :
    NumericRows lo hi a0 a1 b0 b2 c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- contact x0 = 0: L01 gives b0 * y ≥ l0 + b0 l1, L20 gives z ≥ l2 + b2 l0, U12 bounds y above
    obtain ⟨x, hx, h0⟩ := hL 0
    obtain ⟨_, hU12, hL01, hL20, _⟩ := hS x hx
    rw [h0] at hL01 hL20
    have h1 := mul_le_mul_of_nonneg_left hL20 (mul_pos hb0 ha1).le
    have h2 := mul_le_mul_of_nonneg_left hU12 hb0.le
    nlinarith [h1, h2]
  · -- contact x0 = 1: U01 bounds y above, M01 bounds y below
    obtain ⟨x, hx, h0⟩ := hU 0
    obtain ⟨hU01, _, _, _, hM01⟩ := hS x hx
    rw [h0] at hU01 hM01
    have h1 := mul_le_mul_of_nonneg_left hU01 hc.le
    have h2 := mul_le_mul_of_nonneg_left hM01 ha0.le
    nlinarith [h1, h2]
  · -- contact x1 = 0: L01 bounds x below, M01 bounds x above
    obtain ⟨x, hx, h1⟩ := hL 1
    obtain ⟨_, _, hL01, _, hM01⟩ := hS x hx
    rw [h1] at hL01 hM01
    linarith
  · -- contact x1 = 1: U01 bounds x above, U12 bounds z above, L20 bounds z + b2 x below
    obtain ⟨x, hx, h1⟩ := hU 1
    obtain ⟨hU01, hU12, _, hL20, _⟩ := hS x hx
    rw [h1] at hU01 hU12
    have h2 := mul_le_mul_of_nonneg_left hU01 (mul_pos ha1 hb2).le
    have h3 := mul_le_mul_of_nonneg_left hL20 ha1.le
    nlinarith [h2, h3, hU12]
  · -- contact x2 = 0: L20 bounds x below, c·U01 + a0·M01 bounds x above
    obtain ⟨x, hx, h2⟩ := hL 2
    obtain ⟨hU01, _, _, hL20, hM01⟩ := hS x hx
    rw [h2] at hL20
    have h3 := mul_le_mul_of_nonneg_left hU01 hc.le
    have h4 := mul_le_mul_of_nonneg_left hM01 ha0.le
    have hsum : (a0 + c) * x 0 ≤ (a0 + c) * hi 0 + a0 * c * (hi 1 - lo 1) := by linarith
    have h5 := mul_le_mul_of_nonneg_left hL20 (add_pos ha0 hc).le
    have h6 := mul_le_mul_of_nonneg_left hsum hb2.le
    nlinarith [h5, h6]
  · -- contact x2 = 1: U12 bounds y above, L01 and M01 bound x + b0 y from both sides
    obtain ⟨x, hx, h2⟩ := hU 2
    obtain ⟨_, hU12, hL01, _, hM01⟩ := hS x hx
    rw [h2] at hU12
    have h3 := mul_le_mul_of_nonneg_left hU12 (add_pos hb0 hc).le
    nlinarith [h3, hL01, hM01]

/-! ### Positive supports from the five empty caps -/

/-- The five empty caps of row B on a convex set with the six coordinate contacts yield positive
slopes whose supports hold on the whole convex set, hence the numeric rows. -/
theorem exists_numeric_rows (K : Set Point) (hK : Convex ℝ K) (lo hi : Point)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (hcap01 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 1 < lo 1)
    (hcap12 : ¬ ∃ x ∈ K, hi 1 < x 1 ∧ hi 2 < x 2)
    (hcap20 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 2 < lo 2)
    (hcap01' : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hmix : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1) :
    ∃ a0 a1 b0 b2 c : ℝ, 0 < a0 ∧ 0 < a1 ∧ 0 < b0 ∧ 0 < b2 ∧ 0 < c ∧
      NumericRows lo hi a0 a1 b0 b2 c := by
  obtain ⟨a0, ha0, hsa0⟩ := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (hi 1) (hhi 0) (hhi 1)
    (hU 0) (hU 1) hcap01'
  obtain ⟨a1, ha1, hsa1⟩ := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj 1) (AffineMap.proj 2) (hi 1) (hi 2) (hhi 1) (hhi 2)
    (hU 1) (hU 2) hcap12
  obtain ⟨b0, hb0, hsb0⟩ := ConvexCellSeparation.exists_lower_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (lo 0) (lo 1) (hlo 0) (hlo 1)
    (hL 0) (hL 1) hcap01
  obtain ⟨b2, hb2, hsb2⟩ := ConvexCellSeparation.exists_lower_support K hK
    (AffineMap.proj 2) (AffineMap.proj 0) (lo 2) (lo 0) (hlo 2) (hlo 0)
    (hL 2) (hL 0) (fun ⟨x, hx, h1, h2⟩ => hcap20 ⟨x, hx, h2, h1⟩)
  obtain ⟨c, hc, hsc⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (lo 1) (hhi 0) (hlo 1)
    (hU 0) (hL 1) hmix
  refine ⟨a0, a1, b0, b2, c, ha0, ha1, hb0, hb2, hc, ?_⟩
  exact numeric_rows_of_supports K lo hi a0 a1 b0 b2 c ha0 ha1 hb0 hb2 hc
    (fun x hx => ⟨hsa0 x hx, hsa1 x hx, hsb0 x hx, hsb2 x hx, hsc x hx⟩) hL hU

/-! ### The ledger interface -/

open PlanarCapCaseReduction PlanarCapPatterns in
/-- An actual normalized cover realizing the row B pattern (60,1) has strictly interior windows and
positive slopes satisfying the six numeric rows. -/
theorem deficit_obstruction (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1)
    (hh : Holds (SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (EdgeEmpty K (fun i => AffineMap.proj i) lo hi) ⟨60, 1⟩) :
    (∀ i, 0 < lo i ∧ hi i < 1) ∧
      ∃ a0 a1 b0 b2 c : ℝ, 0 < a0 ∧ 0 < a1 ∧ 0 < b0 ∧ 0 < b2 ∧ 0 < c ∧
        NumericRows lo hi a0 a1 b0 b2 c := by
  have hm := CommonPointUnclipped.windows_strict_of_deficit K hK hbox hL hU lo hi horder hcover hdef
  refine ⟨hm, ?_⟩
  have hs2 := hh.1 2 (by decide)
  have hs3 := hh.1 3 (by decide)
  have hs4 := hh.1 4 (by decide)
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev] at hs2 hs3 hs4 hs5 he0
  simp at hs2 hs3 hs4 hs5 he0
  apply exists_numeric_rows K hK lo hi (fun i => (hm i).1) (fun i => (hm i).2) hL hU
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs2 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs3 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs4 x hx h2) (not_le.2 h1)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs5 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he0 x hx h1) (not_le.2 h2)

end Plank.Convex.RowBCapAlgebra

/-- info: 'Plank.Convex.RowBCapAlgebra.numeric_rows_of_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowBCapAlgebra.numeric_rows_of_supports

/-- info: 'Plank.Convex.RowBCapAlgebra.exists_numeric_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowBCapAlgebra.exists_numeric_rows

/-- info: 'Plank.Convex.RowBCapAlgebra.deficit_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowBCapAlgebra.deficit_obstruction
