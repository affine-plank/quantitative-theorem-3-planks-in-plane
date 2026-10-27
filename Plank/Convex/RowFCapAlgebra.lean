/- Row F of the planar cap ledger, pattern (32,11): the singleton cap (0+,1+) and the three mixed
caps (0+,1−), (2+,1−), (0−,1+) are empty. Four positive supports together with the plane relation,
evaluated at the six coordinate contacts, give six numeric inequalities in the window endpoints,
the four slopes, the plane coefficients and the centered plane offset. The contact `x2 = 0` has two
geometric cases according to which vertex of the support polygon the plane functional selects. -/
module
public import Plank.Convex.ConvexCellSeparation
public import Plank.Convex.CommonPointUnclipped
public import Plank.Convex.PlanarCapCaseReduction
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowFCapAlgebra
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- `m = A1 + A2 d`: the plane weight of coordinate 1 after eliminating coordinate 2 by the
support M21. -/
def mC (A : Point) (d : ℝ) : ℝ := A 1 + A 2 * d

/-- `K = A0 + e m`: the coefficient of `lo 0` and of `1 - hi 2`. -/
def kC (A : Point) (d e : ℝ) : ℝ := A 0 + e * mC A d

/-- `L = A0 c + m`: the coefficient of `lo 1`. -/
def lC (A : Point) (c d : ℝ) : ℝ := A 0 * c + mC A d

/-- The four supports of row F on a set, in absolute coordinates: the upper same-sign support
U01 and the mixed supports M01, M21, M10. -/
def Supports (S : Set Point) (lo hi : Point) (a c d e : ℝ) : Prop :=
  ∀ x ∈ S,
    x 0 + a * x 1 ≤ hi 0 + a * hi 1 ∧
    x 0 - c * x 1 ≤ hi 0 - c * lo 1 ∧
    x 2 - d * x 1 ≤ hi 2 - d * lo 1 ∧
    x 1 - e * x 0 ≤ hi 1 - e * lo 0

/-- The six numeric rows of row F, one per coordinate contact, in the order
`x0 = 0`, `x0 = 1`, `x1 = 0`, `x1 = 1`, `x2 = 0`, `x2 = 1`; `P` is the plane offset relative to
the lower corner and `C0, C1` the coefficients of the `x2 = 0` row. -/
def NumericRows (lo hi A : Point) (a c d e P C0 C1 : ℝ) : Prop :=
  kC A d e * lo 0 ≤ mC A d * (hi 1 - lo 1) - (P - A 2 * (hi 2 - lo 2)) ∧
  (1 - hi 0) * (a + c) ≤ a * c * (hi 1 - lo 1) ∧
  lC A c d * lo 1 ≤ A 0 * (hi 0 - lo 0) - (P - A 2 * (hi 2 - lo 2)) ∧
  (1 - hi 1) * (1 + a * e) ≤ e * (hi 0 - lo 0) ∧
  A 2 * lo 2 ≤ C0 * (hi 0 - lo 0) + C1 * (hi 1 - lo 1) - P ∧
  kC A d e * (1 - hi 2) ≤ e * d * (P - A 2 * (hi 2 - lo 2)) + A 0 * d * (hi 1 - lo 1)

/-- The rows with the `x2 = 0` coefficients of the vertex U01 ∩ M01 when `A1 ≤ a A0`, and of the
vertex U01 ∩ M10 when `a A0 ≤ A1`. -/
def CaseRows (lo hi A : Point) (a c d e P : ℝ) : Prop :=
  (A 1 ≤ a * A 0 ∧ NumericRows lo hi A a c d e P (A 0) (a * (A 0 * c + A 1) / (a + c))) ∨
  (a * A 0 ≤ A 1 ∧ NumericRows lo hi A a c d e P ((A 0 + e * A 1) / (1 + a * e)) (A 1))

/-- Supports and the centered plane relation at the six coordinate contacts imply the rows; each
row is a nonnegative combination of the supports at one contact plus a multiple of the plane. -/
theorem numeric_rows_of_supports (S : Set Point) (lo hi A : Point) (a c d e P : ℝ)
    (hA : ∀ i, 0 < A i) (ha : 0 < a) (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hS : Supports S lo hi a c d e)
    (hplane : ∀ x ∈ S, ∑ i, A i * (x i - lo i) = P)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1) :
    CaseRows lo hi A a c d e P := by
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  have hm : 0 ≤ A 1 + A 2 * d := add_nonneg hA1.le (mul_nonneg hA2.le hd.le)
  -- contact x0 = 0: m·M10 + A2·M21 + plane
  have r1 : kC A d e * lo 0 ≤ mC A d * (hi 1 - lo 1) - (P - A 2 * (hi 2 - lo 2)) := by
    obtain ⟨x, hx, h0⟩ := hL 0
    obtain ⟨_, _, hM21, hM10⟩ := hS x hx
    have hp := hplane x hx
    rw [Fin.sum_univ_three] at hp
    rw [h0] at hM10 hp
    have h1 := mul_le_mul_of_nonneg_left hM10 hm
    have h2 := mul_le_mul_of_nonneg_left hM21 hA2.le
    unfold kC mC
    nlinarith [h1, h2, hp]
  -- contact x0 = 1: c·U01 + a·M01
  have r2 : (1 - hi 0) * (a + c) ≤ a * c * (hi 1 - lo 1) := by
    obtain ⟨x, hx, h0⟩ := hU 0
    obtain ⟨hU01, hM01, _, _⟩ := hS x hx
    rw [h0] at hU01 hM01
    have h1 := mul_le_mul_of_nonneg_left hU01 hc.le
    have h2 := mul_le_mul_of_nonneg_left hM01 ha.le
    nlinarith [h1, h2]
  -- contact x1 = 0: A0·M01 + A2·M21 + plane
  have r3 : lC A c d * lo 1 ≤ A 0 * (hi 0 - lo 0) - (P - A 2 * (hi 2 - lo 2)) := by
    obtain ⟨x, hx, h1⟩ := hL 1
    obtain ⟨_, hM01, hM21, _⟩ := hS x hx
    have hp := hplane x hx
    rw [Fin.sum_univ_three] at hp
    rw [h1] at hM01 hM21 hp
    have h2 := mul_le_mul_of_nonneg_left hM01 hA0.le
    have h3 := mul_le_mul_of_nonneg_left hM21 hA2.le
    unfold lC mC
    nlinarith [h2, h3, hp]
  -- contact x1 = 1: e·U01 + M10
  have r4 : (1 - hi 1) * (1 + a * e) ≤ e * (hi 0 - lo 0) := by
    obtain ⟨x, hx, h1⟩ := hU 1
    obtain ⟨hU01, _, _, hM10⟩ := hS x hx
    rw [h1] at hU01 hM10
    have h2 := mul_le_mul_of_nonneg_left hU01 he.le
    nlinarith [h2, hM10]
  -- contact x2 = 1: A0 d·M10 + (A0 + e A1)·M21 − e d·plane
  have r6 : kC A d e * (1 - hi 2) ≤
      e * d * (P - A 2 * (hi 2 - lo 2)) + A 0 * d * (hi 1 - lo 1) := by
    obtain ⟨x, hx, h2⟩ := hU 2
    obtain ⟨_, _, hM21, hM10⟩ := hS x hx
    have hp := hplane x hx
    rw [Fin.sum_univ_three] at hp
    rw [h2] at hM21 hp
    have h1 := mul_le_mul_of_nonneg_left hM10 (mul_nonneg hA0.le hd.le)
    have h3 := mul_le_mul_of_nonneg_left hM21 (add_nonneg hA0.le (mul_nonneg he.le hA1.le))
    have hp' : e * d * (A 0 * (x 0 - lo 0) + A 1 * (x 1 - lo 1) + A 2 * (1 - lo 2)) = e * d * P := by
      rw [hp]
    unfold kC mC
    nlinarith [h1, h3, hp']
  -- contact x2 = 0, vertex U01 ∩ M01: (A1 + A0 c)·U01 + (a A0 − A1)·M01 + (a + c)·plane
  have r5a (hcase : A 1 ≤ a * A 0) : A 2 * lo 2 ≤
      A 0 * (hi 0 - lo 0) + a * (A 0 * c + A 1) / (a + c) * (hi 1 - lo 1) - P := by
    obtain ⟨x, hx, h2⟩ := hL 2
    obtain ⟨hU01, hM01, _, _⟩ := hS x hx
    have hp := hplane x hx
    rw [Fin.sum_univ_three] at hp
    rw [h2] at hp
    have hac : 0 < a + c := add_pos ha hc
    have h1 := mul_le_mul_of_nonneg_left hU01 (add_nonneg hA1.le (mul_nonneg hA0.le hc.le))
    have h3 := mul_le_mul_of_nonneg_left hM01 (sub_nonneg.2 hcase)
    have key : (A 2 * lo 2 - A 0 * (hi 0 - lo 0) + P) * (a + c) ≤
        a * (A 0 * c + A 1) * (hi 1 - lo 1) := by
      nlinarith [h1, h3, hp]
    have h4 := (le_div_iff₀ hac).2 key
    have h5 : a * (A 0 * c + A 1) / (a + c) * (hi 1 - lo 1) =
        a * (A 0 * c + A 1) * (hi 1 - lo 1) / (a + c) := by ring
    linarith [h4, h5]
  -- contact x2 = 0, vertex U01 ∩ M10: (A0 + e A1)·U01 + (A1 − a A0)·M10 + (1 + a e)·plane
  have r5b (hcase : a * A 0 ≤ A 1) : A 2 * lo 2 ≤
      (A 0 + e * A 1) / (1 + a * e) * (hi 0 - lo 0) + A 1 * (hi 1 - lo 1) - P := by
    obtain ⟨x, hx, h2⟩ := hL 2
    obtain ⟨hU01, _, _, hM10⟩ := hS x hx
    have hp := hplane x hx
    rw [Fin.sum_univ_three] at hp
    rw [h2] at hp
    have hae : 0 < 1 + a * e := by positivity
    have h1 := mul_le_mul_of_nonneg_left hU01 (add_nonneg hA0.le (mul_nonneg he.le hA1.le))
    have h3 := mul_le_mul_of_nonneg_left hM10 (sub_nonneg.2 hcase)
    have key : (A 2 * lo 2 - A 1 * (hi 1 - lo 1) + P) * (1 + a * e) ≤
        (A 0 + e * A 1) * (hi 0 - lo 0) := by
      nlinarith [h1, h3, hp]
    have h4 := (le_div_iff₀ hae).2 key
    have h5 : (A 0 + e * A 1) / (1 + a * e) * (hi 0 - lo 0) =
        (A 0 + e * A 1) * (hi 0 - lo 0) / (1 + a * e) := by ring
    linarith [h4, h5]
  rcases le_total (A 1) (a * A 0) with hcase | hcase
  · exact Or.inl ⟨hcase, r1, r2, r3, r4, r5a hcase, r6⟩
  · exact Or.inr ⟨hcase, r1, r2, r3, r4, r5b hcase, r6⟩

/-! ### Positive supports from the four empty caps -/

/-- The four empty caps of row F on a convex set lying on a positive plane, with the six
coordinate contacts, yield positive slopes whose supports hold on the whole convex set,
hence the case rows. The plane offset `P` is measured from the lower corner. -/
theorem exists_numeric_rows (K : Set Point) (hK : Convex ℝ K) (lo hi A : Point) (P : ℝ)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (hA : ∀ i, 0 < A i) (hplane : ∀ x ∈ K, ∑ i, A i * (x i - lo i) = P)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1)
    (hmix21 : ¬ ∃ x ∈ K, hi 2 < x 2 ∧ x 1 < lo 1)
    (hmix10 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ hi 1 < x 1) :
    ∃ a c d e : ℝ, 0 < a ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ CaseRows lo hi A a c d e P := by
  obtain ⟨a, ha, hsa⟩ := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (hi 1) (hhi 0) (hhi 1)
    (hU 0) (hU 1) hcapU01
  obtain ⟨c, hc, hsc⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 0) (AffineMap.proj 1) (hi 0) (lo 1) (hhi 0) (hlo 1)
    (hU 0) (hL 1) hmix01
  obtain ⟨d, hd, hsd⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 2) (AffineMap.proj 1) (hi 2) (lo 1) (hhi 2) (hlo 1)
    (hU 2) (hL 1) hmix21
  obtain ⟨e, he, hse⟩ := ConvexCellSeparation.exists_mixed_support K hK
    (AffineMap.proj 1) (AffineMap.proj 0) (hi 1) (lo 0) (hhi 1) (hlo 0)
    (hU 1) (hL 0) (fun ⟨x, hx, h1, h2⟩ => hmix10 ⟨x, hx, h2, h1⟩)
  refine ⟨a, c, d, e, ha, hc, hd, he, ?_⟩
  exact numeric_rows_of_supports K lo hi A a c d e P hA ha hc hd he
    (fun x hx => ⟨hsa x hx, hsc x hx, hsd x hx, hse x hx⟩) hplane hL hU

/-! ### The ledger interface -/

open PlanarCapCaseReduction PlanarCapPatterns in
/-- An actual normalized cover on a positive plane realizing the row F pattern (32,11) has
strictly interior windows, a nonnegative centered plane offset (from a point of `K` in all three
windows) and positive slopes satisfying the case rows. -/
theorem deficit_obstruction (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1)
    (hh : Holds (SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (EdgeEmpty K (fun i => AffineMap.proj i) lo hi) ⟨32, 11⟩) :
    (∀ i, 0 < lo i ∧ hi i < 1) ∧ 0 ≤ D - ∑ i, A i * lo i ∧
      ∃ a c d e : ℝ, 0 < a ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧
        CaseRows lo hi A a c d e (D - ∑ i, A i * lo i) := by
  have hm := CommonPointUnclipped.windows_strict_of_deficit K hK hbox hL hU lo hi horder hcover hdef
  have hcentered : ∀ x ∈ K, ∑ i, A i * (x i - lo i) = D - ∑ i, A i * lo i := by
    intro x hx
    rw [← hplane x hx, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  obtain ⟨z, hzK, hz⟩ :=
    CommonPointUnclipped.exists_common K hK hbox hL hU lo hi horder hcover hdef
  have hP : 0 ≤ D - ∑ i, A i * lo i := by
    rw [← hcentered z hzK]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hA i).le (sub_nonneg.2 (hz i).1))
  refine ⟨hm, hP, ?_⟩
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  have he1 := hh.2 1 (by decide)
  have he3 := hh.2 3 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev]
    at hs5 he0 he1 he3
  simp at hs5 he0 he1 he3
  apply exists_numeric_rows K hK lo hi A _ (fun i => (hm i).1) (fun i => (hm i).2) hL hU hA
    hcentered
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs5 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he0 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he1 x hx h2) (not_le.2 h1)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he3 x hx h1) (not_le.2 h2)

end Plank.Convex.RowFCapAlgebra

/-- info: 'Plank.Convex.RowFCapAlgebra.numeric_rows_of_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowFCapAlgebra.numeric_rows_of_supports

/-- info: 'Plank.Convex.RowFCapAlgebra.exists_numeric_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowFCapAlgebra.exists_numeric_rows

/-- info: 'Plank.Convex.RowFCapAlgebra.deficit_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowFCapAlgebra.deficit_obstruction
