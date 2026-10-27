/- Equality in the separated mixed-cap case forces an axial contact pair. -/
module
public import Plank.Convex.RowDCapAlgebra
public import Plank.Convex.PlanarTight.BudgetEquality
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.RowD
open RowDCapAlgebra

/-- The four row-D supports have three saturated contact rows at equality.
The statement retains the polynomial form and needs no plane equation. -/
theorem saturated_rows (lo hi : Point) (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hwidth : ∀ i, lo i < hi i) (hsum : ∑ i, (hi i - lo i) = 1)
    (hrows : NumericRows lo hi a b c d) :
    lo 0 * (b + d) = hi 2 - lo 2 ∧
    lo 1 * c * (b + d) = (b + d) * (hi 0 - lo 0) + (hi 2 - lo 2) ∧
    (1 - hi 1) * a * (b + d) = (b + d) * (hi 0 - lo 0) + (hi 2 - lo 2) := by
  obtain ⟨h0, h0', h1, h1', h2, h2'⟩ := hrows
  let A := a + c
  let B := b + d
  let w : Point := fun i => hi i - lo i
  let coeff : Point := ![A * B, a * c * B, A]
  let N := A * B * w 0 + a * c * B * w 1 + A * w 2
  have hA : 0 < A := add_pos ha hc
  have hB : 0 < B := add_pos hb hd
  have hN0 : A * B ≤ N := by
    have hleft := mul_le_mul_of_nonneg_left h0 hA.le
    have hright := mul_le_mul_of_nonneg_left h0' hB.le
    dsimp [N, A, B, w] at *
    nlinarith only [hleft, hright]
  have hN1 : a * c * B ≤ N := by
    have hleft := mul_le_mul_of_nonneg_left h1 ha.le
    have hright := mul_le_mul_of_nonneg_left h1' hc.le
    dsimp [N, A, B, w] at *
    nlinarith only [hleft, hright]
  have hN2 : A ≤ N := by
    dsimp [N, A, B, w] at *
    nlinarith only [h2, h2']
  have heqN : (∑ i, coeff i * w i) = N := by
    simp only [Fin.sum_univ_three]
    rfl
  have heq : ∀ i, coeff i = N := by
    rw [← heqN]
    apply BudgetEquality.coefficients_eq w coeff (fun i => sub_pos.mpr (hwidth i)) hsum
    intro i
    rw [heqN]
    fin_cases i
    · exact hN0
    · exact hN1
    · exact hN2
  have he0 : A * B = N := heq 0
  have he1 : a * c * B = N := heq 1
  have hs0 := BudgetEquality.split_eq A B _ _ _ _ hA hB h0 h0' (by
    dsimp [N, A, B, w] at he0 ⊢
    nlinarith only [he0])
  have hs1 := BudgetEquality.split_eq a c _ _ _ _ ha hc h1 h1' (by
    dsimp [N, A, B, w] at he1 ⊢
    nlinarith only [he1])
  exact ⟨hs0.1, hs1.1, hs1.2⟩

/-- At positive-width equality, the two extrema of coordinate one have the
same other coordinates. Such an axial segment cannot lie in a positive plane. -/
theorem axial_contacts (K : Set Point)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hwidth : ∀ i, lo i < hi i) (hsum : ∑ i, (hi i - lo i) = 1)
    (hsupports : Supports K lo hi a b c d) :
    ∃ L ∈ K, ∃ U ∈ K,
      L 0 = 0 ∧ U 0 = 0 ∧ L 1 = 0 ∧ U 1 = 1 ∧ L 2 = U 2 := by
  have hrows := numeric_rows_of_supports K lo hi a b c d ha hb hc hd hsupports hL hU
  obtain ⟨he0, heL, heU⟩ := saturated_rows lo hi a b c d ha hb hc hd hwidth hsum hrows
  have hB : 0 < b + d := add_pos hb hd
  have hcornerL : hi 0 - c * lo 1 = 0 := by
    nlinarith only [he0, heL, hB]
  have hcornerU : hi 0 + a * hi 1 = a := by
    nlinarith only [he0, heU, hB]
  obtain ⟨L, hL, hL1⟩ := hL 1
  obtain ⟨U, hU, hU1⟩ := hU 1
  have hSL := hsupports L hL
  have hSU := hsupports U hU
  have hL0 : L 0 = 0 := by
    have h := hSL.2.2.1
    rw [hL1, mul_zero, sub_zero, hcornerL] at h
    exact le_antisymm h (hbox L hL 0).1
  have hU0 : U 0 = 0 := by
    have h := hSU.1
    rw [hU1, mul_one, hcornerU] at h
    linarith only [h, (hbox U hU 0).1]
  refine ⟨L, hL, U, hU, hL0, hU0, hL1, hU1, ?_⟩
  have hLlo := hSL.2.1
  have hLhi := hSL.2.2.2
  have hUlo := hSU.2.1
  have hUhi := hSU.2.2.2
  rw [hL0, mul_zero, add_zero] at hLlo
  rw [hL0, mul_zero, sub_zero] at hLhi
  rw [hU0, mul_zero, add_zero] at hUlo
  rw [hU0, mul_zero, sub_zero] at hUhi
  nlinarith only [he0, hLlo, hLhi, hUlo, hUhi]

/-- Positive row-D equality is incompatible with a plane whose normal has
a nonzero coefficient in coordinate one. In particular it is impossible
for the positive plane arising from three distinct planar directions. -/
theorem not_tight_on_plane (K : Set Point)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hwidth : ∀ i, lo i < hi i) (hsupports : Supports K lo hi a b c d)
    (A : Point) (D : ℝ) (hA : A 1 ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D) :
    (∑ i, (hi i - lo i)) ≠ 1 := by
  intro hsum
  obtain ⟨L, hL, U, hU, hL0, hU0, hL1, hU1, h2⟩ :=
    axial_contacts K hbox hL hU lo hi a b c d ha hb hc hd hwidth hsum hsupports
  have hLP := hplane L hL
  have hUP := hplane U hU
  simp only [Fin.sum_univ_three, hL0, hU0, hL1, hU1, mul_zero, mul_one,
    zero_add, h2] at hLP hUP
  exact hA (by linarith only [hLP, hUP])

/-- The separated mixed-cap pattern cannot occur in a tight cover with
three positive strictly internal windows on a positive plane. -/
theorem not_tight_of_caps (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hwidth : ∀ i, lo i < hi i)
    (hcapU01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ hi 1 < x 1)
    (hcapL02 : ¬ ∃ x ∈ K, x 0 < lo 0 ∧ x 2 < lo 2)
    (hmix01 : ¬ ∃ x ∈ K, hi 0 < x 0 ∧ x 1 < lo 1)
    (hmix20 : ¬ ∃ x ∈ K, hi 2 < x 2 ∧ x 0 < lo 0)
    (A : Point) (D : ℝ) (hA : A 1 ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, A i * x i = D) :
    (∑ i, (hi i - lo i)) ≠ 1 := by
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
  exact not_tight_on_plane K hbox hL hU lo hi a b c d ha hb hc hd hwidth
    (fun x hx => ⟨hsa x hx, hsb x hx, hsc x hx, hsd x hx⟩) A D hA hplane

end Plank.Convex.PlanarTight.RowD

/-- info: 'Plank.Convex.PlanarTight.RowD.saturated_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowD.saturated_rows

/-- info: 'Plank.Convex.PlanarTight.RowD.axial_contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowD.axial_contacts

/-- info: 'Plank.Convex.PlanarTight.RowD.not_tight_on_plane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowD.not_tight_on_plane

/-- info: 'Plank.Convex.PlanarTight.RowD.not_tight_of_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.RowD.not_tight_of_caps
