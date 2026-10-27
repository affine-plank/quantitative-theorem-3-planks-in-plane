/- Transfer coefficients for the all-singleton algebraic obstruction.
Opposite transfers contract, so a deficit forces a directed three-cycle. -/
module
public import Plank.Convex.SameSignCapAlgebra
public import Plank.Convex.WidthBudgets
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.SameSignCapTransfer
open scoped BigOperators
open SameSignCapAlgebra

@[simp] theorem prev_next (i : Fin 3) : prev (next i) = i := by fin_cases i <;> rfl

def lowerDen (a b : Point) (i : Fin 3) : ℝ :=
  1 + b i * a (next i) * b (prev i)

def upperDen (a b : Point) (i : Fin 3) : ℝ :=
  1 + a i * b (next i) * a (prev i)

def forward (a b : Point) (i : Fin 3) : ℝ :=
  b i / lowerDen a b i + a i / upperDen a b i

def reverse (a b : Point) (i : Fin 3) : ℝ :=
  b i * a (next i) / lowerDen a b i + a i * b (next i) / upperDen a b i

theorem lowerDen_pos (a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 3) : 0 < lowerDen a b i := by
  dsimp [lowerDen]
  exact add_pos zero_lt_one (mul_pos (mul_pos (hb i) (ha (next i))) (hb (prev i)))

theorem upperDen_pos (a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 3) : 0 < upperDen a b i := by
  dsimp [upperDen]
  exact add_pos zero_lt_one (mul_pos (mul_pos (ha i) (hb (next i))) (ha (prev i)))

/-- The two opposite-contact rows give a linear width budget after the
positive separator coefficients have been fixed. -/
theorem transfer_bound (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (i : Fin 3) :
    1 ≤ (hi i - lo i) +
      forward a b i * (hi (next i) - lo (next i)) +
      reverse a b i * (hi (prev i) - lo (prev i)) := by
  have hl := (le_div_iff₀ (lowerDen_pos a b ha hb i)).mpr (hrows i).2.2.2.2.1
  have hu := (le_div_iff₀ (upperDen_pos a b ha hb i)).mpr (hrows i).2.2.2.2.2
  calc
    1 = (hi i - lo i) + (lo i + (1 - hi i)) := by ring
    _ ≤ (hi i - lo i) +
        ((b i * (hi (next i) - lo (next i)) +
          b i * a (next i) * (hi (prev i) - lo (prev i))) / lowerDen a b i +
        (a i * (hi (next i) - lo (next i)) +
          a i * b (next i) * (hi (prev i) - lo (prev i))) / upperDen a b i) :=
      add_le_add_right (add_le_add hl hu) _
    _ = _ := by dsimp [forward, reverse]; ring

/-- A square measures the gap from reciprocity of a pair of transfers. -/
theorem pair_gap (x y p q : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp : 0 < p) (hq : 0 < q) :
    1 - (x / (1 + x * p) + y / (1 + y * q)) *
      (q / (1 + x * q) + p / (1 + y * p)) =
      (p * q * x * y - 1) ^ 2 /
        ((1 + x * p) * (1 + y * p) * (1 + x * q) * (1 + y * q)) := by
  have hxp : 1 + x * p ≠ 0 := ne_of_gt (by positivity)
  have hyp : 1 + y * p ≠ 0 := ne_of_gt (by positivity)
  have hxq : 1 + x * q ≠ 0 := ne_of_gt (by positivity)
  have hyq : 1 + y * q ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

theorem pair_product_le_one (x y p q : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hp : 0 < p) (hq : 0 < q) :
    (x / (1 + x * p) + y / (1 + y * q)) *
      (q / (1 + x * q) + p / (1 + y * p)) ≤ 1 := by
  have hn : 0 ≤ 1 - (x / (1 + x * p) + y / (1 + y * q)) *
      (q / (1 + x * q) + p / (1 + y * p)) := by
    rw [pair_gap x y p q hx hy hp hq]
    positivity
  linarith only [hn]

theorem pair_le_one (a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : Fin 3) : forward a b i * reverse a b (next i) ≤ 1 := by
  have hg := pair_product_le_one (b i) (a i) (a (next i) * b (prev i))
    (b (next i) * a (prev i)) (hb i) (ha i)
    (mul_pos (ha _) (hb _)) (mul_pos (hb _) (ha _))
  convert hg using 1
  simp only [forward, reverse, lowerDen, upperDen, next_next, prev_next]
  ring

/-- On three vertices, an outgoing edge at each vertex and no opposite
pair of edges force one of the two directed three-cycles. -/
theorem cycle_of_pair_bounds (f r : Point)
    (hp : ∀ i, f i * r (next i) ≤ 1)
    (hout : ∀ i, 1 < f i ∨ 1 < r i) :
    (∀ i, 1 < f i) ∨ (∀ i, 1 < r i) :=
  WidthBudgets.cycle_of_pair_bounds f r hp hout

/-- Any deficit in the eighteen rows forces all three forward transfers
above one, or all three reverse transfers above one. -/
theorem cycle_of_deficit (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (horder : ∀ i, lo i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1) :
    (∀ i, 1 < forward a b i) ∨ (∀ i, 1 < reverse a b i) := by
  apply cycle_of_pair_bounds _ _ (pair_le_one a b ha hb)
  intro i
  by_contra hn
  push Not at hn
  have hf := mul_le_mul_of_nonneg_right hn.1 (sub_nonneg.mpr (horder (next i)))
  have hr := mul_le_mul_of_nonneg_right hn.2 (sub_nonneg.mpr (horder (prev i)))
  have hs : (hi i - lo i) + (hi (next i) - lo (next i)) +
      (hi (prev i) - lo (prev i)) < 1 := by
    fin_cases i <;> simp [Fin.sum_univ_three, next, prev] at hdef ⊢ <;> linarith only [hdef]
  have ht := transfer_bound lo hi a b ha hb hrows i
  linarith only [hf, hr, hs, ht]

def slopeProduct (a b : Point) : ℝ := (∏ i, a i) * (∏ i, b i)

def mixedSum (a b : Point) : ℝ := ∑ i, a i * b (next i) * a (prev i)

def denProduct (a b : Point) : ℝ := ∏ i, lowerDen a b i * upperDen a b i

theorem denProduct_pos (a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    0 < denProduct a b :=
  Finset.prod_pos fun i _ => mul_pos (lowerDen_pos a b ha hb i) (upperDen_pos a b ha hb i)

private theorem prod_forward_eq (a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (∏ i, forward a b i) =
      (∏ i, (b i * upperDen a b i + a i * lowerDen a b i)) / denProduct a b := by
  calc
    _ = ∏ i, (b i * upperDen a b i + a i * lowerDen a b i) /
        (lowerDen a b i * upperDen a b i) := by
      apply Finset.prod_congr rfl
      intro i _
      dsimp [forward]
      field_simp [ne_of_gt (lowerDen_pos a b ha hb i), ne_of_gt (upperDen_pos a b ha hb i)]
    _ = _ := Finset.prod_div_distrib _ _

private theorem prod_reverse_eq (a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    (∏ i, reverse a b i) =
      (∏ i, (b i * a (next i) * upperDen a b i +
        a i * b (next i) * lowerDen a b i)) / denProduct a b := by
  calc
    _ = ∏ i, (b i * a (next i) * upperDen a b i +
        a i * b (next i) * lowerDen a b i) /
        (lowerDen a b i * upperDen a b i) := by
      apply Finset.prod_congr rfl
      intro i _
      dsimp [reverse]
      field_simp [ne_of_gt (lowerDen_pos a b ha hb i), ne_of_gt (upperDen_pos a b ha hb i)]
    _ = _ := Finset.prod_div_distrib _ _

/-- The product of forward transfers has a polynomial gap with a fixed
sign whenever the product of the six slopes is at least one. -/
theorem forward_product_gap (a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    1 - (∏ i, forward a b i) = (slopeProduct a b - 1) *
      ((slopeProduct a b) ^ 2 - 1 +
        (slopeProduct a b + ∏ i, b i) * mixedSum a b +
        (slopeProduct a b + ∏ i, a i) * mixedSum b a +
        2 * slopeProduct a b + (∏ i, a i) + (∏ i, b i)) / denProduct a b := by
  rw [prod_forward_eq a b ha hb]
  apply (eq_div_iff (ne_of_gt (denProduct_pos a b ha hb))).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt (denProduct_pos a b ha hb))]
  simp only [denProduct, slopeProduct, mixedSum, Fin.prod_univ_three, Fin.sum_univ_three,
    lowerDen, upperDen, next, prev, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- The reverse product has the opposite slope-product orientation. -/
theorem reverse_product_gap (a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    1 - (∏ i, reverse a b i) = (1 - slopeProduct a b) *
      (1 - (slopeProduct a b) ^ 2 +
        ((∏ i, b i) + 1) * mixedSum a b +
        ((∏ i, a i) + 1) * mixedSum b a +
        slopeProduct a b * ((∏ i, a i) + (∏ i, b i) + 2)) / denProduct a b := by
  rw [prod_reverse_eq a b ha hb]
  apply (eq_div_iff (ne_of_gt (denProduct_pos a b ha hb))).mpr
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt (denProduct_pos a b ha hb))]
  simp only [denProduct, slopeProduct, mixedSum, Fin.prod_univ_three, Fin.sum_univ_three,
    lowerDen, upperDen, next, prev, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

theorem forward_product_le_one (a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hp : 1 ≤ slopeProduct a b) :
    (∏ i, forward a b i) ≤ 1 := by
  have hA : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have hB : 0 < ∏ i, b i := Finset.prod_pos fun i _ => hb i
  have hS : 0 ≤ mixedSum a b := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (ha i).le (hb (next i)).le) (ha (prev i)).le
  have hT : 0 ≤ mixedSum b a := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (hb i).le (ha (next i)).le) (hb (prev i)).le
  have hP : 0 < slopeProduct a b := lt_of_lt_of_le zero_lt_one hp
  have hsq : 0 ≤ (slopeProduct a b) ^ 2 - 1 := by nlinarith only [hp]
  have hgap : 0 ≤ 1 - (∏ i, forward a b i) := by
    rw [forward_product_gap a b ha hb]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hp) (by positivity))
      (denProduct_pos a b ha hb).le
  linarith only [hgap]

theorem reverse_product_le_one (a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hp : slopeProduct a b ≤ 1) :
    (∏ i, reverse a b i) ≤ 1 := by
  have hA : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  have hB : 0 < ∏ i, b i := Finset.prod_pos fun i _ => hb i
  have hS : 0 ≤ mixedSum a b := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (ha i).le (hb (next i)).le) (ha (prev i)).le
  have hT : 0 ≤ mixedSum b a := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (hb i).le (ha (next i)).le) (hb (prev i)).le
  have hP : 0 < slopeProduct a b := mul_pos hA hB
  have hsq : 0 ≤ 1 - (slopeProduct a b) ^ 2 := by nlinarith only [hp, hP]
  have hgap : 0 ≤ 1 - (∏ i, reverse a b i) := by
    rw [reverse_product_gap a b ha hb]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hp) (by positivity))
      (denProduct_pos a b ha hb).le
  linarith only [hgap]

private theorem prod_gt_one (f : Point) (hf : ∀ i, 1 < f i) : 1 < ∏ i, f i := by
  simp only [Fin.prod_univ_three]
  exact one_lt_mul_of_lt_of_le
    (one_lt_mul_of_lt_of_le (hf 0) (hf 1).le) (hf 2).le

/-- The two possible cycles lie on opposite sides of the balanced
separator product. Neither the orientation nor the product sign is arbitrary. -/
theorem oriented_cycle_of_deficit (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (horder : ∀ i, lo i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1) :
    ((∀ i, 1 < forward a b i) ∧ slopeProduct a b < 1) ∨
      ((∀ i, 1 < reverse a b i) ∧ 1 < slopeProduct a b) := by
  rcases cycle_of_deficit lo hi a b ha hb hrows horder hdef with hf | hr
  · refine Or.inl ⟨hf, ?_⟩
    by_contra hn
    exact (not_lt_of_ge (forward_product_le_one a b ha hb (le_of_not_gt hn)))
      (prod_gt_one _ hf)
  · refine Or.inr ⟨hr, ?_⟩
    by_contra hn
    exact (not_lt_of_ge (reverse_product_le_one a b ha hb (le_of_not_gt hn)))
      (prod_gt_one _ hr)

/-- Balanced positive separators rule out a deficit using only the
eighteen necessary rows, with no geometric plane assumption. -/
theorem width_bound_of_balanced (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (horder : ∀ i, lo i ≤ hi i)
    (hp : slopeProduct a b = 1) : 1 ≤ ∑ i, (hi i - lo i) := by
  by_contra hn
  rcases oriented_cycle_of_deficit lo hi a b ha hb hrows horder (lt_of_not_ge hn) with
    ⟨_, hlt⟩ | ⟨_, hgt⟩
  · exact (ne_of_lt hlt) hp
  · exact (ne_of_gt hgt) hp

/-- The balanced algebraic result applies to supports at the six actual
coordinate contacts. Convexity and a plane relation are unnecessary here. -/
theorem width_bound_of_balanced_supports (S : Set Point)
    (hbox : ∀ x ∈ S, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1)
    (lo hi a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (horder : ∀ i, lo i ≤ hi i)
    (hupper : UpperSupports S hi a) (hlower : LowerSupports S lo b)
    (hp : slopeProduct a b = 1) : 1 ≤ ∑ i, (hi i - lo i) :=
  width_bound_of_balanced lo hi a b ha hb
    (numeric_rows_of_supports S hbox hL hU lo hi a b ha hb hupper hlower) horder hp

/-- An actual all-singleton deficient cover gives one of the two oriented
algebraic obstructions, and cannot admit balanced separators. -/
theorem deficit_obstruction (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1)
    (hsingle : ∀ e, PlanarCapCaseReduction.SingleEmpty K (fun i => AffineMap.proj i) lo hi e) :
    (∀ i, 0 < lo i ∧ hi i < 1) ∧ ∃ a b : Point,
      (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧ NumericRows lo hi a b ∧
      (((∀ i, 1 < forward a b i) ∧ slopeProduct a b < 1) ∨
        ((∀ i, 1 < reverse a b i) ∧ 1 < slopeProduct a b)) := by
  obtain ⟨hm, a, b, ha, hb, hrows⟩ := SameSignCapAlgebra.deficit_obstruction K hK hbox hL hU
    lo hi horder hcover hdef hsingle
  exact ⟨hm, a, b, ha, hb, hrows, oriented_cycle_of_deficit lo hi a b ha hb hrows horder hdef⟩

end Plank.Convex.SameSignCapTransfer

/-- info: 'Plank.Convex.SameSignCapTransfer.pair_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTransfer.pair_gap

/-- info: 'Plank.Convex.SameSignCapTransfer.cycle_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTransfer.cycle_of_deficit

/-- info: 'Plank.Convex.SameSignCapTransfer.forward_product_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTransfer.forward_product_gap

/-- info: 'Plank.Convex.SameSignCapTransfer.reverse_product_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTransfer.reverse_product_gap

/-- info: 'Plank.Convex.SameSignCapTransfer.oriented_cycle_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTransfer.oriented_cycle_of_deficit

/-- info: 'Plank.Convex.SameSignCapTransfer.width_bound_of_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTransfer.width_bound_of_balanced

/-- info: 'Plank.Convex.SameSignCapTransfer.width_bound_of_balanced_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTransfer.width_bound_of_balanced_supports

/-- info: 'Plank.Convex.SameSignCapTransfer.deficit_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapTransfer.deficit_obstruction
