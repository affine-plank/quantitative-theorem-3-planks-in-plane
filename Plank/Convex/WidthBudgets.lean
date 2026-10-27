/- Width bounds from finite families of linear budgets. Common weighted sums,
product comparisons and acyclic coefficient graphs give sufficient conditions. -/
module
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.WellFounded
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.Push
@[expose] public section
set_option autoImplicit false

namespace Plank.Convex.WidthBudgets
open scoped BigOperators

/-- If each coefficient is bounded by the same positive weighted sum, the
nonnegative weights have total at least one. The coefficients may have either sign. -/
theorem width_bound_of_common_budget {ι : Type*} [Fintype ι] (w a : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hpos : 0 < ∑ i, a i * w i)
    (hbudget : ∀ i, a i ≤ ∑ j, a j * w j) : 1 ≤ ∑ i, w i := by
  have h : (∑ i, a i * w i) ≤ (∑ j, a j * w j) * ∑ i, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hbudget i) (hw i)
  nlinarith only [h, hpos]

/-- A product comparison for any finite family of budgets at least one.
The products omitting one factor are bounded by the full positive product. -/
theorem width_bound_of_product_comparison {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w d : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hd : ∀ i, 1 ≤ d i)
    (hcomp : (∏ i, d i) ≤ ∑ i, w i * ∏ j ∈ Finset.univ.erase i, d j) :
    1 ≤ ∑ i, w i := by
  have hP : 0 < ∏ i, d i :=
    Finset.prod_pos fun i _ => lt_of_lt_of_le zero_lt_one (hd i)
  apply width_bound_of_common_budget w (fun i => ∏ j ∈ Finset.univ.erase i, d j) hw
  · simpa only [mul_comm] using lt_of_lt_of_le hP hcomp
  · intro i
    have hi := Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.erase_subset i Finset.univ)
      (fun j _ => le_trans zero_le_one (hd j)) (fun j _ _ => hd j)
    simpa only [mul_comm] using hi.trans hcomp

/-- A single budget with every coefficient at most one bounds the total width. -/
theorem width_bound_of_bounded_row {ι : Type*} [Fintype ι] (w c : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hc : ∀ i, c i ≤ 1)
    (hbudget : 1 ≤ ∑ i, c i * w i) : 1 ≤ ∑ i, w i := by
  calc
    1 ≤ ∑ i, c i * w i := hbudget
    _ ≤ ∑ i, w i := Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hc i) (hw i)).trans_eq (one_mul _)

/-- Draw an arrow from row `i` to column `j` when its coefficient exceeds one.
If this graph is acyclic, a row with no outgoing arrows gives the width bound.
The reversed relation below makes such a row a minimal element. -/
theorem width_bound_of_acyclic_budgets {ι : Type*} [Fintype ι] [Nonempty ι]
    (w : ι → ℝ) (c : ι → ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hbudget : ∀ i, 1 ≤ ∑ j, c i j * w j)
    (hacyclic : ∀ i, ¬ Relation.TransGen (fun j i => 1 < c i j) i i) :
    1 ≤ ∑ i, w i := by
  let R : ι → ι → Prop := fun j i => 1 < c i j
  let : Std.Irrefl (Relation.TransGen R) := ⟨hacyclic⟩
  obtain ⟨i, _, hi⟩ := (Finite.wellFounded_of_trans_of_irrefl
    (Relation.TransGen R)).has_min Set.univ Set.univ_nonempty
  apply width_bound_of_bounded_row w (c i) hw _ (hbudget i)
  intro j
  exact le_of_not_gt (fun h => hi j (Set.mem_univ j) (Relation.TransGen.single h))

/-- The path bounds also imply the older cycle-product criterion. -/
theorem cycle_sum_bound_of_paths (f r : Fin 3 → ℝ) (hf0 : 0 ≤ f 0) (hr1 : 0 ≤ r 1)
    (hp0 : f 0 * r 1 ≤ 1) (hfp : f 1 * f 2 ≤ r 1) (hrp : r 0 * r 2 ≤ f 0) :
    (∏ i, f i) + (∏ i, r i) ≤ 2 := by
  have hF := mul_le_mul_of_nonneg_left hfp hf0
  have hR := mul_le_mul_of_nonneg_left hrp hr1
  simp only [Fin.prod_univ_three]
  nlinarith only [hF, hR, hp0]

/-- On three vertices, an outgoing edge at each vertex and no opposite
pair of edges force one of the two directed three-cycles. -/
theorem cycle_of_pair_bounds (f r : Fin 3 → ℝ)
    (hp : ∀ i, f i * r ((![1, 2, 0] : Fin 3 → Fin 3) i) ≤ 1)
    (hout : ∀ i, 1 < f i ∨ 1 < r i) :
    (∀ i, 1 < f i) ∨ (∀ i, 1 < r i) := by
  have hn (i : Fin 3) (hf : 1 < f i)
      (hr : 1 < r ((![1, 2, 0] : Fin 3 → Fin 3) i)) : False :=
    (not_lt_of_ge (hp i)) (one_lt_mul_of_lt_of_le hf hr.le)
  rcases hout 0 with h0 | h0
  · have h1 : 1 < f 1 := (hout 1).resolve_right (hn 0 h0)
    have h2 : 1 < f 2 := (hout 2).resolve_right (hn 1 h1)
    exact Or.inl (by intro i; fin_cases i <;> assumption)
  · have h2 : 1 < r 2 := (hout 2).resolve_left (fun h => hn 2 h h0)
    have h1 : 1 < r 1 := (hout 1).resolve_left (fun h => hn 1 h h2)
    exact Or.inr (by intro i; fin_cases i <;> assumption)

/-- Pair and path comparisons force an original row whose two off-diagonal
coefficients are at most one. No sign assumption on the coefficients is needed. -/
theorem exists_bounded_row_of_pair_and_path_bounds (f r : Fin 3 → ℝ)
    (hp0 : f 0 * r 1 ≤ 1) (hp1 : f 1 * r 2 ≤ 1) (hp2 : f 2 * r 0 ≤ 1)
    (hfp : f 1 * f 2 ≤ r 1) (hrp : r 0 * r 2 ≤ f 0) :
    ∃ i, f i ≤ 1 ∧ r i ≤ 1 := by
  by_contra! hn
  have hout (i : Fin 3) : 1 < f i ∨ 1 < r i := by
    by_cases h : 1 < f i
    · exact Or.inl h
    · exact Or.inr (hn i (le_of_not_gt h))
  have hp (i : Fin 3) : f i * r ((![1, 2, 0] : Fin 3 → Fin 3) i) ≤ 1 := by
    fin_cases i <;> assumption
  rcases cycle_of_pair_bounds f r hp hout with hf | hr
  · have hr1 : 1 < r 1 := lt_of_lt_of_le
      (one_lt_mul_of_lt_of_le (hf 1) (hf 2).le) hfp
    exact (not_lt_of_ge hp0) (one_lt_mul_of_lt_of_le (hf 0) hr1.le)
  · have hf0 : 1 < f 0 := lt_of_lt_of_le
      (one_lt_mul_of_lt_of_le (hr 0) (hr 2).le) hrp
    exact (not_lt_of_ge hp0) (one_lt_mul_of_lt_of_le hf0 (hr 1).le)

set_option linter.unusedVariables false in
/-- One original budget already bounds the width sum. The nonnegativity
hypotheses on `f,r` are retained for the existing interface. -/
theorem width_bound_of_pair_and_path_bounds (w f r : Fin 3 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) (hr : ∀ i, 0 ≤ r i)
    (hp0 : f 0 * r 1 ≤ 1) (hp1 : f 1 * r 2 ≤ 1) (hp2 : f 2 * r 0 ≤ 1)
    (hfp : f 1 * f 2 ≤ r 1) (hrp : r 0 * r 2 ≤ f 0)
    (h0 : 1 ≤ w 0 + f 0 * w 1 + r 0 * w 2)
    (h1 : 1 ≤ w 1 + f 1 * w 2 + r 1 * w 0)
    (h2 : 1 ≤ w 2 + f 2 * w 0 + r 2 * w 1) : 1 ≤ ∑ i, w i := by
  let c : Fin 3 → Fin 3 → ℝ :=
    ![![1, f 0, r 0], ![r 1, 1, f 1], ![f 2, r 2, 1]]
  have hbudget (i : Fin 3) : 1 ≤ ∑ j, c i j * w j := by
    simp only [Fin.sum_univ_three]
    fin_cases i
    · change 1 ≤ 1 * w 0 + f 0 * w 1 + r 0 * w 2
      simpa only [one_mul] using h0
    · change 1 ≤ r 1 * w 0 + 1 * w 1 + f 1 * w 2
      simp only [one_mul]
      linarith only [h1]
    · change 1 ≤ f 2 * w 0 + r 2 * w 1 + 1 * w 2
      simp only [one_mul]
      linarith only [h2]
  obtain ⟨i, hfi, hri⟩ := exists_bounded_row_of_pair_and_path_bounds f r hp0 hp1 hp2 hfp hrp
  apply width_bound_of_bounded_row w (c i) hw _ (hbudget i)
  intro j
  fin_cases i <;> fin_cases j <;> first | exact le_rfl | exact hfi | exact hri

end Plank.Convex.WidthBudgets

/-- info: 'Plank.Convex.WidthBudgets.width_bound_of_common_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.WidthBudgets.width_bound_of_common_budget

/-- info: 'Plank.Convex.WidthBudgets.width_bound_of_product_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.WidthBudgets.width_bound_of_product_comparison

/-- info: 'Plank.Convex.WidthBudgets.width_bound_of_pair_and_path_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.WidthBudgets.width_bound_of_pair_and_path_bounds

/-- info: 'Plank.Convex.WidthBudgets.width_bound_of_acyclic_budgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.WidthBudgets.width_bound_of_acyclic_budgets

/-- info: 'Plank.Convex.WidthBudgets.exists_bounded_row_of_pair_and_path_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.WidthBudgets.exists_bounded_row_of_pair_and_path_bounds
