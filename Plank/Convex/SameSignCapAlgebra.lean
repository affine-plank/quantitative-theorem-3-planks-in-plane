/- A finite algebraic obstruction for the all-singleton cap case.
Six positive pair separators and the coordinate contacts imply eighteen
polynomial inequalities. Their infeasibility under a deficit is not asserted. -/
module
public import Plank.Convex.ConvexCellSeparation
public import Plank.Convex.PlanarCapCaseReduction
public import Plank.Convex.CommonPointUnclipped
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.SameSignCapAlgebra
open scoped BigOperators

abbrev Point := Fin 3 → ℝ
def next : Fin 3 → Fin 3 := ![1, 2, 0]
def prev : Fin 3 → Fin 3 := ![2, 0, 1]

@[simp] theorem next_next (i : Fin 3) : next (next i) = prev i := by fin_cases i <;> rfl
@[simp] theorem next_prev (i : Fin 3) : next (prev i) = i := by fin_cases i <;> rfl


/-- The three cyclic positions exhaust the coordinate index. -/
theorem index_cases (i j : Fin 3) : j = i ∨ j = next i ∨ j = prev i := by
  fin_cases i <;> fin_cases j <;> decide

/-- Write a sum of three coordinates starting at any cyclic position. -/
theorem sum_cycle (x : Point) (i : Fin 3) : (∑ j, x j) = x i + x (next i) + x (prev i) := by
  fin_cases i <;> simp [Fin.sum_univ_three, next, prev] <;> ring

def UpperSupports (S : Set Point) (hi a : Point) : Prop :=
  ∀ i, ∀ x ∈ S, x i + a i * x (next i) ≤ hi i + a i * hi (next i)

def LowerSupports (S : Set Point) (lo b : Point) : Prop :=
  ∀ i, ∀ x ∈ S, lo i + b i * lo (next i) ≤ x i + b i * x (next i)

/-- Six inequalities per cyclic coordinate: four bounds from the two
coordinate contacts of a pair, and two from its opposite contacts. -/
def NumericRows (lo hi a b : Point) : Prop := ∀ i,
  1 ≤ hi i + a i * hi (next i) ∧
  a i ≤ hi i + a i * hi (next i) ∧
  lo i + b i * lo (next i) ≤ 1 ∧
  lo i + b i * lo (next i) ≤ b i ∧
  lo i * (1 + b i * a (next i) * b (prev i)) ≤
    b i * (hi (next i) - lo (next i)) +
      b i * a (next i) * (hi (prev i) - lo (prev i)) ∧
  (1 - hi i) * (1 + a i * b (next i) * a (prev i)) ≤
    a i * (hi (next i) - lo (next i)) +
      a i * b (next i) * (hi (prev i) - lo (prev i))

/-- The eighteen rows follow from actual supports at all six contacts.
No convexity or plane relation is needed once the supports are supplied. -/
theorem numeric_rows_of_supports (S : Set Point)
    (hbox : ∀ x ∈ S, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ S, x i = 0) (hU : ∀ i, ∃ x ∈ S, x i = 1)
    (lo hi a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hupper : UpperSupports S hi a) (hlower : LowerSupports S lo b) :
    NumericRows lo hi a b := by
  intro i
  obtain ⟨p, hp, hpi⟩ := hL i
  obtain ⟨q, hq, hqi⟩ := hU i
  obtain ⟨r, hr, hrj⟩ := hL (next i)
  obtain ⟨s, hs, hsj⟩ := hU (next i)
  have huq := hupper i q hq
  have hus := hupper i s hs
  have hlp := hlower i p hp
  have hlr := hlower i r hr
  rw [hqi] at huq
  rw [hsj, mul_one] at hus
  rw [hpi, zero_add] at hlp
  rw [hrj, mul_zero, add_zero] at hlr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith only [huq, mul_nonneg (ha i).le (hbox q hq (next i)).1]
  · linarith only [hus, (hbox s hs i).1]
  · exact hlr.trans (hbox r hr i).2
  · have ht := mul_le_mul_of_nonneg_left (hbox p hp (next i)).2 (hb i).le
    exact hlp.trans (by simpa only [mul_one] using ht)
  · have hup := hupper (next i) p hp
    have hlp' := hlower (prev i) p hp
    simp only [next_next] at hup
    simp only [next_prev, hpi, mul_zero, add_zero] at hlp'
    have h1 := mul_le_mul_of_nonneg_left hup (hb i).le
    have h2 := mul_le_mul_of_nonneg_left hlp' (mul_nonneg (hb i).le (ha (next i)).le)
    nlinarith only [h1, h2, hlp]
  · have hlq := hlower (next i) q hq
    have huq' := hupper (prev i) q hq
    simp only [next_next] at hlq
    simp only [next_prev, hqi, mul_one] at huq'
    have h1 := mul_le_mul_of_nonneg_left hlq (ha i).le
    have h2 := mul_le_mul_of_nonneg_left huq' (mul_nonneg (ha i).le (hb (next i)).le)
    nlinarith only [h1, h2, huq]

/-- Empty same-sign caps on a convex body give positive separators on a
the whole body, and hence the polynomial rows. -/
theorem exists_numeric_rows (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hlow : ∀ i, ¬ ∃ x ∈ K, x i < lo i ∧ x (next i) < lo (next i))
    (hhigh : ∀ i, ¬ ∃ x ∈ K, hi i < x i ∧ hi (next i) < x (next i)) :
    ∃ a b : Point, (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧ NumericRows lo hi a b := by
  have hu (i : Fin 3) := ConvexCellSeparation.exists_upper_support K hK
    (AffineMap.proj i) (AffineMap.proj (next i)) (hi i) (hi (next i))
    (hhi i) (hhi (next i)) (hU i) (hU (next i)) (hhigh i)
  have hl (i : Fin 3) := ConvexCellSeparation.exists_lower_support K hK
    (AffineMap.proj i) (AffineMap.proj (next i)) (lo i) (lo (next i))
    (hlo i) (hlo (next i)) (hL i) (hL (next i)) (hlow i)
  choose a ha has using hu
  choose b hb hbs using hl
  exact ⟨a, b, ha, hb, numeric_rows_of_supports K hbox hL hU lo hi a b ha hb has hbs⟩

/-- The six singleton caps are exactly the three lower and three upper pair caps. -/
theorem empty_pair_caps_of_single_empty (K : Set Point) (lo hi : Point)
    (hsingle : ∀ e, PlanarCapCaseReduction.SingleEmpty K (fun i => AffineMap.proj i) lo hi e) :
    (∀ i, ¬ ∃ x ∈ K, x i < lo i ∧ x (next i) < lo (next i)) ∧
    (∀ i, ¬ ∃ x ∈ K, hi i < x i ∧ hi (next i) < x (next i)) := by
  constructor
  · intro i
    let e : Fin 6 := ![2, 0, 4] i
    intro he
    obtain ⟨x, hx, hi', hj'⟩ := he
    apply hsingle e
    refine ⟨x, hx, ?_⟩
    fin_cases i <;> simp [next, e, PlanarCapCaseReduction.wall,
      PlanarCapCaseReduction.next, PlanarCapPatterns.prev] at hi' hj' ⊢ <;>
      constructor <;> linarith
  · intro i
    let e : Fin 6 := ![5, 3, 1] i
    intro he
    obtain ⟨x, hx, hi', hj'⟩ := he
    apply hsingle e
    refine ⟨x, hx, ?_⟩
    fin_cases i <;> simp [next, e, PlanarCapCaseReduction.wall,
      PlanarCapCaseReduction.next, PlanarCapPatterns.prev] at hi' hj' ⊢ <;>
      constructor <;> linarith

/-- Any actual deficient cover with all six singleton caps empty produces
the eighteen-row algebraic obstruction, with strictly interior windows.
The assertion that no such real parameters exist remains a separate task. -/
theorem deficit_obstruction (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1)
    (hsingle : ∀ e, PlanarCapCaseReduction.SingleEmpty K (fun i => AffineMap.proj i) lo hi e) :
    (∀ i, 0 < lo i ∧ hi i < 1) ∧
      ∃ a b : Point, (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧ NumericRows lo hi a b := by
  have hm := CommonPointUnclipped.windows_strict_of_deficit K hK hbox hL hU
    lo hi horder hcover hdef
  have hcaps := empty_pair_caps_of_single_empty K lo hi hsingle
  exact ⟨hm, exists_numeric_rows K hK hbox hL hU lo hi
    (fun i => (hm i).1) (fun i => (hm i).2) hcaps.1 hcaps.2⟩

end Plank.Convex.SameSignCapAlgebra

/-- info: 'Plank.Convex.SameSignCapAlgebra.numeric_rows_of_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapAlgebra.numeric_rows_of_supports

/-- info: 'Plank.Convex.SameSignCapAlgebra.exists_numeric_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapAlgebra.exists_numeric_rows

/-- info: 'Plank.Convex.SameSignCapAlgebra.deficit_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapAlgebra.deficit_obstruction
