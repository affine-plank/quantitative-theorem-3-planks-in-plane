/- Every three-window cover on a positive affine plane supplies one of the
39 minimal six-cycle cap patterns. This is an exhaustive reduction, not a
proof of the width inequalities associated with the patterns. -/
module
public import Plank.Convex.MixedPlaneCapReduction
public import Plank.Convex.PlanarCapPatterns
public import Mathlib.Data.Fin.VecNotation
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarCapCaseReduction
open scoped BigOperators
open PlanarCapPatterns

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def next (i : Fin 6) : Fin 6 := ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

private theorem next_prev (i : Fin 6) : next (prev i) = i := by fin_cases i <;> rfl

/-- The circular wall order is high 0, low 1, high 2, low 0, high 1, low 2. -/
def wall (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ) : Fin 6 → E →ᵃ[ℝ] ℝ :=
  ![f 0 - AffineMap.const ℝ E (hi 0), AffineMap.const ℝ E (lo 1) - f 1,
    f 2 - AffineMap.const ℝ E (hi 2), AffineMap.const ℝ E (lo 0) - f 0,
    f 1 - AffineMap.const ℝ E (hi 1), AffineMap.const ℝ E (lo 2) - f 2]

def EmptyPair (K : Set E) (g h : E →ᵃ[ℝ] ℝ) : Prop :=
  ¬ ∃ x ∈ K, 0 < g x ∧ 0 < h x

/-- A singleton removes one mixed escape pattern through a same-sign cap. -/
def SingleEmpty (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (i : Fin 6) : Prop :=
  EmptyPair K (wall f lo hi (next i)) (wall f lo hi (prev i))

/-- An edge removes two adjacent mixed escape patterns through a mixed cap. -/
def EdgeEmpty (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (i : Fin 6) : Prop :=
  EmptyPair K (wall f lo hi i) (wall f lo hi (next i))

private def cuts (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (i : Fin 6) : Fin 3 → E →ᵃ[ℝ] ℝ :=
  ![wall f lo hi (prev i), wall f lo hi i, wall f lo hi (next i)]

private theorem mixed_relation (S : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (a : Fin 3 → ℝ) (d : ℝ) (ha : ∀ j, 0 < a j)
    (hplane : ∀ v ∈ S, ∑ j, a j * f j v = d)
    (lo hi : Fin 3 → ℝ) (i : Fin 6) :
    ∃ (r : Fin 3 → ℝ) (c : ℝ), (∃ j, 0 < r j) ∧ (∃ j, r j < 0) ∧
      ∀ v ∈ S, ∑ j, r j * cuts f lo hi i j v = c := by
  let w : Fin 6 → ℝ := ![a 0, -a 1, a 2, -a 0, a 1, -a 2]
  let b : Fin 6 → ℝ := ![a 0 * hi 0, a 1 * lo 1, a 2 * hi 2,
    a 0 * lo 0, a 1 * hi 1, a 2 * lo 2]
  refine ⟨![w (prev i), w i, w (next i)], d - (b (prev i) + b i + b (next i)),
    ?_, ?_, ?_⟩
  · fin_cases i
    · exact ⟨1, ha 0⟩
    · exact ⟨0, ha 0⟩
    · exact ⟨1, ha 2⟩
    · exact ⟨0, ha 2⟩
    · exact ⟨1, ha 1⟩
    · exact ⟨0, ha 1⟩
  · fin_cases i
    · exact ⟨0, neg_neg_of_pos (ha 2)⟩
    · exact ⟨1, neg_neg_of_pos (ha 1)⟩
    · exact ⟨0, neg_neg_of_pos (ha 1)⟩
    · exact ⟨1, neg_neg_of_pos (ha 0)⟩
    · exact ⟨0, neg_neg_of_pos (ha 0)⟩
    · exact ⟨1, neg_neg_of_pos (ha 2)⟩
  · intro v hv
    have hp := hplane v hv
    simp only [Fin.sum_univ_three] at hp
    fin_cases i <;>
      simp [cuts, wall, prev, next, w, b, Fin.sum_univ_three] <;> linarith

private theorem triple_empty_of_cover (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) (i : Fin 6) :
    ¬ ∃ x ∈ K, ∀ j, 0 < cuts f lo hi i j x := by
  rintro ⟨x, hx, hc⟩
  obtain ⟨j, hjlo, hjhi⟩ := hcover x hx
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  fin_cases i <;> fin_cases j <;>
    simp [cuts, wall, prev, next] at h0 h1 h2 hjlo hjhi <;> linarith

/-- Every mixed escape triple has an empty pair cap. Convexity is supplied by
the finite hull; the strictly positive affine relation is the planar hypothesis. -/
theorem node_covered (S : Set E) (hS : S.Finite) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (a : Fin 3 → ℝ) (d : ℝ) (ha : ∀ j, 0 < a j)
    (hplane : ∀ v ∈ S, ∑ j, a j * f j v = d)
    (lo hi : Fin 3 → ℝ)
    (hcover : ∀ x ∈ convexHull ℝ S, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j)
    (i : Fin 6) :
    SingleEmpty (convexHull ℝ S) f lo hi i ∨
      EdgeEmpty (convexHull ℝ S) f lo hi i ∨
      EdgeEmpty (convexHull ℝ S) f lo hi (prev i) := by
  obtain ⟨r, c, hrp, hrn, hrel⟩ := mixed_relation S f a d ha hplane lo hi i
  have he := MixedPlaneCapReduction.empty_pair_of_empty_triple S hS
    (cuts f lo hi i) r c hrp hrn hrel
    (triple_empty_of_cover (convexHull ℝ S) f lo hi hcover i)
  rcases he with he | he | he
  · right; right
    simpa [EdgeEmpty, EmptyPair, cuts, next_prev] using he
  · right; left
    exact he
  · left
    exact he

/-- A covered finite hull on a positive affine plane realizes one of the
39 listed minimal cap patterns. The conclusion records actual empty caps
throughout the hull, rather than only tests at its generators or edges. -/
theorem exists_cap_pattern (S : Set E) (hS : S.Finite) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (a : Fin 3 → ℝ) (d : ℝ) (ha : ∀ j, 0 < a j)
    (hplane : ∀ v ∈ S, ∑ j, a j * f j v = d)
    (lo hi : Fin 3 → ℝ)
    (hcover : ∀ x ∈ convexHull ℝ S, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) :
    ∃ p ∈ patterns, Holds (SingleEmpty (convexHull ℝ S) f lo hi)
      (EdgeEmpty (convexHull ℝ S) f lo hi) p := by
  exact exists_holding_pattern _ _ (node_covered S hS f a d ha hplane lo hi hcover)

/-- The same local alternative holds on every convex set, without a finite
generation, compactness, closedness, or nondegeneracy assumption. -/
theorem node_covered_convex (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a : Fin 3 → ℝ) (d : ℝ) (ha : ∀ j, 0 < a j)
    (hplane : ∀ v ∈ K, ∑ j, a j * f j v = d)
    (lo hi : Fin 3 → ℝ)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j)
    (i : Fin 6) :
    SingleEmpty K f lo hi i ∨ EdgeEmpty K f lo hi i ∨ EdgeEmpty K f lo hi (prev i) := by
  obtain ⟨r, c, hrp, hrn, hrel⟩ := mixed_relation K f a d ha hplane lo hi i
  have he := MixedPlaneCapReduction.empty_pair_of_empty_triple_convex K hK
    (cuts f lo hi i) r c hrp hrn hrel (triple_empty_of_cover K f lo hi hcover i)
  rcases he with he | he | he
  · right; right
    simpa [EdgeEmpty, EmptyPair, cuts, next_prev] using he
  · right; left
    exact he
  · left
    exact he

/-- Every three-window cover of a convex set on a positive affine plane
realizes one of the 39 cap patterns. Each selected cap is empty on all of K. -/
theorem exists_cap_pattern_convex (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a : Fin 3 → ℝ) (d : ℝ) (ha : ∀ j, 0 < a j)
    (hplane : ∀ v ∈ K, ∑ j, a j * f j v = d)
    (lo hi : Fin 3 → ℝ)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) :
    ∃ p ∈ patterns, Holds (SingleEmpty K f lo hi) (EdgeEmpty K f lo hi) p := by
  exact exists_holding_pattern _ _ (node_covered_convex K hK f a d ha hplane lo hi hcover)

private theorem triple_empty_of_nodes (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ)
    (hnodes : ∀ i, SingleEmpty K f lo hi i ∨ EdgeEmpty K f lo hi i ∨
      EdgeEmpty K f lo hi (prev i)) (i : Fin 6) :
    ¬ ∃ x ∈ K, ∀ j, 0 < cuts f lo hi i j x := by
  rintro ⟨x, hx, hf⟩
  rcases hnodes i with he | he | he
  · exact he ⟨x, hx, hf 2, hf 0⟩
  · exact he ⟨x, hx, hf 1, hf 2⟩
  · have he' : EmptyPair K (wall f lo hi (prev i)) (wall f lo hi i) := by
      simpa only [EdgeEmpty, next_prev] using he
    exact he' ⟨x, hx, hf 0, hf 1⟩

/-- The six cap alternatives imply actual coverage when the positive plane
meets the window box. This direction does not need convexity. -/
theorem covered_of_nodes (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (a : Fin 3 → ℝ) (d : ℝ) (ha : ∀ j, 0 < a j)
    (hplane : ∀ v ∈ K, ∑ j, a j * f j v = d)
    (lo hi : Fin 3 → ℝ) (hlo : ∑ j, a j * lo j ≤ d)
    (hhi : d ≤ ∑ j, a j * hi j)
    (hnodes : ∀ i, SingleEmpty K f lo hi i ∨ EdgeEmpty K f lo hi i ∨
      EdgeEmpty K f lo hi (prev i)) :
    ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j := by
  classical
  intro x hx
  by_contra h
  have hout (j : Fin 3) : f j x < lo j ∨ hi j < f j x := by
    by_cases hl : lo j ≤ f j x
    · exact Or.inr (lt_of_not_ge (fun hh => h ⟨j, hl, hh⟩))
    · exact Or.inl (lt_of_not_ge hl)
  have he (i : Fin 6) : ¬ ∀ j, 0 < cuts f lo hi i j x := by
    intro hf
    exact triple_empty_of_nodes K f lo hi hnodes i ⟨x, hx, hf⟩
  have hp := hplane x hx
  simp only [Fin.sum_univ_three] at hp hlo hhi
  rcases hout 0 with h0 | h0 <;> rcases hout 1 with h1 | h1 <;>
    rcases hout 2 with h2 | h2
  · have h0' := mul_lt_mul_of_pos_left h0 (ha 0)
    have h1' := mul_lt_mul_of_pos_left h1 (ha 1)
    have h2' := mul_lt_mul_of_pos_left h2 (ha 2)
    linarith only [hp, hlo, h0', h1', h2']
  · apply he 2
    intro j
    fin_cases j <;> simp [cuts, wall, prev, next] <;> assumption
  · apply he 4
    intro j
    fin_cases j <;> simp [cuts, wall, prev, next] <;> assumption
  · apply he 3
    intro j
    fin_cases j <;> simp [cuts, wall, prev, next] <;> assumption
  · apply he 0
    intro j
    fin_cases j <;> simp [cuts, wall, prev, next] <;> assumption
  · apply he 1
    intro j
    fin_cases j <;> simp [cuts, wall, prev, next] <;> assumption
  · apply he 5
    intro j
    fin_cases j <;> simp [cuts, wall, prev, next] <;> assumption
  · have h0' := mul_lt_mul_of_pos_left h0 (ha 0)
    have h1' := mul_lt_mul_of_pos_left h1 (ha 1)
    have h2' := mul_lt_mul_of_pos_left h2 (ha 2)
    linarith only [hp, hhi, h0', h1', h2']

/-- With the plane meeting the window box, the finite cap cases are exactly
equivalent to coverage of an arbitrary convex set. -/
theorem covered_iff_cap_pattern (K : Set E) (hK : Convex ℝ K)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) (a : Fin 3 → ℝ) (d : ℝ) (ha : ∀ j, 0 < a j)
    (hplane : ∀ v ∈ K, ∑ j, a j * f j v = d)
    (lo hi : Fin 3 → ℝ) (hlo : ∑ j, a j * lo j ≤ d)
    (hhi : d ≤ ∑ j, a j * hi j) :
    (∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) ↔
      ∃ p ∈ patterns, Holds (SingleEmpty K f lo hi) (EdgeEmpty K f lo hi) p := by
  constructor
  · exact exists_cap_pattern_convex K hK f a d ha hplane lo hi
  · rintro ⟨p, hp, hh⟩
    exact covered_of_nodes K f a d ha hplane lo hi hlo hhi
      (nodes_of_holding_pattern _ _ p hp hh)

end Plank.Convex.PlanarCapCaseReduction

/-- info: 'Plank.Convex.PlanarCapCaseReduction.node_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapCaseReduction.node_covered

/-- info: 'Plank.Convex.PlanarCapCaseReduction.exists_cap_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapCaseReduction.exists_cap_pattern

/-- info: 'Plank.Convex.PlanarCapCaseReduction.exists_cap_pattern_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapCaseReduction.exists_cap_pattern_convex

/-- info: 'Plank.Convex.PlanarCapCaseReduction.covered_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapCaseReduction.covered_of_nodes

/-- info: 'Plank.Convex.PlanarCapCaseReduction.covered_iff_cap_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapCaseReduction.covered_iff_cap_pattern
