/- Row E of the planar cap ledger, patterns (36,9), (9,18), (18,36): the two singleton caps and
the two mixed caps of one coordinate pair are the four ways to escape both of its windows, so
those two windows alone cover the body and the two-plank theorem gives the width bound. -/
module
public import Plank.Convex.TwoAffineWindows
public import Plank.Convex.PlanarCapSymmetry
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.RowECapWidth
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- Two coordinate windows covering a convex set that attains `0` and `1` in both coordinates
have total width at least one, by the shared affine-window bound. -/
theorem two_windows_width_bound (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i) (i j : Fin 3)
    (hcover : ∀ x ∈ K, (lo i ≤ x i ∧ x i ≤ hi i) ∨ (lo j ≤ x j ∧ x j ≤ hi j)) :
    1 ≤ (hi i - lo i) + (hi j - lo j) := by
  exact TwoAffineWindows.width_bound K hK (AffineMap.proj i) (AffineMap.proj j)
    (fun x hx => ⟨hbox x hx i, hbox x hx j⟩)
    (lo i) (hi i) (lo j) (hi j) (horder i) (horder j)
    (hL i) (hU i) (hL j) (hU j) hcover

/-- The four empty caps of a coordinate pair leave its two windows covering the set, so those two
windows alone carry the width bound; the third window only adds its nonnegative width. -/
theorem width_bound_of_pair_caps (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i) (i j : Fin 3) (hij : i ≠ j)
    (hLL : ¬ ∃ x ∈ K, x i < lo i ∧ x j < lo j)
    (hUU : ¬ ∃ x ∈ K, hi i < x i ∧ hi j < x j)
    (hUL : ¬ ∃ x ∈ K, hi i < x i ∧ x j < lo j)
    (hLU : ¬ ∃ x ∈ K, x i < lo i ∧ hi j < x j) :
    1 ≤ ∑ k, (hi k - lo k) := by
  have h2 := two_windows_width_bound K hK hbox hL hU lo hi horder i j (by
    intro x hx
    by_cases hi1 : lo i ≤ x i ∧ x i ≤ hi i
    · exact Or.inl hi1
    · right
      have hout : x i < lo i ∨ hi i < x i := by
        by_contra hcon
        push Not at hcon
        exact hi1 ⟨hcon.1, hcon.2⟩
      constructor
      · by_contra hj
        push Not at hj
        rcases hout with hlt | hgt
        · exact hLL ⟨x, hx, hlt, hj⟩
        · exact hUL ⟨x, hx, hgt, hj⟩
      · by_contra hj
        push Not at hj
        rcases hout with hlt | hgt
        · exact hLU ⟨x, hx, hlt, hj⟩
        · exact hUU ⟨x, hx, hgt, hj⟩)
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset (Fin 3)))
    (fun k _ _ => sub_nonneg.2 (horder k))
  rw [Finset.sum_pair hij] at hsub
  linarith

/-! ### The ledger interface -/

open PlanarCapPatterns in
/-- The three labelled members of row E: the four caps of the coordinate pairs (0,1), (1,2), (2,0). -/
def IsRowE (p : Pattern) : Prop :=
  p = ⟨36, 9⟩ ∨ p = ⟨9, 18⟩ ∨ p = ⟨18, 36⟩

open PlanarCapPatterns in
instance (p : Pattern) : Decidable (IsRowE p) :=
  inferInstanceAs (Decidable (p = ⟨36, 9⟩ ∨ p = ⟨9, 18⟩ ∨ p = ⟨18, 36⟩))

open PlanarCapCaseReduction PlanarCapPatterns in
private theorem representative_width_bound : PlanarCapSymmetry.WidthBound ⟨36, 9⟩ := by
  intro K hK hbox hL hU lo hi horder _hcover hh
  have hs2 := hh.1 2 (by decide)
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  have he3 := hh.2 3 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev]
    at hs2 hs5 he0 he3
  simp at hs2 hs5 he0 he3
  apply width_bound_of_pair_caps K hK hbox hL hU lo hi horder 0 1 (by decide)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs2 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs5 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he0 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he3 x hx h1) (not_le.2 h2)

open PlanarCapCaseReduction PlanarCapPatterns in
/-- All three patterns of row E satisfy the width bound. The four empty caps
already make two coordinate windows cover the set. -/
theorem width_bound (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (_hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (p : Pattern) (hp : IsRowE p)
    (hh : Holds (SingleEmpty K (fun i => AffineMap.proj i) lo hi)
      (EdgeEmpty K (fun i => AffineMap.proj i) lo hi) p) :
    1 ≤ ∑ i, (hi i - lo i) := by
  have horbit : ∃ r : Fin 6, ∃ reverse : Bool,
      PlanarCapSymmetry.Pulls p ⟨36, 9⟩ r reverse := by
    rcases hp with rfl | rfl | rfl <;> decide
  obtain ⟨r, reverse, hr⟩ := horbit
  exact PlanarCapSymmetry.width_bound_of_pulls p _ r reverse hr
    representative_width_bound K hK hbox hL hU lo hi horder _hcover hh

end Plank.Convex.RowECapWidth

/-- info: 'Plank.Convex.RowECapWidth.two_windows_width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowECapWidth.two_windows_width_bound

/-- info: 'Plank.Convex.RowECapWidth.width_bound_of_pair_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowECapWidth.width_bound_of_pair_caps

/-- info: 'Plank.Convex.RowECapWidth.width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.RowECapWidth.width_bound
