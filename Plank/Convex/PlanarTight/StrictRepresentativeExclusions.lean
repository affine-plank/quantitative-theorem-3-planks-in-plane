/- Five strict positive equality exclusions in the finite planar cap ledger. -/
module
public import Plank.Convex.PlanarTight.StrictCapSetting
public import Plank.Convex.PlanarTight.RowB
public import Plank.Convex.PlanarTight.RowD
public import Plank.Convex.PlanarTight.RowFCommonPoint
public import Plank.Convex.PlanarTight.OppositeCaps
public import Plank.Convex.RowECapWidth
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.StrictRepresentativeExclusions
open StrictCapSetting PlanarCapPatterns PlanarCapCaseReduction

theorem rowB : Excluded ⟨60, 1⟩ := by
  intro C hh
  have hs2 := hh.1 2 (by decide)
  have hs3 := hh.1 3 (by decide)
  have hs4 := hh.1 4 (by decide)
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev]
    at hs2 hs3 hs4 hs5 he0
  simp at hs2 hs3 hs4 hs5 he0
  apply RowB.not_tight_of_caps C.K C.convex C.min C.max C.lo C.hi
    C.lo_pos C.hi_lt C.width_pos ?_ ?_ ?_ ?_ ?_ C.total
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

theorem rowD : Excluded ⟨48, 5⟩ := by
  intro C hh
  have hs4 := hh.1 4 (by decide)
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  have he2 := hh.2 2 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev]
    at hs4 hs5 he0 he2
  simp at hs4 hs5 he0 he2
  apply RowD.not_tight_of_caps C.K C.convex C.box C.min C.max C.lo C.hi
    C.lo_pos C.hi_lt C.width_pos ?_ ?_ ?_ ?_ C.A C.D (C.positive 1).ne' C.plane C.total
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs5 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs4 x hx h2) (not_le.2 h1)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he0 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he2 x hx h1) (not_le.2 h2)

theorem rowE : Excluded ⟨36, 9⟩ := by
  intro C hh
  have hs2 := hh.1 2 (by decide)
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  have he3 := hh.2 3 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev]
    at hs2 hs5 he0 he3
  simp at hs2 hs5 he0 he3
  have htwo := RowECapWidth.two_windows_width_bound C.K C.convex C.box C.min C.max
    C.lo C.hi (fun i => (C.width_pos i).le) 0 1 (by
      intro x hx
      by_cases h0 : C.lo 0 ≤ x 0 ∧ x 0 ≤ C.hi 0
      · exact Or.inl h0
      · right
        have hout : x 0 < C.lo 0 ∨ C.hi 0 < x 0 := by
          by_contra hcon
          push Not at hcon
          exact h0 ⟨hcon.1, hcon.2⟩
        constructor
        · rcases hout with hl | hu
          · exact hs2 x hx hl
          · exact he0 x hx hu
        · rcases hout with hl | hu
          · exact he3 x hx hl
          · exact hs5 x hx hu)
  have hsum := C.total
  rw [Fin.sum_univ_three] at hsum
  linarith only [htwo, hsum, C.width_pos 2]

theorem rowF : Excluded ⟨32, 11⟩ := by
  intro C hh
  have hs5 := hh.1 5 (by decide)
  have he0 := hh.2 0 (by decide)
  have he1 := hh.2 1 (by decide)
  have he3 := hh.2 3 (by decide)
  simp only [SingleEmpty, EdgeEmpty, EmptyPair, wall, next, PlanarCapPatterns.prev]
    at hs5 he0 he1 he3
  simp at hs5 he0 he1 he3
  apply RowF.not_tight_of_cover C.K C.convex C.box C.min C.max C.lo C.hi C.A C.D
    C.positive C.plane C.lo_pos C.hi_lt C.width_pos C.covered ?_ ?_ ?_ ?_ C.total
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (hs5 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he0 x hx h1) (not_le.2 h2)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he1 x hx h2) (not_le.2 h1)
  · rintro ⟨x, hx, h1, h2⟩
    exact absurd (he3 x hx h1) (not_le.2 h2)

theorem rowH : Excluded ⟨0, 27⟩ := by
  intro C hh
  have he0 := hh.2 0 (by decide)
  have he1 := hh.2 1 (by decide)
  have he3 := hh.2 3 (by decide)
  have he4 := hh.2 4 (by decide)
  simp only [EdgeEmpty, EmptyPair, wall, next] at he0 he1 he3 he4
  simp at he0 he1 he3 he4
  let t : Fin 2 → Fin 3 := ![0, 2]
  obtain ⟨i, hmax⟩ : ∃ i : Fin 2, ∀ j : Fin 2, C.A (t j) ≤ C.A (t i) := by
    rcases le_total (C.A 0) (C.A 2) with h | h
    · exact ⟨1, fun j => by fin_cases j; exact h; exact le_rfl⟩
    · exact ⟨0, fun j => by fin_cases j; exact le_rfl; exact h⟩
  have hplane (x : Point) (hx : x ∈ C.K) :
      C.A 1 * x 1 + ∑ j : Fin 2, C.A (t j) * x (t j) = C.D := by
    have hp := C.plane x hx
    simp only [Fin.sum_univ_three] at hp
    simpa only [Fin.sum_univ_two, t, Matrix.cons_val_zero, Matrix.cons_val_one,
      add_comm, add_left_comm, add_assoc] using hp
  obtain ⟨L, hL, hLi⟩ := C.min (t i)
  obtain ⟨U, hU, hUi⟩ := C.max (t i)
  have hw := OppositeCaps.strict_width_bound C.K C.convex (AffineMap.proj 1)
    (fun j : Fin 2 => AffineMap.proj (t j)) (C.A 1) (fun j => C.A (t j)) C.D
    (C.positive 1) (fun j => (C.positive (t j)).le) hplane i (C.positive (t i)) hmax
    (fun j => C.lo (t j)) (fun j => C.hi (t j)) (C.lo 1) (C.hi 1)
    (fun j => (C.width_pos (t j)).le) (C.width_pos 1) (C.lo_pos 1) (C.hi_lt 1)
    (C.min 1) (C.max 1) ⟨L, hL, hLi, C.box L hL 1⟩ ⟨U, hU, hUi, C.box U hU 1⟩
    (by
      intro x hx hy j
      fin_cases j
      · exact le_of_not_gt fun h => (not_le.2 hy) (he3 x hx h)
      · exact he4 x hx hy)
    (by
      intro x hx hy j
      fin_cases j
      · exact le_of_not_gt fun h => (not_le.2 hy) (he0 x hx h)
      · exact he1 x hx hy)
  have hsum := C.total
  simp only [Fin.sum_univ_three] at hsum
  simp only [Fin.sum_univ_two, t, Matrix.cons_val_zero, Matrix.cons_val_one] at hw
  linarith only [hsum, hw]

end Plank.Convex.PlanarTight.StrictRepresentativeExclusions

/-- info: 'Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowB

/-- info: 'Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowD

/-- info: 'Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowE

/-- info: 'Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowF

/-- info: 'Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.StrictRepresentativeExclusions.rowH
