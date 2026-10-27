module
/-
# Planks — the objects and the statements

The definitions of the whole development, and nothing else: planks and
triangles in the plane, relative width, the configuration record `Config`
(three planks against the standard triangle), and the conjecture
statements at every generality (namespace `Bang`).

This file imports `Plank.Plane` (the plane vocabulary, re-exported here)
and Mathlib, contains no `sorry`, and is the first chapter of the paper:
a reader who finishes it knows exactly *what* is claimed everywhere else.

Naming: the working plane is plain `ℝ × ℝ` with the explicit dot product
`dot` — the elementary vocabulary of the audit surface. The inner-product
-space generalities live in the `Bang` namespace at the end. Old names
replaced here: `PlankConjecture.dot`/`.Plank`/`.Triangle`
(Dim2N3/ElementaryStatement), `KPlankLedger.fn`/`.Slab`/`.Wn`/`.relW`,
`KPlankAssembly.Config`, `TightGlobalBridge.stdTriangle`.
-/
public import Plank.Plane
public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section


-- Module-system bookkeeping: `public section` exports the signatures;
-- the surrounding exposed section exports definition bodies, so downstream files
-- may unfold it (`simp [dot]`, `unfold Config.relW`, …).
public section

open scoped RealInnerProductSpace

noncomputable section

/-! ## §1  The plane: dot products, planks, triangles — now `Plank.Plane`

The definitions `dot`, `Plank`, `Triangle`, `Triangle.width`,
`Triangle.shadowMin`, `Triangle.shadowMax`, `Plank.relWidth` and
`ThreePlanksOnATriangle` live in `Plank.Plane`, which this file imports
publicly, so every consumer of `Plank.Core` still sees them. -/

/-! ## §2  The standard triangle and configurations

Affine invariance (proved in `Plank/Transport.lean`) reduces every
triangle to the **standard triangle** `conv{(0,0), (1,0), (0,1)}`, whose
width formula is a rational expression in the normal's coordinates.  A
`Config` bundles what remains after that reduction: three planks against
the standard triangle. -/

/-- The three vertices `(0,0)`, `(1,0)`, `(0,1)` are not collinear. -/
theorem std_not_collinear :
    ¬ Collinear ℝ ({((0:ℝ),(0:ℝ)), ((1:ℝ),(0:ℝ)), ((0:ℝ),(1:ℝ))} :
      Set (ℝ × ℝ)) := by
  intro h
  rw [collinear_iff_of_mem (Set.mem_insert _ _)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, hr⟩ := hv ((1:ℝ),(0:ℝ)) (by simp)
  obtain ⟨s, hs⟩ := hv ((0:ℝ),(1:ℝ)) (by simp)
  have hr1 : (1:ℝ) = r * v.1 := by simpa [Prod.ext_iff] using congrArg Prod.fst hr
  have hr2 : r * v.2 = 0 := by simpa [Prod.ext_iff] using congrArg Prod.snd hr
  have hs1 : s * v.1 = 0 := by simpa [Prod.ext_iff] using congrArg Prod.fst hs
  have hs2 : (1:ℝ) = s * v.2 := by simpa [Prod.ext_iff] using congrArg Prod.snd hs
  nlinarith [hr1, hr2, hs1, hs2]

/-- The **standard triangle** with vertices `(0,0)`, `(1,0)`, `(0,1)`.
(Replaces `TightGlobalBridge.stdTriangle`, which was the same set.) -/
def stdTriangle : Triangle :=
  ⟨((0:ℝ),(0:ℝ)), ((1:ℝ),(0:ℝ)), ((0:ℝ),(1:ℝ)), std_not_collinear⟩

/-- A **configuration**: three planks, read against the standard
triangle.  The single object that Symmetry, GapCells, Tight, V1 and
Quant all speak about.  (Replaces `KPlankAssembly.Config`.) -/
structure Config where
  plank : Fin 3 → Plank

/-- The `i`-th plank's relative width against the standard triangle. -/
def Config.relW (C : Config) (i : Fin 3) : ℝ :=
  (C.plank i).relWidth stdTriangle

/-- The ledger: the sum of the three relative widths. -/
def Config.sumRelW (C : Config) : ℝ := ∑ i, C.relW i

/-- The configuration covers the standard triangle. -/
def Config.Covers (C : Config) : Prop :=
  ∀ P ∈ stdTriangle, ∃ i, P ∈ C.plank i

/-- The **gap**: the part of the standard triangle no plank covers. -/
def Config.uncovered (C : Config) : Set (ℝ × ℝ) :=
  stdTriangle.set \ ⋃ i, (C.plank i).set

/-- The area of the gap, as a real number. -/
def Config.gapArea (C : Config) : ℝ :=
  (MeasureTheory.volume C.uncovered).toReal

/-- The **deficit** `1 − Σ rw`: what the ledger is missing.  The v1
theorem says a covering has deficit `≤ 0`; the v3 theorem bounds the gap
area from below by `deficit² · |T|` where `|T| = 1/2`. -/
def Config.deficit (C : Config) : ℝ := 1 - C.sumRelW

/-- The **signed square bound** for one configuration:
`gap ≥ (1 − Σ rw)² · |T|` with `|T| = 1/2`.  This is v3's
*deficit-regime* currency, **not** a universal claim — over-coverings
refute the signed form (three full-width planks give `deficit = −2`,
`gap = 0`).  The global v3 claim is the positive-part form
`Quant.SqPos`, `(1 − Σ rw)₊² · |T| ≤ gap`, which reduces to `SqBound`
exactly on `Σ rw < 1` (`Quant.sqPos_of_lt_one`) and implies v1 for
coverings. -/
def Config.SqBound (C : Config) : Prop :=
  C.deficit ^ 2 * (1 / 2) ≤ C.gapArea

/-! ## §3  The conjecture at every generality (namespace `Bang`)

The general statements live in an arbitrary finite-dimensional real
inner product space.  They are the outer shell of the development: the
plane theory above is the `d = 2`, `n = 3` instance (dictionary in
`Plank/Transport.lean`), and Ambrus's lifting (also Transport) says the
simplex statements below imply the whole conjecture. -/

namespace Bang

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Width of a set `K` along direction `u`:
`sup_{y ∈ K} ⟪y, u⟫ − inf_{y ∈ K} ⟪y, u⟫`.  (Was the root-level
`widthAlong`.) -/
def widthAlong (K : Set E) (u : E) : ℝ :=
  sSup ((fun x => ⟪x, u⟫) '' K) - sInf ((fun x => ⟪x, u⟫) '' K)

/-- **Bang's affine plank conjecture** in the space `E`: a convex body
covered by finitely many planks receives total relative width `≥ 1`. -/
def Conjecture (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (K : ConvexBody E), (interior (K : Set E)).Nonempty →
    ∀ (n : ℕ) (u : Fin n → E) (lo hi : Fin n → ℝ),
      (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
      ↑K ⊆ ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
      1 ≤ ∑ i : Fin n, (hi i - lo i) / widthAlong (↑K) (u i)

/-- The conjecture with the number of planks fixed at `n`. -/
def ConjectureFor (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) : Prop :=
  ∀ (K : ConvexBody E), (interior (K : Set E)).Nonempty →
    ∀ (u : Fin n → E) (lo hi : Fin n → ℝ),
      (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
      ↑K ⊆ ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
      1 ≤ ∑ i : Fin n, (hi i - lo i) / widthAlong (↑K) (u i)

/-- The conjecture restricted to `d`-simplices with `n` planks.  By
Ambrus's lifting (`Plank/Transport.lean`), the case `d = 2n − 1` in
`ℝ^{2n−1}` already implies `ConjectureFor · n` everywhere. -/
def SimplexFor (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (d n : ℕ) : Prop :=
  ∀ (s : Affine.Simplex ℝ E d),
    (interior (convexHull ℝ (Set.range s.points))).Nonempty →
    ∀ (u : Fin n → E) (lo hi : Fin n → ℝ),
      (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
      convexHull ℝ (Set.range s.points) ⊆
        ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
      1 ≤ ∑ i : Fin n, (hi i - lo i) /
        widthAlong (convexHull ℝ (Set.range s.points)) (u i)

end Bang

end
