module
/-
# Planks, triangles, and relative width in the plane

These definitions use normal vectors for the geometric proof.
`TriangleAffineForms` connects them to affine functions and shadow diameters;
`Plank/Audit/Triangle.lean` gives the reader-facing statement in terms of sets.
-/
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section


noncomputable section

/-! ## §1  The plane: dot products, planks, triangles -/

/-- The dot product of two vectors in the plane. -/
def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

/-- A **plank**: the strip between two parallel lines, given by a normal
direction `u ≠ 0` and bounds `lo ≤ hi` on the dot product with `u`. -/
structure Plank where
  u : ℝ × ℝ
  lo : ℝ
  hi : ℝ
  u_ne_zero : u ≠ 0
  lo_le_hi : lo ≤ hi

/-- A point lies in the plank if its dot product with the normal is
between the two bounds. -/
instance : Membership (ℝ × ℝ) Plank where
  mem p P := p.lo ≤ dot p.u P ∧ dot p.u P ≤ p.hi

/-- The plank as a subset of the plane. -/
def Plank.set (p : Plank) : Set (ℝ × ℝ) := {P | P ∈ p}

/-- A triangle in the plane: three vertices, not all on one line. -/
structure Triangle where
  A : ℝ × ℝ
  B : ℝ × ℝ
  C : ℝ × ℝ
  not_collinear : ¬ Collinear ℝ ({A, B, C} : Set (ℝ × ℝ))

/-- A point lies in the (filled) triangle if it is a weighted average of
the three vertices. -/
instance : Membership (ℝ × ℝ) Triangle where
  mem T P := ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
    P = α • T.A + β • T.B + γ • T.C

/-- The triangle as a subset of the plane. -/
def Triangle.set (T : Triangle) : Set (ℝ × ℝ) := {P | P ∈ T}

/-- The width of triangle `T` along direction `u`: the extent of the
shadow of its vertices, max minus min. -/
def Triangle.width (T : Triangle) (u : ℝ × ℝ) : ℝ :=
  max (dot u T.A) (max (dot u T.B) (dot u T.C)) -
  min (dot u T.A) (min (dot u T.B) (dot u T.C))

/-- The smallest vertex shadow of `T` along `u` — the lower end of the
shadow range `width` measures. -/
def Triangle.shadowMin (T : Triangle) (u : ℝ × ℝ) : ℝ :=
  min (dot u T.A) (min (dot u T.B) (dot u T.C))

/-- The largest vertex shadow of `T` along `u`. -/
def Triangle.shadowMax (T : Triangle) (u : ℝ × ℝ) : ℝ :=
  max (dot u T.A) (max (dot u T.B) (dot u T.C))

/-- The **relative width** of plank `p` with respect to triangle `T`:
the plank's width as a fraction of the triangle's width, both measured
along the plank's normal.  (Both carry a factor `1/‖u‖`, which cancels.) -/
def Plank.relWidth (p : Plank) (T : Triangle) : ℝ :=
  (p.hi - p.lo) / T.width p.u

/-- **The affine plank conjecture for three planks on a triangle**: if
every point of a triangle lies in one of three planks, then the sum of
the planks' relative widths is at least 1. The direct geometric proof is
`Plank.Simple.three_planks_rotation_final` in `Proofs/Rotation.lean`. -/
def ThreePlanksOnATriangle : Prop :=
  ∀ (T : Triangle) (p₁ p₂ p₃ : Plank),
    (∀ P ∈ T, P ∈ p₁ ∨ P ∈ p₂ ∨ P ∈ p₃) →
    1 ≤ p₁.relWidth T + p₂.relWidth T + p₃.relWidth T


end
