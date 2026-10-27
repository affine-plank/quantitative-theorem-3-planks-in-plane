/- Reflection of affine unit coordinates and their exact windows.
The historical namespaces are retained for the classification clients. -/
module
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

namespace TwoPlankClassification
/-- Reflection of one unit coordinate. -/
def reflect (X : E →ᵃ[ℝ] ℝ) : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E 1 - X

@[simp] theorem reflect_apply (X : E →ᵃ[ℝ] ℝ) (z : E) : reflect X z = 1 - X z := rfl

end TwoPlankClassification

namespace OrientedCommonChord
def coordinates (flip : Fin 3 → Bool) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (i : Fin 3) : E →ᵃ[ℝ] ℝ :=
  if flip i then TwoPlankClassification.reflect (f i) else f i

def lower (flip : Fin 3 → Bool) (lo hi : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  if flip i then 1 - hi i else lo i

def upper (flip : Fin 3 → Bool) (lo hi : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  if flip i then 1 - lo i else hi i

theorem window_iff (flip : Fin 3 → Bool) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (z : E) (i : Fin 3) :
    (lower flip lo hi i ≤ coordinates flip f i z ∧
      coordinates flip f i z ≤ upper flip lo hi i) ↔
      lo i ≤ f i z ∧ f i z ≤ hi i := by
  cases h : flip i <;>
    simp only [coordinates, lower, upper, h, Bool.false_eq_true, if_false, if_true,
      TwoPlankClassification.reflect_apply, sub_le_sub_iff_left, and_comm]

theorem width_eq (flip : Fin 3 → Bool) (lo hi : Fin 3 → ℝ) (i : Fin 3) :
    upper flip lo hi i - lower flip lo hi i = hi i - lo i := by
  cases h : flip i <;> simp [lower, upper, h]

theorem box (flip : Fin 3 → Bool) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (z : E) (i : Fin 3) (h : 0 ≤ f i z ∧ f i z ≤ 1) :
    0 ≤ coordinates flip f i z ∧ coordinates flip f i z ≤ 1 := by
  cases he : flip i
  · simpa [coordinates, he] using h
  · simp only [coordinates, he, ↓reduceIte, TwoPlankClassification.reflect_apply]
    constructor <;> linarith only [h.1, h.2]

end OrientedCommonChord
end Plank.Convex.PlanarTight
