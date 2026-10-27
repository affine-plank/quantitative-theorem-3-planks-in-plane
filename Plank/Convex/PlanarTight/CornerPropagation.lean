/- A missing open cell touching the body in just one of its boundary
hyperplanes forces that hyperplane to support the whole body. -/
module
public import Plank.Convex.ConvexCellSeparation
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.CornerPropagation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If two cuts are strict at Q and the middle cut vanishes there,
emptiness of their common positive cell forces the middle cut nonpositive
throughout the convex body. -/
theorem support (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (Q : E) (hQ : Q ∈ K) (h₀ : 0 < f 0 Q) (h₁ : f 1 Q = 0) (h₂ : 0 < f 2 Q)
    (hempty : ¬ ∃ z ∈ K, ∀ i, 0 < f i z) : ∀ z ∈ K, f 1 z ≤ 0 := by
  obtain ⟨m, hm, hsum, hrows⟩ := ConvexCellSeparation.exists_weights K hK f hempty
  have hq := hrows Q hQ
  rw [Fin.sum_univ_three, h₁, mul_zero, add_zero] at hq
  have hp₀ := mul_nonneg (hm 0) h₀.le
  have hp₂ := mul_nonneg (hm 2) h₂.le
  have hm₀ : m 0 = 0 := le_antisymm
    (nonpos_of_mul_nonpos_left (by linarith only [hq, hp₂]) h₀) (hm 0)
  have hm₂ : m 2 = 0 := le_antisymm
    (nonpos_of_mul_nonpos_left (by linarith only [hq, hp₀]) h₂) (hm 2)
  have hm₁ : m 1 = 1 := by
    simpa only [Fin.sum_univ_three, hm₀, hm₂, zero_add, add_zero] using hsum
  intro z hz
  simpa only [Fin.sum_univ_three, hm₀, hm₁, hm₂, zero_mul, one_mul, zero_add, add_zero]
    using hrows z hz

end Plank.Convex.PlanarTight.CornerPropagation

/-- info: 'Plank.Convex.PlanarTight.CornerPropagation.support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CornerPropagation.support
