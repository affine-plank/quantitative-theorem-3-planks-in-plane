/- A continuous scalar image of a preconnected set cannot cross the gap
between two covering windows. Empty sets and noncompact open caps are allowed. -/
module
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false

namespace Plank.Convex.ConvexSeparatedWindows

variable {E : Type*} [TopologicalSpace E]

/-- A preconnected set covered by two separated scalar windows lies wholly
in one window. Neither compactness nor nonemptiness is required. -/
theorem allocate (S : Set E) (hS : IsPreconnected S) (f : E → ℝ)
    (hf : ContinuousOn f S) (l1 h1 l2 h2 : ℝ) (hgap : h1 < l2)
    (hcover : ∀ p ∈ S, (l1 ≤ f p ∧ f p ≤ h1) ∨ (l2 ≤ f p ∧ f p ≤ h2)) :
    (∀ p ∈ S, l1 ≤ f p ∧ f p ≤ h1) ∨
      (∀ p ∈ S, l2 ≤ f p ∧ f p ≤ h2) := by
  let m := (h1 + l2) / 2
  have hm1 : h1 < m := by dsimp [m]; linarith only [hgap]
  have hm2 : m < l2 := by dsimp [m]; linarith only [hgap]
  have hne : ∀ p ∈ S, f p ≠ m := by
    intro p hp heq
    rcases hcover p hp with hp1 | hp2
    · linarith only [hp1.2, hm1, heq]
    · linarith only [hp2.1, hm2, heq]
  rcases hS.mapsTo_Ioi_or_Iio hf hne with hright | hleft
  · right
    intro p hp
    rcases hcover p hp with hp1 | hp2
    · have hm : m < f p := hright hp
      exact False.elim (by linarith only [hp1.2, hm1, hm])
    · exact hp2
  · left
    intro p hp
    rcases hcover p hp with hp1 | hp2
    · exact hp1
    · have hm : f p < m := hleft hp
      exact False.elim (by linarith only [hp2.1, hm2, hm])

variable [AddCommGroup E] [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- In particular, the result applies to convex open caps and a scalar
functional continuous only on the cap. -/
theorem allocate_convex (S : Set E) (hS : Convex ℝ S) (f : E → ℝ)
    (hf : ContinuousOn f S) (l1 h1 l2 h2 : ℝ) (hgap : h1 < l2)
    (hcover : ∀ p ∈ S, (l1 ≤ f p ∧ f p ≤ h1) ∨ (l2 ≤ f p ∧ f p ≤ h2)) :
    (∀ p ∈ S, l1 ≤ f p ∧ f p ≤ h1) ∨
      (∀ p ∈ S, l2 ≤ f p ∧ f p ≤ h2) :=
  allocate S hS.isPreconnected f hf l1 h1 l2 h2 hgap hcover

end Plank.Convex.ConvexSeparatedWindows

/-- info: 'Plank.Convex.ConvexSeparatedWindows.allocate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexSeparatedWindows.allocate

/-- info: 'Plank.Convex.ConvexSeparatedWindows.allocate_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexSeparatedWindows.allocate_convex
