/- Pair-support adapters for the shared Hahn–Banach separator. -/
module
public import Plank.Convex.ConvexPairSeparator
public import Plank.Convex.ConvexPairSegments
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ConvexCellSeparation
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The witness-based form of the shared positive pair separator. -/
theorem exists_pos_pair (K : Set E) (hK : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (p q : E) (hp : p ∈ K) (hq : q ∈ K) (hgp : 0 < g p) (hhq : 0 < h q)
    (he : ¬ ∃ x ∈ K, 0 < g x ∧ 0 < h x) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, g x + a * h x ≤ 0 :=
  exists_pos_separator K hK g h ⟨p, hp, hgp⟩ ⟨q, hq, hhq⟩ he


end Plank.Convex.ConvexCellSeparation

/-- info: 'Plank.Convex.ConvexCellSeparation.exists_pos_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCellSeparation.exists_pos_pair
