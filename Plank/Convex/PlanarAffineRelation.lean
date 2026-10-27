/- Any three planar affine functions satisfy a nontrivial affine relation. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.NormNum
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarAffineRelation
abbrev Point := Fin 3 → ℝ

/-- Three affine functions on a space of dimension at most two have a nontrivial
linear combination that is constant. Some coefficients may vanish. -/
theorem exists_relation_of_finrank_le_two {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E ≤ 2)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) :
    ∃ a : Fin 3 → ℝ, (∃ i, a i ≠ 0) ∧ ∃ d : ℝ, ∀ x, ∑ i, a i * f i x = d := by
  classical
  have hd : Module.finrank ℝ (E →ₗ[ℝ] ℝ) ≤ 2 := by
    rw [← (Module.Basis.ofVectorSpace ℝ E).toDualEquiv.finrank_eq]
    exact hdim
  have hdep : ¬ LinearIndependent ℝ (fun i => (f i).linear) := by
    intro h
    have hc : 3 ≤ Module.finrank ℝ (E →ₗ[ℝ] ℝ) := h.fintype_card_le_finrank
    exact (by norm_num : ¬ (3 ≤ 2)) (hc.trans hd)
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨a, ha, i, hi⟩ := hdep
  refine ⟨a, ⟨i, hi⟩, ∑ i, a i * f i 0, fun x => ?_⟩
  have H := congrArg (fun L : E →ₗ[ℝ] ℝ => L x) ha
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at H
  have he (i : Fin 3) : f i x = (f i).linear x + f i 0 := congrFun (f i).decomp x
  simp only [he, mul_add, Finset.sum_add_distrib, H, zero_add]

/-- The relation in ordinary planar coordinates. -/
theorem exists_relation (f : Fin 3 → (Fin 2 → ℝ) →ᵃ[ℝ] ℝ) :
    ∃ a : Point, (∃ i, a i ≠ 0) ∧ ∃ d : ℝ, ∀ x, ∑ i, a i*f i x = d := by
  exact exists_relation_of_finrank_le_two (by simp) f

end Plank.Convex.PlanarAffineRelation

/-- info: 'Plank.Convex.PlanarAffineRelation.exists_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarAffineRelation.exists_relation
