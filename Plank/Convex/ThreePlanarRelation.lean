/- A full affine relation among three pairwise independent planar directions. -/
module
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ThreePlanarDirections
abbrev Point2 := Fin 2 → ℝ

private theorem dual_dimension :
    Fintype.card (Fin 2) = Module.finrank ℝ (Point2 →ₗ[ℝ] ℝ) := by
  rw [← (Pi.basisFun ℝ (Fin 2)).toDualEquiv.finrank_eq]
  simp

private def normalBasis (L0 L1 : Point2 →ₗ[ℝ] ℝ)
    (h01 : LinearIndependent ℝ ![L0, L1]) : Module.Basis (Fin 2) ℝ (Point2 →ₗ[ℝ] ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank h01 dual_dimension

private theorem normalBasis_apply (L0 L1 : Point2 →ₗ[ℝ] ℝ)
    (h01 : LinearIndependent ℝ ![L0, L1]) (i : Fin 2) :
    normalBasis L0 L1 h01 i = ![L0, L1] i := by
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank h01 dual_dimension) i

/-- The third linear part has two nonzero coefficients in the basis formed
by the first two. All three pairwise independence hypotheses are explicit. -/
theorem exists_linear_coefficients (L0 L1 L2 : Point2 →ₗ[ℝ] ℝ)
    (h01 : LinearIndependent ℝ ![L0, L1])
    (h02 : LinearIndependent ℝ ![L0, L2])
    (h12 : LinearIndependent ℝ ![L1, L2]) :
    ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ L2 = a • L0 + b • L1 := by
  let B := normalBasis L0 L1 h01
  let a := B.repr L2 0
  let b := B.repr L2 1
  have hlin : L2 = a • L0 + b • L1 := by
    simpa only [Fin.sum_univ_two, B, normalBasis_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, a, b] using (B.sum_repr L2).symm
  have ha : a ≠ 0 := by
    intro ha
    have hdep : ∑ i : Fin 2, ![-b, 1] i • ![L1, L2] i = 0 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_smul, hlin, ha, zero_smul, zero_add]
      apply LinearMap.ext
      intro x
      change -b * L1 x + b * L1 x = 0
      ring
    have hz := Fintype.linearIndependent_iff.mp h12 ![-b, 1] hdep 1
    norm_num at hz
  have hb : b ≠ 0 := by
    intro hb
    have hdep : ∑ i : Fin 2, ![-a, 1] i • ![L0, L2] i = 0 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        one_smul, hlin, hb, zero_smul, add_zero]
      apply LinearMap.ext
      intro x
      change -a * L0 x + a * L0 x = 0
      ring
    have hz := Fintype.linearIndependent_iff.mp h02 ![-a, 1] hdep 1
    norm_num at hz
  exact ⟨a, b, ha, hb, hlin⟩

private theorem apply_eq_linear_add (f : Point2 →ᵃ[ℝ] ℝ) (p : Point2) :
    f p = f.linear p + f 0 := by
  simpa using f.map_vadd (0 : Point2) p

/-- Constants do not affect the direction normalization. The coefficients
may have either sign; pairwise independence only forces them to be nonzero. -/
theorem exists_coefficients (f0 f1 f2 : Point2 →ᵃ[ℝ] ℝ)
    (h01 : LinearIndependent ℝ ![f0.linear, f1.linear])
    (h02 : LinearIndependent ℝ ![f0.linear, f2.linear])
    (h12 : LinearIndependent ℝ ![f1.linear, f2.linear]) :
    ∃ a b c : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ ∀ p,
      f2 p = a * f0 p + b * f1 p + c := by
  obtain ⟨a, b, ha, hb, hlin⟩ :=
    exists_linear_coefficients f0.linear f1.linear f2.linear h01 h02 h12
  refine ⟨a, b, f2 0 - a * f0 0 - b * f1 0, ha, hb, fun p => ?_⟩
  rw [apply_eq_linear_add f2 p, hlin,
    apply_eq_linear_add f0 p, apply_eq_linear_add f1 p]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

end Plank.Convex.ThreePlanarDirections

/-- info: 'Plank.Convex.ThreePlanarDirections.exists_linear_coefficients' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ThreePlanarDirections.exists_linear_coefficients

/-- info: 'Plank.Convex.ThreePlanarDirections.exists_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ThreePlanarDirections.exists_coefficients
