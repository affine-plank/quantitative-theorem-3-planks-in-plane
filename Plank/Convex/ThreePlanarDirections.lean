/- Three pairwise independent planar affine directions can be normalized
to the two coordinates and their sum, with an arbitrary constant offset. -/
module
public import Plank.Convex.ThreePlanarRelation
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ThreePlanarDirections

/-- The rescaled first two affine forms as actual planar coordinates. -/
def coordinateMap (f0 f1 : Point2 →ᵃ[ℝ] ℝ) (a b : ℝ) : Point2 →ᵃ[ℝ] Point2 :=
  AffineMap.pi ![a • f0, b • f1]

@[simp] theorem coordinateMap_zero (f0 f1 : Point2 →ᵃ[ℝ] ℝ) (a b : ℝ)
    (p : Point2) : coordinateMap f0 f1 a b p 0 = a * f0 p := rfl

@[simp] theorem coordinateMap_one (f0 f1 : Point2 →ᵃ[ℝ] ℝ) (a b : ℝ)
    (p : Point2) : coordinateMap f0 f1 a b p 1 = b * f1 p := rfl

/-- Nonzero rescaling of two independent affine directions is bijective. -/
theorem coordinateMap_bijective (f0 f1 : Point2 →ᵃ[ℝ] ℝ)
    (h01 : LinearIndependent ℝ ![f0.linear, f1.linear])
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Bijective (coordinateMap f0 f1 a b) := by
  have hdim : Fintype.card (Fin 2) = Module.finrank ℝ (Point2 →ₗ[ℝ] ℝ) := by
    rw [← (Pi.basisFun ℝ (Fin 2)).toDualEquiv.finrank_eq]
    simp
  let B := basisOfLinearIndependentOfCardEqFinrank h01 hdim
  have hB (i : Fin 2) : B i = ![f0.linear, f1.linear] i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank h01 hdim) i
  have hinj : Function.Injective (coordinateMap f0 f1 a b).linear := by
    intro x y hxy
    have h0 : f0.linear x = f0.linear y := by
      apply mul_left_cancel₀ ha
      exact congrFun hxy 0
    have h1 : f1.linear x = f1.linear y := by
      apply mul_left_cancel₀ hb
      exact congrFun hxy 1
    funext j
    have hexpand := B.sum_repr (LinearMap.proj j : Point2 →ₗ[ℝ] ℝ)
    rw [Fin.sum_univ_two] at hexpand
    have heval (z : Point2) :
        B.repr (LinearMap.proj j) 0 * f0.linear z +
          B.repr (LinearMap.proj j) 1 * f1.linear z = z j := by
      have hz := congrArg (fun L : Point2 →ₗ[ℝ] ℝ => L z) hexpand
      simpa only [hB, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, LinearMap.proj_apply] using hz
    rw [← heval x, ← heval y, h0, h1]
  exact (coordinateMap f0 f1 a b).linear_bijective_iff.mp
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Three pairwise independent planar directions become X, Y, and X+Y+c
under an actual affine equivalence. No geometric or sign assumptions occur. -/
theorem exists_normalization (f0 f1 f2 : Point2 →ᵃ[ℝ] ℝ)
    (h01 : LinearIndependent ℝ ![f0.linear, f1.linear])
    (h02 : LinearIndependent ℝ ![f0.linear, f2.linear])
    (h12 : LinearIndependent ℝ ![f1.linear, f2.linear]) :
    ∃ (a b c : ℝ) (e : Point2 ≃ᵃ[ℝ] Point2),
      a ≠ 0 ∧ b ≠ 0 ∧ (∀ p, e p 0 = a * f0 p) ∧
        (∀ p, e p 1 = b * f1 p) ∧
        (∀ p, f2 p = e p 0 + e p 1 + c) := by
  obtain ⟨a, b, c, ha, hb, hform⟩ := exists_coefficients f0 f1 f2 h01 h02 h12
  let e : Point2 ≃ᵃ[ℝ] Point2 :=
    AffineEquiv.ofBijective (coordinateMap_bijective f0 f1 h01 a b ha hb)
  exact ⟨a, b, c, e, ha, hb, fun _ => rfl, fun _ => rfl, hform⟩

end Plank.Convex.ThreePlanarDirections

/-- info: 'Plank.Convex.ThreePlanarDirections.coordinateMap_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ThreePlanarDirections.coordinateMap_bijective

/-- info: 'Plank.Convex.ThreePlanarDirections.exists_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ThreePlanarDirections.exists_normalization
