/- Dense linear perturbations avoid chart walls and singular Hessians. -/
module

public import Plank.Proofs.Quant.QuadraticChartCalculus
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.QuadraticChartPerturbations

open Set PlanarPolygonCharts QuadraticChartCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A hyperplane in the space of perturbing covectors. -/
def evaluationWall (z : E) (c : ℝ) : (E →L[ℝ] ℝ) →ᵃ[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ z).toLinearMap.toAffineMap + AffineMap.const ℝ _ c

omit [FiniteDimensional ℝ E] in
@[simp] theorem evaluationWall_apply (z : E) (c : ℝ) (v : E →L[ℝ] ℝ) :
    evaluationWall z c v = v z+c := rfl

theorem evaluationWall_ne_zero (z : E) (c : ℝ) (hz : z ≠ 0) :
    evaluationWall z c ≠ 0 := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℝ hz
  intro he
  have h0 := congrArg (fun F : (E →L[ℝ] ℝ) →ᵃ[ℝ] ℝ => F 0) he
  have h1 := congrArg (fun F : (E →L[ℝ] ℝ) →ᵃ[ℝ] ℝ => F l.toContinuousLinearMap) he
  change (0 : ℝ)+c = 0 at h0
  change l z+c = 0 at h1
  exact hl (by linarith only [h0, h1])

theorem hessian_surjective_of_injective (q : QuadraticFormula E)
    (h : Function.Injective (hessian q)) : Function.Surjective (hessian q) := by
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    calc
      Module.finrank ℝ E = Module.finrank ℝ (E →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
      _ = Module.finrank ℝ (E →L[ℝ] ℝ) :=
        (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp h

theorem derivative_from_zero (q : QuadraticFormula E) (x z : E) :
    derivative q x z = derivative q 0 z+hessian q x z := by
  have h := congrArg (fun v : E →L[ℝ] ℝ => v z) (derivative_add q 0 x)
  simpa only [zero_add, add_apply] using h

/-- If a Hessian is singular, one proper affine hyperplane contains
the entire gradient image. Its normal is a nonzero kernel direction. -/
theorem exists_singular_image_wall (q : QuadraticFormula E) :
    ∃ L : (E →L[ℝ] ℝ) →ᵃ[ℝ] ℝ, L ≠ 0 ∧
      (¬Function.Injective (hessian q) → ∀ x : E, L (derivative q x) = 0) := by
  classical
  by_cases hi : Function.Injective (hessian q)
  · refine ⟨AffineMap.const ℝ _ 1, ?_, fun hn => (hn hi).elim⟩
    intro h
    have := congrArg (fun L : (E →L[ℝ] ℝ) →ᵃ[ℝ] ℝ => L 0) h
    simp at this
  · obtain ⟨z, hz, hker⟩ : ∃ z : E, z ≠ 0 ∧ hessian q z = 0 := by
      unfold Function.Injective at hi
      push Not at hi
      obtain ⟨x, y, heq, hne⟩ := hi
      exact ⟨x-y, sub_ne_zero.mpr hne, by rw [map_sub, heq, sub_self]⟩
    refine ⟨evaluationWall z (-derivative q 0 z), evaluationWall_ne_zero z _ hz, ?_⟩
    intro _ x
    rw [evaluationWall_apply, derivative_from_zero, hessian_symm, hker, zero_apply]
    ring

/-- The gradient image of any nontrivial wall lies in a proper affine
hyperplane of perturbing covectors. For invertible Hessians this is
constructed by solving for the original wall normal; the singular case
uses the preceding kernel-direction hyperplane. -/
theorem exists_wall_image_wall (q : QuadraticFormula E) (F : E →ᵃ[ℝ] ℝ) :
    ∃ L : (E →L[ℝ] ℝ) →ᵃ[ℝ] ℝ, L ≠ 0 ∧
      ∀ x : E, F ≠ 0 → F x = 0 → L (derivative q x) = 0 := by
  classical
  by_cases hF : F.linear = 0
  · refine ⟨AffineMap.const ℝ _ 1, ?_, ?_⟩
    · intro h
      have := congrArg (fun L : (E →L[ℝ] ℝ) →ᵃ[ℝ] ℝ => L 0) h
      simp at this
    · intro x hn hx
      exfalso
      apply hn
      ext y
      change F y = 0
      have h := F.linearMap_vsub y x
      simpa only [hF, LinearMap.zero_apply, vsub_eq_sub, hx, sub_zero] using h.symm
  · by_cases hi : Function.Injective (hessian q)
    · obtain ⟨z, hz⟩ := hessian_surjective_of_injective q hi F.linear.toContinuousLinearMap
      have hn : z ≠ 0 := by
        intro he
        rw [he, map_zero] at hz
        apply hF
        ext y
        have hy := congrArg (fun v : E →L[ℝ] ℝ => v y) hz
        exact hy.symm
      refine ⟨evaluationWall z (F 0-derivative q 0 z), evaluationWall_ne_zero z _ hn, ?_⟩
      intro x _ hx
      have hFx := affine_eval_line F 0 x 1
      simp only [zero_add, one_smul, one_mul, hx] at hFx
      rw [evaluationWall_apply, derivative_from_zero, hessian_symm, hz]
      change derivative q 0 z+F.linear x+(F 0-derivative q 0 z) = 0
      linarith only [hFx]
    · obtain ⟨L, hL, hzero⟩ := exists_singular_image_wall q
      exact ⟨L, hL, fun x _ _ => hzero hi x⟩

/-- A good linear perturbation can be the gradient of a chart only at
an off-wall point of a chart with injective Hessian. -/
def Good {σ τ : Type*} (q : σ → QuadraticFormula E) (F : τ → E →ᵃ[ℝ] ℝ)
    (v : E →L[ℝ] ℝ) : Prop :=
  ∀ i x, derivative (q i) x = v → Function.Injective (hessian (q i)) ∧
    ∀ w, F w ≠ 0 → F w x ≠ 0

/-- The excluded values are a finite family of explicitly constructed
proper affine hyperplanes. Good perturbations therefore form a dense set. -/
theorem dense_good {σ τ : Type*} [Finite σ] [Finite τ]
    (q : σ → QuadraticFormula E) (F : τ → E →ᵃ[ℝ] ℝ) :
    Dense {v : E →L[ℝ] ℝ | Good q F v} := by
  classical
  choose Ls hs using fun i => exists_singular_image_wall (q i)
  choose Lw hw using fun p : σ × τ => exists_wall_image_wall (q p.1) (F p.2)
  let L : σ ⊕ (σ × τ) → (E →L[ℝ] ℝ) →ᵃ[ℝ] ℝ := Sum.elim Ls Lw
  apply (dense_off_walls L).mono
  intro v hv i x hx
  constructor
  · by_contra hi
    have hn := hv (Sum.inl i) (hs i).1
    have hz := (hs i).2 hi x
    rw [hx] at hz
    exact hn hz
  · intro w hF hzero
    have hn := hv (Sum.inr (i,w)) (hw (i,w)).1
    have hz := (hw (i,w)).2 x hF hzero
    rw [hx] at hz
    exact hn hz

end Plank.QuadraticChartPerturbations
