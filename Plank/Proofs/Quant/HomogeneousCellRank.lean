/- An extra scalar parameter turns root-concavity into a strict cell-count
bound. The curvature data are explicit; no geometric realization is assumed. -/
module

public import Plank.Proofs.Quant.ComponentRank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.HomogeneousCellRank

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

def liftGradient (d A : ℝ) (g : E →ₗ[ℝ] ℝ) : E × ℝ →ₗ[ℝ] ℝ :=
  g.comp (LinearMap.fst ℝ E ℝ) + (d*A) • LinearMap.snd ℝ E ℝ

@[simp] theorem liftGradient_apply (d A : ℝ) (g : E →ₗ[ℝ] ℝ) (w : E × ℝ) :
    liftGradient d A g w = g w.1+d*A*w.2 := rfl

def liftCurvature (d A : ℝ) (g : E →ₗ[ℝ] ℝ) (H : E → ℝ) (w : E × ℝ) : ℝ :=
  H w.1+2*(d-1)*w.2*g w.1+d*(d-1)*A*w.2^2

/-- Completing the square removes all dependence on the extra coordinate
on the lifted gradient kernel. Only positivity of `d*A` is needed. -/
theorem liftCurvature_nonpos_on_kernel {d A : ℝ} (hd : 0<d) (hA : 0<A)
    (g : E →ₗ[ℝ] ℝ) (H : E → ℝ)
    (hc : ∀ z, d*A*H z ≤ (d-1)*(g z)^2)
    (w : E × ℝ) (hw : liftGradient d A g w=0) :
    liftCurvature d A g H w ≤ 0 := by
  have heq : g w.1 = -(d*A*w.2) := by
    change g w.1+d*A*w.2=0 at hw
    linarith only [hw]
  have he : d*A*liftCurvature d A g H w = d*A*H w.1-(d-1)*(g w.1)^2 := by
    dsimp only [liftCurvature]
    rw [heq]
    ring
  apply nonpos_of_mul_nonpos_right (a := d*A) _ (mul_pos hd hA)
  rw [he]
  exact sub_nonpos.mpr (hc w.1)

/-- A positive lifted total curvature requires one more cell than the
parameter dimension. No square gradient system or inverse is needed. -/
theorem dimension_lt_components [Module.Finite ℝ E]
    (d : ℝ) (hd : 0<d) (A : ι → ℝ) (g : ι → E →ₗ[ℝ] ℝ)
    (H : ι → E → ℝ) (hA : ∀ i, 0<A i)
    (hc : ∀ i z, d*A i*H i z ≤ (d-1)*(g i z)^2)
    (hpos : ∀ w : E × ℝ, w≠0 → 0<∑ i, liftCurvature d (A i) (g i) (H i) w) :
    Module.finrank ℝ E < Fintype.card ι := by
  have hrank := ComponentRank.dimension_le_components
    (fun i => liftGradient d (A i) (g i))
    (fun i => liftCurvature d (A i) (g i) (H i))
    (fun i => liftCurvature_nonpos_on_kernel hd (hA i) (g i) (H i) (hc i)) hpos
  have hs : Module.finrank ℝ E+1 ≤ Fintype.card ι := by
    simpa only [Module.finrank_prod, Module.finrank_self] using hrank
  exact Nat.lt_of_succ_le hs

end Plank.HomogeneousCellRank
