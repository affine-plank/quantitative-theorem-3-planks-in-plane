/- A bounded sublevel polyhedron with at most dimension-many rows has a common row root. -/
module
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Plank.Convex.BoundedPolyhedron
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ray_zero (S : Set E) (hS : Bornology.IsBounded S) (B d : E)
    (h : ∀ t : ℝ, 0 ≤ t → B + t • d ∈ S) : d = 0 := by
  by_contra hd
  obtain ⟨M, hM⟩ := hS.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt ((M + ‖B‖) / ‖d‖)
  have hn := (div_lt_iff₀ (norm_pos_iff.mpr hd)).mp hn
  have H := norm_sub_le (B + (n : ℝ) • d) B
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)] at H
  exact hn.not_ge (H.trans (add_le_add (hM _ (h n (Nat.cast_nonneg n))) le_rfl))

/-- Boundedness rules out every row-kernel direction and forces the common
root to have cost no greater than the original feasible point. -/
theorem bounded_root [FiniteDimensional ℝ E] {J : Type*} [Fintype J]
    (f : J → E →ₗ[ℝ] ℝ) (c : J → ℝ) (cost : E →ₗ[ℝ] ℝ) (B : E)
    (hB : ∀ j, c j ≤ f j B)
    (hbounded : Bornology.IsBounded {Y | (∀ j, c j ≤ f j Y) ∧ cost Y ≤ cost B})
    (hcard : Fintype.card J ≤ Module.finrank ℝ E) :
    Fintype.card J = Module.finrank ℝ E ∧
      ∃ Y, (∀ j, c j = f j Y) ∧ cost Y ≤ cost B := by
  have no_ray (d : E) (hf : ∀ j, 0 ≤ f j d) (hc : cost d ≤ 0) : d = 0 := by
    apply ray_zero _ hbounded B d
    intro t ht
    simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul]
    exact ⟨fun j => (hB j).trans (le_add_of_nonneg_right (mul_nonneg ht (hf j))),
      add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht hc)⟩
  have ker_zero (d : E) (hd : ∀ j, f j d = 0) : d = 0 := by
    by_cases hc : cost d ≤ 0
    · exact no_ray d (fun j => (hd j).ge) hc
    · exact neg_eq_zero.mp (no_ray (-d) (fun j => by simp [hd]) (by simp; linarith))
  let F : E →ₗ[ℝ] (J → ℝ) := LinearMap.pi f
  have hinj : Function.Injective F := by
    intro u v huv
    apply sub_eq_zero.mp
    apply ker_zero (u-v)
    intro j
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun huv j)
  have hdim : Module.finrank ℝ E = Module.finrank ℝ (J → ℝ) :=
    le_antisymm (F.finrank_le_finrank_of_injective hinj) (by simpa using hcard)
  obtain ⟨Y, hY⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj c
  refine ⟨by simpa using hdim.symm, Y, fun j => (congrFun hY j).symm, ?_⟩
  by_contra! hc
  have he := no_ray (B-Y) (fun j => by
    rw [map_sub, show f j Y = c j from congrFun hY j]
    exact sub_nonneg.mpr (hB j)) (by rw [map_sub]; linarith only [hc])
  exact hc.ne (congrArg cost (sub_eq_zero.mp he))

end Plank.Convex.BoundedPolyhedron
