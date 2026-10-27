/- Fewer linear constraints than ambient dimensions leave a nonzero motion. -/
module
public import Plank.Convex.FiniteExtremeMinimum
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Logic.Equiv.Sum
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators Topology
namespace Plank.Convex.ExtremeMinimumRank

theorem common_kernel_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {J : Type*} [Fintype J]
    (f : J → E →L[ℝ] ℝ) (hdim : Fintype.card J < Module.finrank ℝ E) :
    ∃ d : E, d ≠ 0 ∧ ∀ j, f j d = 0 := by
  by_contra hn
  have hk (d : E) (hd : ∀ j, f j d = 0) : d = 0 := by
    by_contra hd0
    exact hn ⟨d, hd0, hd⟩
  let F : E →ₗ[ℝ] (J → ℝ) := LinearMap.pi fun j => (f j).toLinearMap
  have hi : Function.Injective F := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hk
    intro j
    rw [map_sub]
    exact sub_eq_zero.mpr (congrFun hxy j)
  have h := F.finrank_le_finrank_of_injective hi
  simp only [Module.finrank_pi] at h
  exact (not_le_of_gt hdim) h

theorem not_extreme_of_few_constraints {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {J : Type*} [Fintype J]
    (s U : Set E) (x : E) (hx : x ∈ s.extremePoints ℝ)
    (hU : IsOpen U) (hxU : x ∈ U)
    (f : J → E →L[ℝ] ℝ) (c : J → ℝ)
    (hcur : ∀ j, c j ≤ f j x)
    (hlocal : ∀ y ∈ U, (∀ j, c j ≤ f j y) → y ∈ s)
    (hdim : Fintype.card J < Module.finrank ℝ E) : False := by
  obtain ⟨d, hd, hf⟩ := common_kernel_nonzero f hdim
  exact hd (Plank.Convex.ExtremeMinimum.extreme_active_kernel s U x hx hU hxU f c hcur
    hlocal d (fun j _ => hf j))

/-- A local linear model at an extreme point has at least as many active rows as dimensions. -/
theorem card_active_ge_finrank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {J : Type*} [Fintype J]
    (s U : Set E) (x : E) (hx : x ∈ s.extremePoints ℝ)
    (hU : IsOpen U) (hxU : x ∈ U)
    (f : J → E →L[ℝ] ℝ) (c : J → ℝ)
    (hcur : ∀ j, c j ≤ f j x)
    (hlocal : ∀ y ∈ U, (∀ j, c j ≤ f j y) → y ∈ s) :
    Module.finrank ℝ E ≤ Nat.card {j : J // c j = f j x} := by
  classical
  rw [Nat.card_eq_fintype_card]
  by_contra! hdim
  obtain ⟨d, hd, hf⟩ := common_kernel_nonzero
    (fun j : {j : J // c j = f j x} => f j.val) hdim
  exact hd (ExtremeMinimum.extreme_active_kernel s U x hx hU hxU f c hcur hlocal d
    (fun j hj => hf ⟨j, hj⟩))

/-- If the entire local model has at most as many rows as dimensions, every row is active. -/
theorem all_active_of_card_le_finrank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {J : Type*} [Fintype J]
    (s U : Set E) (x : E) (hx : x ∈ s.extremePoints ℝ)
    (hU : IsOpen U) (hxU : x ∈ U)
    (f : J → E →L[ℝ] ℝ) (c : J → ℝ)
    (hcur : ∀ j, c j ≤ f j x)
    (hlocal : ∀ y ∈ U, (∀ j, c j ≤ f j y) → y ∈ s)
    (hdim : Fintype.card J ≤ Module.finrank ℝ E) : ∀ j, c j = f j x := by
  classical
  have hcard := card_active_ge_finrank s U x hx hU hxU f c hcur hlocal
  rw [Nat.card_eq_fintype_card] at hcard
  intro j
  by_contra hn
  exact (not_lt_of_ge (hdim.trans hcard)) (Fintype.card_subtype_lt hn)

/-- Count active rows in two families without changing the local neighbourhood. -/
theorem card_active_sum_ge_finrank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {J I : Type*} [Fintype J] [Fintype I]
    (s U : Set E) (x : E) (hx : x ∈ s.extremePoints ℝ) (hU : IsOpen U) (hxU : x ∈ U)
    (f : J → E →L[ℝ] ℝ) (c : J → ℝ) (g : I → E →L[ℝ] ℝ) (d : I → ℝ)
    (hf : ∀ j, c j ≤ f j x) (hg : ∀ i, d i ≤ g i x)
    (hlocal : ∀ y ∈ U, (∀ j, c j ≤ f j y) → (∀ i, d i ≤ g i y) → y ∈ s) :
    Module.finrank ℝ E ≤ Nat.card {j : J // c j = f j x} + Nat.card {i : I // d i = g i x} := by
  have H := card_active_ge_finrank s U x hx hU hxU (Sum.elim f g) (Sum.elim c d)
    (by intro z; cases z with | inl j => exact hf j | inr i => exact hg i)
    (fun y hy h => hlocal y hy (fun j => h (.inl j)) (fun i => h (.inr i)))
  rw [Nat.card_congr (Equiv.subtypeSum (p := fun z => Sum.elim c d z = Sum.elim f g z x)),
    Nat.card_sum] at H
  exact H

end Plank.Convex.ExtremeMinimumRank
