/-
Copyright (c) 2026 Zaz Brown. All rights reserved.
Supporting lemmas for the Affine Plank Conjecture.
Properties of `minWidth` and homothety scaling.
-/
module

public import Geometry.AffinePlankConjecture
public import Geometry.WidthAlong
public import Mathlib.Data.Real.Pointwise

@[expose] public section

open scoped RealInnerProductSpace Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Homothety scaling of `widthAlong` -/

/-- Key identity: `widthAlong (c • K) u = widthAlong K (c • u)`. -/
theorem widthAlong_smul_set_eq {K : Set E} (c : ℝ) (u : E) :
    widthAlong (c • K) u = widthAlong K (c • u) := by
  unfold widthAlong
  congr 1 <;> {
    congr 1; ext y; simp only [Set.mem_image, Set.mem_smul_set]; constructor
    · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, by rw [real_inner_smul_left, inner_smul_right]⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨c • k, ⟨k, hk, rfl⟩, by rw [real_inner_smul_left, inner_smul_right]⟩
  }

/-- `widthAlong (c • K) u = |c| * widthAlong K u` (homothety scaling). -/
theorem widthAlong_smul_set {K : Set E} (hne : K.Nonempty) (hbdd : Bornology.IsBounded K)
    (c : ℝ) (u : E) :
    widthAlong (c • K) u = |c| * widthAlong K u := by
  rw [widthAlong_smul_set_eq, widthAlong_smul hne hbdd]

/-! ## Properties of `minWidth` -/

/-- The set `{widthAlong K u / ‖u‖ | u ≠ 0}` is nonempty when `E` is nontrivial. -/
theorem minWidth_image_nonempty [Nontrivial E] (K : Set E) :
    ((fun u => widthAlong K u / ‖u‖) '' {u : E | u ≠ 0}).Nonempty := by
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  exact ⟨widthAlong K u / ‖u‖, u, hu, rfl⟩

/-- `minWidth` is nonneg for a `ConvexBody`. -/
theorem minWidth_nonneg [FiniteDimensional ℝ E] [Nontrivial E] (K : ConvexBody E) :
    0 ≤ minWidth (↑K : Set E) := by
  unfold minWidth
  apply le_csInf (minWidth_image_nonempty _)
  rintro y ⟨u, -, rfl⟩
  exact div_nonneg (widthAlong_nonneg_convexBody K u) (norm_nonneg u)

/-- `minWidth K ≤ widthAlong K u / ‖u‖` for `u ≠ 0`. -/
theorem minWidth_le_widthAlong_div_norm [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) {u : E} (hu : u ≠ 0) :
    minWidth (↑K : Set E) ≤ widthAlong (↑K : Set E) u / ‖u‖ := by
  unfold minWidth
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨v, -, rfl⟩
    exact div_nonneg (widthAlong_nonneg_convexBody K v) (norm_nonneg v)
  · exact Set.mem_image_of_mem _ hu

/-- `widthAlong K u ≥ minWidth K * ‖u‖` for `u ≠ 0`. -/
theorem widthAlong_ge_minWidth_mul_norm [FiniteDimensional ℝ E] [Nontrivial E]
    (K : ConvexBody E) {u : E} (hu : u ≠ 0) :
    minWidth (↑K : Set E) * ‖u‖ ≤ widthAlong (↑K : Set E) u :=
  (le_div_iff₀ (norm_pos_iff.mpr hu)).mp (minWidth_le_widthAlong_div_norm K hu)

/-- `minWidth` scales under homothety: `minWidth (c • K) = |c| * minWidth K`. -/
theorem minWidth_smul_set [Nontrivial E] {K : Set E} (hne : K.Nonempty)
    (hbdd : Bornology.IsBounded K) (c : ℝ) :
    minWidth (c • K) = |c| * minWidth K := by
  unfold minWidth
  have him : (fun u => widthAlong (c • K) u / ‖u‖) '' {u : E | u ≠ 0} =
      (fun u => |c| * widthAlong K u / ‖u‖) '' {u : E | u ≠ 0} := by
    ext y; simp only [Set.mem_image, Set.mem_setOf_eq]; constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by rw [widthAlong_smul_set hne hbdd]⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by rw [widthAlong_smul_set hne hbdd]⟩
  rw [him]; simp_rw [mul_div_assoc]
  rw [show (fun u => |c| * (widthAlong K u / ‖u‖)) '' {u : E | u ≠ 0} =
    |c| • ((fun u => widthAlong K u / ‖u‖) '' {u : E | u ≠ 0}) from by
      ext y; simp only [Set.mem_image, Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
      constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩]
  rw [Real.sInf_smul_of_nonneg (abs_nonneg c)]; simp [smul_eq_mul]
