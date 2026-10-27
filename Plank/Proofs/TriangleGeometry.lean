module
/-
# Elementary geometry of a triangle

Widths are spreads of vertex values. The filled triangle is their convex
hull, so affine levels attain their extrema at vertices. These lemmas keep
the namespace `Proofs.Transport`; the older Transport module re-exports them.
-/
public import Plank.Proofs.PlaneBasic
public import Mathlib.Analysis.Convex.Combination

@[expose] public section


noncomputable section

open Proofs.Basic

namespace Proofs.Transport

/-! ## §0  The width toolbox -/

/-- Shifting all three shadows by a constant does not change the spread. -/
theorem spread_shift (a b c : ℝ) :
    max 0 (max (b - a) (c - a)) - min 0 (min (b - a) (c - a))
      = max a (max b c) - min a (min b c) := by
  rw [show (0 : ℝ) = a - a from (sub_self a).symm, max_sub_sub_right,
    max_sub_sub_right, min_sub_sub_right, min_sub_sub_right]
  ring

theorem width_neg (T : Triangle) (u : ℝ × ℝ) : T.width (-u) = T.width u := by
  simp only [Triangle.width, dot_neg_left, max_neg_neg, min_neg_neg]
  ring

theorem width_smul (T : Triangle) (c : ℝ) (u : ℝ × ℝ) :
    T.width (c • u) = |c| * T.width u := by
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    simp only [Triangle.width, dot_smul_left]
    rw [mul_sub, mul_max_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc,
      mul_min_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc]
  · have hc' : (0 : ℝ) ≤ -c := by linarith
    have hsm : c • u = -((-c) • u) := by
      rw [neg_smul, neg_neg]
    rw [hsm, width_neg, abs_of_neg hc]
    simp only [Triangle.width, dot_smul_left]
    rw [mul_sub, mul_max_of_nonneg _ _ hc', mul_max_of_nonneg _ _ hc',
      mul_min_of_nonneg _ _ hc', mul_min_of_nonneg _ _ hc']

theorem width_pos (T : Triangle) {u : ℝ × ℝ} (hu : u ≠ 0) : 0 < T.width u := by
  rcases lt_or_ge 0 (T.width u) with h | h
  · exact h
  · exfalso
    -- a nonpositive spread forces the three shadows to coincide
    set a := dot u T.A with ha
    set b := dot u T.B with hb
    set c := dot u T.C with hc
    have hmax : max a (max b c) ≤ min a (min b c) := by
      have : T.width u = max a (max b c) - min a (min b c) := rfl
      linarith [this ▸ h]
    have hba : b = a := le_antisymm
      (le_trans (le_max_of_le_right (le_max_left b c))
        (le_trans hmax (min_le_left _ _)))
      (le_trans (le_max_left a _) (le_trans hmax
        (le_trans (min_le_right _ _) (min_le_left b c))))
    have hca : c = a := le_antisymm
      (le_trans (le_max_of_le_right (le_max_right b c))
        (le_trans hmax (min_le_left _ _)))
      (le_trans (le_max_left a _) (le_trans hmax
        (le_trans (min_le_right _ _) (min_le_right b c))))
    refine det3_ne_zero T (det3_eq_zero_of_dot_edges hu ?_ ?_)
    · rw [dot_sub_right, ← ha, ← hb, hba]; ring
    · rw [dot_sub_right, ← ha, ← hc, hca]; ring

/-- The filled triangle is convex. -/
theorem convex_triangle (T : Triangle) : Convex ℝ T.set := by
  rintro x ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ y ⟨α', β', γ', hα', hβ', hγ', hsum', rfl⟩
    s t hs ht hst
  refine ⟨s * α + t * α', s * β + t * β', s * γ + t * γ', ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · nlinarith [hsum, hsum', hst]
  · module

theorem set_eq_convexHull (T : Triangle) :
    T.set = convexHull ℝ ({T.A, T.B, T.C} : Set (ℝ × ℝ)) := by
  apply Set.Subset.antisymm
  · rintro P ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩
    have hmem : ∀ i : Fin 3, ![T.A, T.B, T.C] i ∈ convexHull ℝ
        ({T.A, T.B, T.C} : Set (ℝ × ℝ)) := by
      intro i
      refine subset_convexHull ℝ _ ?_
      fin_cases i <;> simp
    have := (convex_convexHull ℝ ({T.A, T.B, T.C} : Set (ℝ × ℝ))).sum_mem
      (t := (Finset.univ : Finset (Fin 3))) (w := ![α, β, γ])
      (z := ![T.A, T.B, T.C])
      (by intro i _; fin_cases i <;> assumption)
      (by simp [Fin.sum_univ_three]; linarith)
      (fun i _ => hmem i)
    simpa [Fin.sum_univ_three] using this
  · refine convexHull_min ?_ (convex_triangle T)
    rintro P (rfl | rfl | rfl)
    · exact ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩
    · exact ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩
    · exact ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, by module⟩

/-- Every vertex of a triangle belongs to it. -/
theorem mem_A (T : Triangle) : T.A ∈ T :=
  ⟨1, 0, 0, by norm_num, le_refl _, le_refl _, by norm_num, by module⟩

theorem mem_B (T : Triangle) : T.B ∈ T :=
  ⟨0, 1, 0, le_refl _, by norm_num, le_refl _, by norm_num, by module⟩

theorem mem_C (T : Triangle) : T.C ∈ T :=
  ⟨0, 0, 1, le_refl _, le_refl _, by norm_num, by norm_num, by module⟩

/-- A shadow of a point of a triangle never exceeds the vertex shadows. -/
theorem dot_le_max (T : Triangle) (u : ℝ × ℝ) {X : ℝ × ℝ} (hX : X ∈ T) :
    dot u X ≤ max (dot u T.A) (max (dot u T.B) (dot u T.C)) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := hX
  have hd : dot u (α • T.A + β • T.B + γ • T.C)
      = α * dot u T.A + β * dot u T.B + γ * dot u T.C := by
    rw [dot_add_right, dot_add_right, dot_smul_right, dot_smul_right, dot_smul_right]
  rw [hd]
  have m0 : dot u T.A ≤ max (dot u T.A) (max (dot u T.B) (dot u T.C)) :=
    le_max_left _ _
  have m1 : dot u T.B ≤ max (dot u T.A) (max (dot u T.B) (dot u T.C)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have m2 : dot u T.C ≤ max (dot u T.A) (max (dot u T.B) (dot u T.C)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hM : (α + β + γ) * max (dot u T.A) (max (dot u T.B) (dot u T.C))
      = max (dot u T.A) (max (dot u T.B) (dot u T.C)) := by rw [hsum]; ring
  nlinarith [mul_nonneg hα (sub_nonneg.mpr m0), mul_nonneg hβ (sub_nonneg.mpr m1),
    mul_nonneg hγ (sub_nonneg.mpr m2)]

theorem min_le_dot (T : Triangle) (u : ℝ × ℝ) {X : ℝ × ℝ} (hX : X ∈ T) :
    min (dot u T.A) (min (dot u T.B) (dot u T.C)) ≤ dot u X := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩ := hX
  have hd : dot u (α • T.A + β • T.B + γ • T.C)
      = α * dot u T.A + β * dot u T.B + γ * dot u T.C := by
    rw [dot_add_right, dot_add_right, dot_smul_right, dot_smul_right, dot_smul_right]
  rw [hd]
  have m0 : min (dot u T.A) (min (dot u T.B) (dot u T.C)) ≤ dot u T.A :=
    min_le_left _ _
  have m1 : min (dot u T.A) (min (dot u T.B) (dot u T.C)) ≤ dot u T.B :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have m2 : min (dot u T.A) (min (dot u T.B) (dot u T.C)) ≤ dot u T.C :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hM : (α + β + γ) * min (dot u T.A) (min (dot u T.B) (dot u T.C))
      = min (dot u T.A) (min (dot u T.B) (dot u T.C)) := by rw [hsum]; ring
  nlinarith [mul_nonneg hα (sub_nonneg.mpr m0), mul_nonneg hβ (sub_nonneg.mpr m1),
    mul_nonneg hγ (sub_nonneg.mpr m2)]

end Proofs.Transport

end
