module
/-
# Proofs/PlaneBasic — elementary plane algebra

Elementary algebra for the geometric proof: bilinearity of `dot`, the
two-dimensional perpendicularity dichotomy, and the determinant form of
non-collinearity.  Nothing here is specific to planks.

The definitions come from `Plank.Plane`; the
old `Plank.Proofs.Basic` re-exports it together with `Plank.Core`.
-/
public import Plank.Plane
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Push

@[expose] public section


noncomputable section

namespace Proofs.Basic

/-! ## §1  Bilinearity of `dot` -/

@[simp] theorem dot_zero_left (v : ℝ × ℝ) : dot 0 v = 0 := by simp [dot]

@[simp] theorem dot_zero_right (u : ℝ × ℝ) : dot u 0 = 0 := by simp [dot]

theorem dot_comm (u v : ℝ × ℝ) : dot u v = dot v u := by
  simp only [dot]; ring

theorem dot_neg_left (u v : ℝ × ℝ) : dot (-u) v = -dot u v := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

theorem dot_neg_right (u v : ℝ × ℝ) : dot u (-v) = -dot u v := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

theorem dot_smul_left (c : ℝ) (u v : ℝ × ℝ) : dot (c • u) v = c * dot u v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_smul_right (c : ℝ) (u v : ℝ × ℝ) : dot u (c • v) = c * dot u v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_add_right (u v w : ℝ × ℝ) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

theorem dot_sub_right (u v w : ℝ × ℝ) : dot u (v - w) = dot u v - dot u w := by
  simp only [dot, Prod.fst_sub, Prod.snd_sub]; ring

theorem dot_add_left (u v w : ℝ × ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

/-- A vector of the plane is zero exactly when both coordinates are. -/
theorem ne_zero_iff {u : ℝ × ℝ} : u ≠ 0 ↔ u.1 ≠ 0 ∨ u.2 ≠ 0 := by
  rw [Ne, Prod.ext_iff]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h ⟨by simpa using hc.1, by simpa using hc.2⟩
  · rintro (h | h) ⟨h1, h2⟩
    · exact h (by simpa using h1)
    · exact h (by simpa using h2)

/-- The **perpendicular** of `u`, the quarter-turn `(u₁, u₂) ↦ (−u₂, u₁)`. -/
def perp (u : ℝ × ℝ) : ℝ × ℝ := (-u.2, u.1)

@[simp] theorem dot_perp (u : ℝ × ℝ) : dot u (perp u) = 0 := by
  simp only [dot, perp]; ring

/-- In the plane the orthogonal complement of a nonzero vector is the
line spanned by its perpendicular. -/
theorem exists_smul_perp {u v : ℝ × ℝ} (hu : u ≠ 0) (h : dot u v = 0) :
    ∃ t : ℝ, v = t • perp u := by
  have hd : u.1 * v.1 + u.2 * v.2 = 0 := h
  have hN : u.1 ^ 2 + u.2 ^ 2 ≠ 0 := by
    rcases ne_zero_iff.mp hu with h1 | h1
    · positivity
    · positivity
  have key1 : v.1 * (u.1 ^ 2 + u.2 ^ 2) = (u.1 * v.2 - u.2 * v.1) * -u.2 := by
    linear_combination u.1 * hd
  have key2 : v.2 * (u.1 ^ 2 + u.2 ^ 2) = (u.1 * v.2 - u.2 * v.1) * u.1 := by
    linear_combination u.2 * hd
  refine ⟨(u.1 * v.2 - u.2 * v.1) / (u.1 ^ 2 + u.2 ^ 2), Prod.ext ?_ ?_⟩
  · simp only [perp, Prod.smul_fst, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hN]
    linear_combination key1
  · simp only [perp, Prod.smul_snd, smul_eq_mul]
    rw [div_mul_eq_mul_div, eq_div_iff hN]
    linear_combination key2

/-! ## §2  Unfolding the two `Membership` instances -/

/-- Membership in a plank, spelled out. -/
theorem mem_plank_iff {p : Plank} {P : ℝ × ℝ} :
    P ∈ p ↔ p.lo ≤ dot p.u P ∧ dot p.u P ≤ p.hi := Iff.rfl

/-- Membership in a filled triangle, spelled out. -/
theorem mem_triangle_iff {T : Triangle} {P : ℝ × ℝ} :
    P ∈ T ↔ ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
      P = α • T.A + β • T.B + γ • T.C := Iff.rfl

/-! ## §3  Non-collinearity as a determinant -/

/-- The determinant of the two edge vectors at `A`. -/
def det3 (A B C : ℝ × ℝ) : ℝ :=
  (B.1 - A.1) * (C.2 - A.2) - (B.2 - A.2) * (C.1 - A.1)

/-- A vanishing determinant means the three points are collinear. -/
theorem collinear_of_det3_eq_zero {A B C : ℝ × ℝ} (h : det3 A B C = 0) :
    Collinear ℝ ({A, B, C} : Set (ℝ × ℝ)) := by
  rw [collinear_iff_of_mem (Set.mem_insert A _)]
  simp only [det3] at h
  by_cases hp : B - A = 0
  · have hBA : B = A := sub_eq_zero.mp hp
    refine ⟨C - A, ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨0, by simp [hBA]⟩
    · exact ⟨1, by simp⟩
  · have hp' : (B - A).1 ≠ 0 ∨ (B - A).2 ≠ 0 := ne_zero_iff.mp hp
    refine ⟨B - A, ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · rcases hp' with h1 | h1
      · have h1' : B.1 - A.1 ≠ 0 := by simpa using h1
        refine ⟨(x.1 - A.1) / (B.1 - A.1), Prod.ext ?_ ?_⟩
        · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub,
            smul_eq_mul]
          rw [div_mul_cancel₀ _ h1']; ring
        · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub,
            smul_eq_mul]
          field_simp
          linear_combination h
      · have h1' : B.2 - A.2 ≠ 0 := by simpa using h1
        refine ⟨(x.2 - A.2) / (B.2 - A.2), Prod.ext ?_ ?_⟩
        · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, Prod.fst_sub,
            smul_eq_mul]
          field_simp
          linear_combination -h
        · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, Prod.snd_sub,
            smul_eq_mul]
          rw [div_mul_cancel₀ _ h1']; ring

/-- The edge determinant of a triangle is nonzero. -/
theorem det3_ne_zero (T : Triangle) : det3 T.A T.B T.C ≠ 0 := fun h =>
  T.not_collinear (collinear_of_det3_eq_zero h)

/-- Collinear points have vanishing edge determinant. -/
theorem det3_eq_zero_of_collinear {A B C : ℝ × ℝ}
    (h : Collinear ℝ ({A, B, C} : Set (ℝ × ℝ))) : det3 A B C = 0 := by
  rw [collinear_iff_of_mem (Set.mem_insert A _)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨s, hs⟩ := hv B (by simp)
  obtain ⟨t, ht⟩ := hv C (by simp)
  have h1 : B.1 = s * v.1 + A.1 := by simpa using congrArg Prod.fst hs
  have h2 : B.2 = s * v.2 + A.2 := by simpa using congrArg Prod.snd hs
  have h3 : C.1 = t * v.1 + A.1 := by simpa using congrArg Prod.fst ht
  have h4 : C.2 = t * v.2 + A.2 := by simpa using congrArg Prod.snd ht
  simp only [det3, h1, h2, h3, h4]; ring

/-- …hence a nonzero determinant certifies a genuine triangle. -/
theorem not_collinear_of_det3_ne_zero {A B C : ℝ × ℝ} (h : det3 A B C ≠ 0) :
    ¬ Collinear ℝ ({A, B, C} : Set (ℝ × ℝ)) := fun hc => h (det3_eq_zero_of_collinear hc)

/-- If a nonzero direction is orthogonal to both edges at `A`, the three
points are degenerate: the plane has no room for two independent
directions in one line's orthogonal complement. -/
theorem det3_eq_zero_of_dot_edges {u : ℝ × ℝ} (hu : u ≠ 0) {A B C : ℝ × ℝ}
    (h1 : dot u (B - A) = 0) (h2 : dot u (C - A) = 0) : det3 A B C = 0 := by
  obtain ⟨s, hs⟩ := exists_smul_perp hu h1
  obtain ⟨t, ht⟩ := exists_smul_perp hu h2
  have hs1 : B.1 - A.1 = s * -u.2 := by
    simpa [perp, Prod.smul_fst] using congrArg Prod.fst hs
  have hs2 : B.2 - A.2 = s * u.1 := by
    simpa [perp, Prod.smul_snd] using congrArg Prod.snd hs
  have ht1 : C.1 - A.1 = t * -u.2 := by
    simpa [perp, Prod.smul_fst] using congrArg Prod.fst ht
  have ht2 : C.2 - A.2 = t * u.1 := by
    simpa [perp, Prod.smul_snd] using congrArg Prod.snd ht
  simp only [det3, hs1, hs2, ht1, ht2]; ring

end Proofs.Basic

end
