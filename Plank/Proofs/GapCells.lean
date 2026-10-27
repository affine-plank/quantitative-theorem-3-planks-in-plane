module
/-
# Proofs/GapCells — compactness, shadows, clamping

Mirror of `Plank/GapCells.lean`.  As in `Proofs/Symmetry`, guard G2
keeps this file from naming the topic file's definitions (`Plank.side`,
`Config.cell`, `Config.margin`, …), so everything here is stated over
`Plank.Core` vocabulary only:

§1 the standard triangle is compact and its shadow along `u` is the
   interval `[min 0 (min u₁ u₂), max 0 (max u₁ u₂)]`;
§2 clamping a window into that interval never widens it;
§3 continuity and the attainment of a minimum over the triangle;
§4 strict half-planes are open and convex, and a nonempty open set of
   the plane has positive area.
-/
public import Plank.Proofs.Transport

@[expose] public section


public section

noncomputable section

open Proofs.Basic Proofs.Transport MeasureTheory

namespace Proofs.GapCells

/-! ## §1  Compactness and shadows -/

theorem continuous_dot (u : ℝ × ℝ) : Continuous fun x : ℝ × ℝ => dot u x := by
  simp only [dot]
  fun_prop

theorem isCompact_stdTriangle : IsCompact stdTriangle.set := by
  rw [set_eq_convexHull]
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.toFinite _)

theorem stdTriangle_nonempty : stdTriangle.set.Nonempty :=
  ⟨stdTriangle.A, ⟨1, 0, 0, by norm_num, le_refl _, le_refl _, by norm_num, by module⟩⟩

/-- Every shadow of a point of the standard triangle lies between the
smallest and the largest vertex shadow. -/
theorem dot_shadow_bounds (u : ℝ × ℝ) {P : ℝ × ℝ} (hP : P ∈ stdTriangle) :
    min 0 (min u.1 u.2) ≤ dot u P ∧ dot u P ≤ max 0 (max u.1 u.2) := by
  obtain ⟨h1, h2, h3⟩ := (stdTriangle_mem_iff P).mp hP
  have hd : dot u P = u.1 * P.1 + u.2 * P.2 := rfl
  constructor
  · have m0 : min 0 (min u.1 u.2) ≤ 0 := min_le_left _ _
    have m1 : min 0 (min u.1 u.2) ≤ u.1 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have m2 : min 0 (min u.1 u.2) ≤ u.2 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    nlinarith
  · have m0 : (0 : ℝ) ≤ max 0 (max u.1 u.2) := le_max_left _ _
    have m1 : u.1 ≤ max 0 (max u.1 u.2) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have m2 : u.2 ≤ max 0 (max u.1 u.2) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    nlinarith

theorem shadowMin_le_shadowMax (u : ℝ × ℝ) :
    min 0 (min u.1 u.2) ≤ max 0 (max u.1 u.2) :=
  le_trans (min_le_left _ _) (le_max_left _ _)

/-- Every filled triangle is compact (a hull of three points). -/
theorem isCompact_triangle (T : Triangle) : IsCompact T.set := by
  rw [set_eq_convexHull]
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.toFinite _)

/-- A continuous function on a triangle attains a minimum. -/
theorem exists_min_on_triangle (T : Triangle) {f : (ℝ × ℝ) → ℝ}
    (hf : Continuous f) : ∃ z ∈ T.set, ∀ x ∈ T.set, f z ≤ f x := by
  obtain ⟨z, hz, hmin⟩ :=
    (isCompact_triangle T).exists_isMinOn ⟨T.A, mem_A T⟩ hf.continuousOn
  exact ⟨z, hz, fun x hx => hmin hx⟩

/-- A vertex of the standard triangle realises the shadow minimum. -/
theorem exists_vertex_min (u : ℝ × ℝ) :
    ∃ Q : ℝ × ℝ, Q ∈ stdTriangle ∧ dot u Q = min 0 (min u.1 u.2) := by
  have hA : ((0 : ℝ), (0 : ℝ)) ∈ stdTriangle :=
    (stdTriangle_mem_iff _).mpr ⟨le_refl 0, le_refl 0, by norm_num⟩
  have hB : ((1 : ℝ), (0 : ℝ)) ∈ stdTriangle :=
    (stdTriangle_mem_iff _).mpr ⟨zero_le_one, le_refl 0, by norm_num⟩
  have hC : ((0 : ℝ), (1 : ℝ)) ∈ stdTriangle :=
    (stdTriangle_mem_iff _).mpr ⟨le_refl 0, zero_le_one, by norm_num⟩
  rcases le_total (0 : ℝ) (min u.1 u.2) with h | h
  · exact ⟨_, hA, by rw [min_eq_left h]; simp [dot]⟩
  · rcases le_total u.1 u.2 with h2 | h2
    · exact ⟨_, hB, by rw [min_eq_right h, min_eq_left h2]; simp [dot]⟩
    · exact ⟨_, hC, by rw [min_eq_right h, min_eq_right h2]; simp [dot]⟩

/-! ### How the six moves act on a shadow range -/

theorem min_neg_pair (a b : ℝ) : min (0 : ℝ) (min (-a) (-b)) = -max 0 (max a b) := by
  simp only [min_def, max_def]; split_ifs <;> linarith

theorem max_neg_pair (a b : ℝ) : max (0 : ℝ) (max (-a) (-b)) = -min 0 (min a b) := by
  simp only [min_def, max_def]; split_ifs <;> linarith

theorem min_smul_pair (c a b : ℝ) (hc : 0 ≤ c) :
    min (0 : ℝ) (min (c * a) (c * b)) = c * min 0 (min a b) := by
  rw [mul_min_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc, mul_zero]

theorem max_smul_pair (c a b : ℝ) (hc : 0 ≤ c) :
    max (0 : ℝ) (max (c * a) (c * b)) = c * max 0 (max a b) := by
  rw [mul_max_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc, mul_zero]

theorem min_rot_pair (a b : ℝ) :
    min (0 : ℝ) (min (b - a) (-a)) = min 0 (min a b) - a := by
  simp only [min_def]; split_ifs <;> linarith

theorem max_rot_pair (a b : ℝ) :
    max (0 : ℝ) (max (b - a) (-a)) = max 0 (max a b) - a := by
  simp only [max_def]; split_ifs <;> linarith

theorem min_swap_pair (a b : ℝ) : min (0 : ℝ) (min b a) = min 0 (min a b) := by
  rw [min_comm b a]

theorem max_swap_pair (a b : ℝ) : max (0 : ℝ) (max b a) = max 0 (max a b) := by
  rw [max_comm b a]

/-! ## §2  Clamping a window into the shadow interval -/

/-- The clamp of `x` into `[m, M]`. -/
@[expose] def clamp (m M x : ℝ) : ℝ := max m (min x M)

theorem clamp_ge (m M x : ℝ) : m ≤ clamp m M x := le_max_left _ _

theorem clamp_le (m M x : ℝ) (h : m ≤ M) : clamp m M x ≤ M :=
  max_le h (min_le_right _ _)

/-- Clamping is monotone. -/
theorem clamp_mono (m M : ℝ) {x y : ℝ} (h : x ≤ y) : clamp m M x ≤ clamp m M y := by
  simp only [clamp, max_def, min_def]
  split_ifs <;> linarith

/-- Clamping never widens an interval. -/
theorem clamp_sub_le (m M x y : ℝ) (h : x ≤ y) :
    clamp m M y - clamp m M x ≤ y - x := by
  simp only [clamp, max_def, min_def]
  split_ifs <;> linarith

/-- A point already inside the interval is above the clamp of any lower
endpoint and below the clamp of any upper endpoint. -/
theorem clamp_le_of_mem {m M x t : ℝ} (hm : m ≤ t) (hx : x ≤ t) :
    clamp m M x ≤ t := max_le hm (le_trans (min_le_left _ _) hx)

theorem le_clamp_of_mem {m M x t : ℝ} (hM : t ≤ M) (hx : t ≤ x) :
    t ≤ clamp m M x := le_max_of_le_right (le_min hx hM)

/-! ## §3  Attainment of the minimum -/

/-- A continuous function on the standard triangle attains the infimum
of its values there (`IsCompact.exists_isMinOn`). -/
theorem exists_min_on_stdTriangle {f : (ℝ × ℝ) → ℝ} (hf : Continuous f) :
    ∃ z ∈ stdTriangle.set, f z = sInf (f '' stdTriangle.set) := by
  obtain ⟨z, hz, hmin⟩ :=
    isCompact_stdTriangle.exists_isMinOn stdTriangle_nonempty hf.continuousOn
  refine ⟨z, hz, le_antisymm ?_ ?_⟩
  · exact le_csInf ⟨f z, ⟨z, hz, rfl⟩⟩ (by rintro y ⟨x, hx, rfl⟩; exact hmin hx)
  · exact csInf_le ((isCompact_stdTriangle.image hf).bddBelow) ⟨z, hz, rfl⟩

/-- The infimum is a lower bound for every value on the triangle. -/
theorem sInf_le_of_mem {f : (ℝ × ℝ) → ℝ} (hf : Continuous f) {z : ℝ × ℝ}
    (hz : z ∈ stdTriangle.set) : sInf (f '' stdTriangle.set) ≤ f z :=
  csInf_le ((isCompact_stdTriangle.image hf).bddBelow) ⟨z, hz, rfl⟩

/-! ## §4  Strict half-planes -/

theorem isOpen_dot_lt (u : ℝ × ℝ) (c : ℝ) : IsOpen {x : ℝ × ℝ | dot u x < c} :=
  isOpen_lt (continuous_dot u) continuous_const

theorem isOpen_lt_dot (u : ℝ × ℝ) (c : ℝ) : IsOpen {x : ℝ × ℝ | c < dot u x} :=
  isOpen_lt continuous_const (continuous_dot u)

theorem convex_dot_lt (u : ℝ × ℝ) (c : ℝ) : Convex ℝ {x : ℝ × ℝ | dot u x < c} :=
  convex_halfSpace_lt ⟨fun x y => dot_add_right u x y,
    fun c x => dot_smul_right c u x⟩ c

theorem convex_lt_dot (u : ℝ × ℝ) (c : ℝ) : Convex ℝ {x : ℝ × ℝ | c < dot u x} :=
  convex_halfSpace_gt ⟨fun x y => dot_add_right u x y,
    fun c x => dot_smul_right c u x⟩ c

/-- A nonempty open subset of the plane has positive area. -/
theorem volume_pos_of_isOpen {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < volume U := hU.measure_pos volume hne

end Proofs.GapCells

end
