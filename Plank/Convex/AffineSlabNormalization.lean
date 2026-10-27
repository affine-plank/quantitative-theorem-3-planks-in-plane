/- Clipping normalized slab windows preserves coverage and never increases
their summed relative widths. The coordinate map need not be affine or injective. -/
module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Tactic.Ring.Basic
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.AffineSlabNormalization

open scoped BigOperators

def clamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp_nonneg (t : ℝ) : 0 ≤ clamp t := le_max_left _ _

theorem clamp_le_one (t : ℝ) : clamp t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem clamp_mono : Monotone clamp :=
  fun _ _ hab => max_le_max le_rfl (min_le_min le_rfl hab)

theorem clamp_self (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : clamp t = t := by
  rw [clamp, min_eq_right ht.2, max_eq_right ht.1]

/-- Ordered endpoint clipping cannot increase interval length. -/
theorem clamp_sub_le (l h : ℝ) (hlh : l ≤ h) : clamp h - clamp l ≤ h - l := by
  have hmax : |clamp h - clamp l| ≤ |min 1 h - min 1 l| := by
    simpa only [clamp, max_comm] using
      abs_max_sub_max_le_abs (min 1 h) (min 1 l) (0 : ℝ)
  have hmin : |min 1 h - min 1 l| ≤ |h - l| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (h - l))] using
      abs_min_sub_min_le_max (1 : ℝ) h (1 : ℝ) l
  exact (le_abs_self _).trans ((hmax.trans hmin).trans_eq
    (abs_of_nonneg (sub_nonneg.mpr hlh)))

theorem clamp_interval (l h z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1)
    (hlh : l ≤ z ∧ z ≤ h) : clamp l ≤ z ∧ z ≤ clamp h := by
  simpa only [clamp_self z hz] using
    And.intro (clamp_mono hlh.1) (clamp_mono hlh.2)

variable {I E : Type*}

def lower (m W lo : I → ℝ) (i : I) : ℝ := clamp ((lo i - m i) / W i)

def width (m W lo hi : I → ℝ) (i : I) : ℝ :=
  clamp ((hi i - m i) / W i) - lower m W lo i

theorem lower_add_width (m W lo hi : I → ℝ) (i : I) :
    lower m W lo i + width m W lo hi i = clamp ((hi i - m i) / W i) := by
  unfold width
  ring

theorem width_nonneg (m W lo hi : I → ℝ) (hW : ∀ i, 0 < W i)
    (hlo : ∀ i, lo i ≤ hi i) (i : I) : 0 ≤ width m W lo hi i := by
  exact sub_nonneg.mpr (clamp_mono
    ((div_le_div_iff_of_pos_right (hW i)).2 (sub_le_sub_right (hlo i) (m i))))

theorem width_le (m W lo hi : I → ℝ) (hW : ∀ i, 0 < W i)
    (hlo : ∀ i, lo i ≤ hi i) (i : I) :
    width m W lo hi i ≤ (hi i - lo i) / W i := by
  calc
    width m W lo hi i ≤ (hi i - m i) / W i - (lo i - m i) / W i :=
      clamp_sub_le _ _ ((div_le_div_iff_of_pos_right (hW i)).2
        (sub_le_sub_right (hlo i) (m i)))
    _ = (hi i - lo i) / W i := by ring

/-- The finite normalized windows lie in the unit cube, cover the actual
image of `K`, and cost no more than the original relative widths. Empty
index types and windows disjoint from the unit interval are permitted. -/
theorem normalize_cover [Fintype I] (K : Set E) (f : I → E → ℝ)
    (e : E → I → ℝ) (m W lo hi : I → ℝ)
    (hW : ∀ i, 0 < W i)
    (he : ∀ p ∈ K, ∀ i, e p i = (f i p - m i) / W i)
    (hb : ∀ p ∈ K, ∀ i, 0 ≤ e p i ∧ e p i ≤ 1)
    (hlo : ∀ i, lo i ≤ hi i)
    (hcover : ∀ p ∈ K, ∃ i, lo i ≤ f i p ∧ f i p ≤ hi i) :
    (∀ i, 0 ≤ width m W lo hi i) ∧
    (∀ i, 0 ≤ lower m W lo i) ∧
    (∀ i, lower m W lo i + width m W lo hi i ≤ 1) ∧
    (∀ z ∈ e '' K, ∃ i, lower m W lo i ≤ z i ∧
      z i ≤ lower m W lo i + width m W lo hi i) ∧
    (∑ i, width m W lo hi i) ≤ ∑ i, (hi i - lo i) / W i := by
  refine ⟨width_nonneg m W lo hi hW hlo, fun i => clamp_nonneg _, ?_, ?_, ?_⟩
  · intro i
    rw [lower_add_width]
    exact clamp_le_one _
  · rintro z ⟨p, hp, rfl⟩
    obtain ⟨i, hil, hih⟩ := hcover p hp
    refine ⟨i, ?_⟩
    rw [lower_add_width]
    apply clamp_interval _ _ _ (hb p hp i)
    rw [he p hp i]
    exact ⟨(div_le_div_iff_of_pos_right (hW i)).2 (sub_le_sub_right hil (m i)),
      (div_le_div_iff_of_pos_right (hW i)).2 (sub_le_sub_right hih (m i))⟩
  · exact Finset.sum_le_sum (fun i _ => width_le m W lo hi hW hlo i)

end Plank.Convex.AffineSlabNormalization

/-- info: 'Plank.Convex.AffineSlabNormalization.clamp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.AffineSlabNormalization.clamp_sub_le

/-- info: 'Plank.Convex.AffineSlabNormalization.clamp_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.AffineSlabNormalization.clamp_interval

/-- info: 'Plank.Convex.AffineSlabNormalization.normalize_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.AffineSlabNormalization.normalize_cover
