/- Honest extended-volume QAPC on every convex set, derived from its compact-body case. -/
module

public import QuantitativePlanks.Extensions.Width
public import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ExtendedQuantitative

open Set MeasureTheory Metric Filter FiniteDimensionalCapWindowScaling
  FiniteDimensionalInductionBoundary
open scoped ENNReal Topology BigOperators

theorem ofReal_deficit {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (max 0 (1-r)) = 1 - ENNReal.ofReal r := by
  rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, zero_max,
    ENNReal.ofReal_sub 1 hr, ENNReal.ofReal_one]

/-- The bounded-set estimate rewritten in genuine extended nonnegative arithmetic.
No positive-volume or positive-directional-span hypothesis is required. -/
theorem bounded {d m : ℕ} (hbound : SharpBound d m)
    {K : Set (Point d)} (hb : Bornology.IsBounded K) (hc : Convex ℝ K)
    (f : Fin m → Point d →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin m → ℝ) (horder : ∀ i, lo i ≤ hi i) :
    (1 - ExtendedWidth.budget K f lo hi)^(d+1) * volume K ≤
      volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) := by
  by_cases hz : volume K = 0
  · simp only [hz, mul_zero]
    exact bot_le
  have hW (i) : 0 < Body.width K (f i) :=
    ConvexSetQuantitative.width_pos_of_measure_pos hb (pos_iff_ne_zero.mpr hz) (f i) (hf i)
  have hR : 0 ≤ ∑ i, (hi i-lo i)/Body.width K (f i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (sub_nonneg.mpr (horder i)) (hW i).le
  have hreal := BoundedConvexBounds.sharpBound_of_isBounded hbound hb hc f lo hi horder hW
  have he := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul (pow_nonneg (le_max_left 0 _) _),
    ENNReal.ofReal_pow (le_max_left 0 _) (d+1), ofReal_deficit hR,
    ENNReal.ofReal_toReal hb.measure_lt_top.ne,
    ENNReal.ofReal_toReal (hb.subset sdiff_subset).measure_lt_top.ne] at he
  rwa [ExtendedWidth.budget_eq_of_isBounded hb f lo hi horder hW]

/-- Any compact-body QAPC implies its honest extended-volume version on all
convex sets. Infinite directional spans contribute zero relative width. -/
theorem sharpBound_ordered {d m : ℕ} (hbound : SharpBound d m)
    {K : Set (Point d)} (hc : Convex ℝ K)
    (f : Fin m → Point d →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin m → ℝ) (horder : ∀ i, lo i ≤ hi i) :
    (1 - ExtendedWidth.budget K f lo hi)^(d+1) * volume K ≤
      volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) := by
  let C : ℕ → Set (Point d) := fun n => K ∩ closedBall 0 (n : ℝ)
  have hC : Monotone C := by
    intro i j hij
    change K ∩ closedBall (0 : Point d) (i : ℝ) ⊆ K ∩ closedBall 0 (j : ℝ)
    intro x hx
    exact ⟨hx.1, mem_closedBall.mpr ((mem_closedBall.mp hx.2).trans (Nat.cast_le.mpr hij))⟩
  have hCK (n) : C n ⊆ K := inter_subset_left
  have hunion : (⋃ n, C n) = K := iUnion_inter_closedBall_nat K 0
  have hb (n) : Bornology.IsBounded (C n) :=
    (isBounded_closedBall (x := (0 : Point d)) (r := (n : ℝ))).subset inter_subset_right
  have hcC (n) : Convex ℝ (C n) := hc.inter (convex_closedBall 0 (n : ℝ))
  have hbudget := ExtendedWidth.tendsto_budget_iUnion C hC f lo hi
  rw [hunion] at hbudget
  have hcoeff : Tendsto (fun n => (1 - ExtendedWidth.budget (C n) f lo hi)^(d+1))
      atTop (𝓝 ((1 - ExtendedWidth.budget K f lo hi)^(d+1))) :=
    ENNReal.Tendsto.pow (((ENNReal.continuous_sub_left (a := 1) (by norm_num)).tendsto _).comp hbudget)
  have hmeasure : Tendsto (fun n => volume (C n)) atTop (𝓝 (volume K)) := by
    simpa only [Function.comp_def, hunion] using tendsto_measure_iUnion_atTop (μ := volume) hC
  by_cases hzero : (1 - ExtendedWidth.budget K f lo hi)^(d+1) = 0
  · simp only [hzero, zero_mul]
    exact bot_le
  have hfinite : (1 - ExtendedWidth.budget K f lo hi)^(d+1) ≠ ∞ :=
    ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      (by simpa using pow_le_pow_left' (tsub_le_self :
        1 - ExtendedWidth.budget K f lo hi ≤ 1) (d+1))
  apply le_of_tendsto (ENNReal.Tendsto.mul hcoeff (Or.inl hzero) hmeasure (Or.inr hfinite))
  apply Filter.Eventually.of_forall
  intro n
  exact (bounded hbound (hb n) (hcC n) f hf lo hi horder).trans
    (measure_mono (sdiff_subset_sdiff_left (hCK n)))

theorem budget_normalize_hi {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}
    (K : Set E) (f : Fin m → E →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ) :
    ExtendedWidth.budget K f lo (fun i => max (lo i) (hi i)) =
      ExtendedWidth.budget K f lo hi := by
  unfold ExtendedWidth.budget
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change ENNReal.ofReal (max (lo i) (hi i) - lo i) = ENNReal.ofReal (hi i - lo i)
  by_cases h : lo i ≤ hi i
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_not_ge h), sub_self, ENNReal.ofReal_zero,
      ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]

/-- Genuine extended-volume QAPC for every convex set. No compactness,
boundedness, finiteness, nonemptiness, positive span, measurability or endpoint
order hypothesis is needed. Reversed windows are empty and have zero cost. -/
theorem sharpBound {d m : ℕ} (hbound : SharpBound d m)
    {K : Set (Point d)} (hc : Convex ℝ K)
    (f : Fin m → Point d →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin m → ℝ) :
    (1 - ExtendedWidth.budget K f lo hi)^(d+1) * volume K ≤
      volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) := by
  have h := sharpBound_ordered hbound hc f hf lo (fun i => max (lo i) (hi i))
    (fun i => le_max_left _ _)
  rw [budget_normalize_hi] at h
  apply h.trans
  apply measure_mono
  apply sdiff_subset_sdiff_right
  apply iUnion_mono
  intro i x hx
  exact ⟨hx.1, hx.2.trans (le_max_right _ _)⟩

/-- Three-plank planar QAPC with extended spans and extended volume, for all
convex sets including nonclosed, unbounded and zero-area sets. -/
theorem planar_three {K : Set (Point 1)} (hc : Convex ℝ K)
    (f : Fin 3 → Point 1 →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin 3 → ℝ) :
    (1 - ExtendedWidth.budget K f lo hi)^2 * volume K ≤
      volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) :=
  sharpBound CoveringFirstQuantitative.sharpBound_three hc f hf lo hi

/-- Two-plank QAPC in every positive dimension with no restrictions on the
convex set beyond convexity itself. -/
theorem two_planks {d : ℕ} {K : Set (Point d)} (hc : Convex ℝ K)
    (f : Fin 2 → Point d →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin 2 → ℝ) :
    (1 - ExtendedWidth.budget K f lo hi)^(d+1) * volume K ≤
      volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) :=
  sharpBound FiniteDimensionalTwoPlank.sharpBound_two hc f hf lo hi

/-- A genuinely nonvacuous infinite-volume consequence: a strict budget below
one leaves infinite uncovered volume. -/
theorem infinite_uncovered_of_budget_lt_one {d m : ℕ} (hbound : SharpBound d m)
    {K : Set (Point d)} (hc : Convex ℝ K) (hV : volume K = ∞)
    (f : Fin m → Point d →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : Fin m → ℝ) (hR : ExtendedWidth.budget K f lo hi < 1) :
    volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) = ∞ := by
  have h := sharpBound hbound hc f hf lo hi
  rw [hV, ENNReal.mul_top (pow_ne_zero _ (ne_of_gt (tsub_pos_of_lt hR)))] at h
  exact top_le_iff.mp h

end Plank.ExtendedQuantitative

#print axioms Plank.ExtendedQuantitative.sharpBound
#print axioms Plank.ExtendedQuantitative.planar_three
#print axioms Plank.ExtendedQuantitative.two_planks
#print axioms Plank.ExtendedQuantitative.infinite_uncovered_of_budget_lt_one
