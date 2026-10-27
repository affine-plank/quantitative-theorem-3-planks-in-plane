/- Complete two-plank equality, including untrimmed and zero-width windows. -/
module
public import Plank.Convex.PlanarTight.TwoPlankClassification
public import Plank.Convex.PlanarTight.NoWaste
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoPlankComplete
open TwoPlankClassification AffineSlabNormalization

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Neither interval loses length when a tight two-plank cover is clipped. -/
theorem clipped_widths (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (H : Ranges K X Y) (l u m v : ℝ) (hlu : l ≤ u) (hmv : m ≤ v)
    (ht : Tight K X Y l u m v) :
    clamp u - clamp l = u - l ∧ clamp v - clamp m = v - m := by
  have hc : ∀ p ∈ K, (clamp l ≤ X p ∧ X p ≤ clamp u) ∨
      (clamp m ≤ Y p ∧ Y p ≤ clamp v) := by
    intro p hp
    rcases ht.2 p hp with h | h
    · exact Or.inl (clamp_interval l u (X p) (H.box p hp).1 h)
    · exact Or.inr (clamp_interval m v (Y p) (H.box p hp).2 h)
  have hb := TwoAffineWindows.width_bound K hK X Y H.box
    (clamp l) (clamp u) (clamp m) (clamp v) (clamp_mono hlu) (clamp_mono hmv)
    H.minX H.maxX H.minY H.maxY hc
  have hX := clamp_sub_le l u hlu
  have hY := clamp_sub_le m v hmv
  have hs := ht.1
  constructor <;> linarith only [hb, hX, hY, hs]

/-- Two positive normal windows, or a full unit-range window accompanied
by an arbitrary zero-width window. There are no clipping assumptions. -/
def Normal (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ) : Prop :=
  (l < u ∧ m < v ∧ TwoPlankClassification.Normal K X Y l u m v) ∨
    (l = u ∧ m = 0 ∧ v = 1) ∨ (m = v ∧ l = 0 ∧ u = 1)

/-- Exhaustive two-plank equality for arbitrary ordered real endpoints.
The zero-width plank may be any affine level, including outside the body. -/
theorem tight_iff (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (H : Ranges K X Y) (l u m v : ℝ) (hlu : l ≤ u) (hmv : m ≤ v) :
    Tight K X Y l u m v ↔ Normal K X Y l u m v := by
  constructor
  · intro ht
    obtain ⟨heX, heY⟩ := clipped_widths K hK X Y H l u m v hlu hmv ht
    have hs := ht.1
    by_cases hX : l < u
    · obtain ⟨hl, hu⟩ := endpoints_of_clamp_width_eq l u hX heX
      by_cases hY : m < v
      · obtain ⟨hm, hv⟩ := endpoints_of_clamp_width_eq m v hY heY
        exact Or.inl ⟨hX, hY, (TwoPlankClassification.tight_iff K hK X Y H l u m v
          hl hu hm hv hX hY).mp ht⟩
      · have hz : m = v := le_antisymm hmv (le_of_not_gt hY)
        exact Or.inr (Or.inr ⟨hz, by linarith only [hs, hz, hl, hu],
          by linarith only [hs, hz, hl, hu]⟩)
    · have hz : l = u := le_antisymm hlu (le_of_not_gt hX)
      have hY : m < v := by linarith only [hs, hz]
      obtain ⟨hm, hv⟩ := endpoints_of_clamp_width_eq m v hY heY
      exact Or.inr (Or.inl ⟨hz, by linarith only [hs, hz, hm, hv],
        by linarith only [hs, hz, hm, hv]⟩)
  · rintro (⟨hX, hY, hn⟩ | ⟨hz, hm, hv⟩ | ⟨hz, hl, hu⟩)
    · have hb : 0 ≤ l ∧ u ≤ 1 ∧ 0 ≤ m ∧ v ≤ 1 := by
        rcases hn with hn | hn | hn | hn | hn
        · obtain ⟨g, q, p, hg, hg1, hq, hq1, hp, hp1, hl, hu, hm, hv, _⟩ := hn
          constructor
          · rw [hl]; positivity
          constructor
          · rw [hu]; nlinarith only [hg, hg1, hq1]
          constructor
          · rw [hm]; positivity
          · rw [hv]; nlinarith only [hg, hp1]
        · obtain ⟨hl, hu0, hu1, c, hc, hc1, hm, hv, _⟩ := hn
          exact ⟨by rw [hl], hu1.le, by rw [hm]; positivity,
            by rw [hv]; nlinarith only [hu0, hc1]⟩
        · obtain ⟨hu, hl0, hl1, c, hc, hc1, hm, hv, _⟩ := hn
          exact ⟨by linarith only [hl1], by linarith only [hu],
            by rw [hm]; positivity,
            by rw [hv]; nlinarith only [hl0, hc1]⟩
        · obtain ⟨hm, hv0, hv1, c, hc, hc1, hl, hu, _⟩ := hn
          exact ⟨by rw [hl]; positivity, by rw [hu]; nlinarith only [hv0, hc1],
            by rw [hm], hv1.le⟩
        · obtain ⟨hv, hm0, hm1, c, hc, hc1, hl, hu, _⟩ := hn
          exact ⟨by rw [hl]; positivity, by rw [hu]; nlinarith only [hm0, hc1],
            by linarith only [hm1], by linarith only [hv]⟩
      exact (TwoPlankClassification.tight_iff K hK X Y H l u m v
        hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hX hY).mpr hn
    · refine ⟨by rw [hz, hm, hv]; ring, ?_⟩
      intro p hp
      exact Or.inr (by simpa only [hm, hv] using (H.box p hp).2)
    · refine ⟨by rw [hz, hl, hu]; ring, ?_⟩
      intro p hp
      exact Or.inl (by simpa only [hl, hu] using (H.box p hp).1)

end Plank.Convex.PlanarTight.TwoPlankComplete

/-- info: 'Plank.Convex.PlanarTight.TwoPlankComplete.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankComplete.tight_iff
