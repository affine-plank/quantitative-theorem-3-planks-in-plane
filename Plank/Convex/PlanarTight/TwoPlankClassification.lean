/- Complete normalized classification of two positive planks, including every
boundary position of their windows. -/
module
public import Plank.Convex.AffineWindowOrientation
public import Plank.Convex.PlanarTight.TwoPlankBoundary
public import Plank.Convex.PlanarTight.TwoPlankInterior
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoPlankClassification

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Both affine coordinates have attained range `[0,1]` on the body. -/
structure Ranges (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) : Prop where
  box : ∀ z ∈ K, (0 ≤ X z ∧ X z ≤ 1) ∧ (0 ≤ Y z ∧ Y z ≤ 1)
  minX : ∃ z ∈ K, X z = 0
  maxX : ∃ z ∈ K, X z = 1
  minY : ∃ z ∈ K, Y z = 0
  maxY : ∃ z ∈ K, Y z = 1

theorem Ranges.swap {K : Set E} {X Y : E →ᵃ[ℝ] ℝ} (H : Ranges K X Y) :
    Ranges K Y X :=
  ⟨fun z hz => (H.box z hz).symm, H.minY, H.maxY, H.minX, H.maxX⟩

theorem Ranges.reflect {K : Set E} {X Y : E →ᵃ[ℝ] ℝ} (H : Ranges K X Y) :
    Ranges K (reflect X) Y := by
  refine ⟨?_, ?_, ?_, H.minY, H.maxY⟩
  · intro z hz
    obtain ⟨hx, hy⟩ := H.box z hz
    exact ⟨⟨sub_nonneg.mpr hx.2, by simpa using hx.1⟩, hy⟩
  · obtain ⟨z, hz, hx⟩ := H.maxX
    exact ⟨z, hz, by simp [hx]⟩
  · obtain ⟨z, hz, hx⟩ := H.minX
    exact ⟨z, hz, by simp [hx]⟩

/-- The property classified below. -/
def Tight (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ) : Prop :=
  (u - l) + (v - m) = 1 ∧
    ∀ z ∈ K, (l ≤ X z ∧ X z ≤ u) ∨ (m ≤ Y z ∧ Y z ≤ v)

theorem tight_swap (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ) :
    Tight K Y X m v l u ↔ Tight K X Y l u m v := by
  simp only [Tight, add_comm (v - m), or_comm]

theorem tight_reflect (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ) :
    Tight K (reflect X) Y (1 - u) (1 - l) m v ↔ Tight K X Y l u m v := by
  unfold Tight
  constructor
  · rintro ⟨hsum, hcover⟩
    refine ⟨by linarith only [hsum], ?_⟩
    intro z hz
    rcases hcover z hz with h | h
    · exact Or.inl (by simpa only [reflect_apply, sub_le_sub_iff_left] using h.symm)
    · exact Or.inr h
  · rintro ⟨hsum, hcover⟩
    refine ⟨by linarith only [hsum], ?_⟩
    intro z hz
    rcases hcover z hz with h | h
    · exact Or.inl (by simpa only [reflect_apply, sub_le_sub_iff_left] using h.symm)
    · exact Or.inr h

/-- The triangular enclosure family with the first window anchored at zero.
The endpoint apexes `c=0` and `c=1` are included. -/
def Anchored (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ) : Prop :=
  l = 0 ∧ 0 < u ∧ u < 1 ∧
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ m = u * c ∧ v = u * c + (1 - u) ∧
      ∀ z ∈ K, c * X z ≤ Y z ∧ Y z ≤ 1 - (1 - c) * X z

/-- The complete list: an internal quadrilateral, or a triangular enclosure
anchored at one of the four directional extrema. All entries specify
endpoint equations and body inequalities, without a covering predicate. -/
def Normal (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ) : Prop :=
  TwoPlankInterior.Normal K X Y l u m v ∨
  Anchored K X Y l u m v ∨
  Anchored K (reflect X) Y (1 - u) (1 - l) m v ∨
  Anchored K Y X m v l u ∨
  Anchored K (reflect Y) X (1 - v) (1 - m) l u

private theorem anchored_of_tight (K : Set E) (hK : Convex ℝ K)
    (X Y : E →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (l u m v : ℝ) (hl : l = 0) (hlu : l < u) (hmv : m < v)
    (hm : 0 ≤ m) (hv : v ≤ 1) (htight : Tight K X Y l u m v) :
    Anchored K X Y l u m v := by
  subst l
  have hu : u < 1 := by have hw := htight.1; linarith only [hw, hmv]
  refine ⟨rfl, hlu, hu, ?_⟩
  apply (TwoPlankBoundary.tight_iff K hK X Y H.box H.maxX H.minY H.maxY
    u m v hlu hu hm hv).mp
  simpa only [Tight, sub_zero] using htight

private theorem tight_of_anchored (K : Set E) (hK : Convex ℝ K)
    (X Y : E →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (l u m v : ℝ) (hm : 0 ≤ m) (hv : v ≤ 1)
    (hnormal : Anchored K X Y l u m v) : Tight K X Y l u m v := by
  obtain ⟨rfl, hu, hu₁, hshape⟩ := hnormal
  have htight := (TwoPlankBoundary.tight_iff K hK X Y H.box H.maxX H.minY H.maxY
    u m v hu hu₁ hm hv).mpr hshape
  simpa only [Tight, sub_zero] using htight

/-- Exhaustive equality classification for two positive normalized windows.
No compactness, finite-dimensionality, or independence of the coordinates
is required beyond convexity and the attained unit ranges. -/
theorem tight_iff (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (H : Ranges K X Y) (l u m v : ℝ)
    (hl : 0 ≤ l) (hu : u ≤ 1) (hm : 0 ≤ m) (hv : v ≤ 1)
    (hlu : l < u) (hmv : m < v) :
    Tight K X Y l u m v ↔ Normal K X Y l u m v := by
  constructor
  · intro htight
    by_cases hl₀ : l = 0
    · exact Or.inr (Or.inl (anchored_of_tight K hK X Y H l u m v hl₀ hlu hmv hm hv htight))
    by_cases hu₁ : u = 1
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      apply anchored_of_tight K hK (reflect X) Y H.reflect (1 - u) (1 - l) m v
        (by rw [hu₁]; ring) (by linarith only [hlu]) hmv hm hv
      exact (tight_reflect K X Y l u m v).mpr htight
    by_cases hm₀ : m = 0
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
      apply anchored_of_tight K hK Y X H.swap m v l u hm₀ hmv hlu hl hu
      exact (tight_swap K X Y l u m v).mpr htight
    by_cases hv₁ : v = 1
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
      apply anchored_of_tight K hK (reflect Y) X H.swap.reflect (1 - v) (1 - m) l u
        (by rw [hv₁]; ring) (by linarith only [hmv]) hlu hl hu
      exact (tight_reflect K Y X m v l u).mpr ((tight_swap K X Y l u m v).mpr htight)
    apply Or.inl
    exact (TwoPlankInterior.tight_iff K hK X Y H.box H.minX H.maxX H.minY H.maxY
      l u m v (lt_of_le_of_ne hl (Ne.symm hl₀)) (lt_of_le_of_ne hu hu₁)
      (lt_of_le_of_ne hm (Ne.symm hm₀)) (lt_of_le_of_ne hv hv₁) hlu hmv).mp htight
  · intro hnormal
    rcases hnormal with h | h | h | h | h
    · rcases h with ⟨g, q, p, _, _, hq, hq₁, hp, hp₁, hlform, huform, hmform, hvform, hshape⟩
      refine ⟨?_, ?_⟩
      · rw [hlform, huform, hmform, hvform]
        ring
      · intro z hz
        rw [hlform, huform, hmform, hvform]
        exact TwoPlankQuadrilateral.covered_of_enclosure K X Y g q p hq hq₁ hp hp₁ hshape z hz
    · exact tight_of_anchored K hK X Y H l u m v hm hv h
    · apply (tight_reflect K X Y l u m v).mp
      exact tight_of_anchored K hK (reflect X) Y H.reflect (1 - u) (1 - l) m v hm hv h
    · apply (tight_swap K X Y l u m v).mp
      exact tight_of_anchored K hK Y X H.swap m v l u hl hu h
    · apply (tight_swap K X Y l u m v).mp
      apply (tight_reflect K Y X m v l u).mp
      exact tight_of_anchored K hK (reflect Y) X H.swap.reflect (1 - v) (1 - m) l u hl hu h

end Plank.Convex.PlanarTight.TwoPlankClassification

/-- info: 'Plank.Convex.PlanarTight.TwoPlankClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankClassification.tight_iff
