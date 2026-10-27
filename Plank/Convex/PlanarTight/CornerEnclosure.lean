/- The endpoint triangular enclosures force a cube vertex on a
normalized body in a plane with positive coefficients. -/
module
public import Plank.Convex.PlanarTight.TwoPlankClassification
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.CornerEnclosure

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The four triangles obtained by cutting the unit square along a diagonal. -/
def Enclosed (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) : Prop :=
  (∀ z ∈ K, X z + Y z ≤ 1) ∨ (∀ z ∈ K, X z ≤ Y z) ∨
  (∀ z ∈ K, Y z ≤ X z) ∨ (∀ z ∈ K, 1 ≤ X z + Y z)

theorem swap {K : Set E} {X Y : E →ᵃ[ℝ] ℝ} (h : Enclosed K Y X) : Enclosed K X Y := by
  rcases h with h | h | h | h
  · exact Or.inl (by intro z hz; simpa only [add_comm] using h z hz)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (by intro z hz; simpa only [add_comm] using h z hz)))

theorem reflect {K : Set E} {X Y : E →ᵃ[ℝ] ℝ}
    (h : Enclosed K (TwoPlankClassification.reflect X) Y) : Enclosed K X Y := by
  rcases h with h | h | h | h
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    intro z hz
    have hs := h z hz
    change 1 - X z + Y z ≤ 1 at hs
    linarith only [hs]
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    intro z hz
    have hs := h z hz
    change 1 - X z ≤ Y z at hs
    linarith only [hs]
  · apply Or.inl
    intro z hz
    have hs := h z hz
    change Y z ≤ 1 - X z at hs
    linarith only [hs]
  · apply Or.inr ∘ Or.inl
    intro z hz
    have hs := h z hz
    change 1 ≤ 1 - X z + Y z at hs
    linarith only [hs]

abbrev Point := Fin 3 → ℝ

/-- The corner forced by a diagonal triangle has all three coordinates
at their directional extrema. Convexity is not required here. -/
theorem exists_cube_vertex (K : Set Point)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (hshape : Enclosed K (AffineMap.proj 1) (AffineMap.proj 2)) :
    ∃ z ∈ K, ∀ i, z i = 0 ∨ z i = 1 := by
  have atMax (V : Point) (hV : V ∈ K)
      (hmax : ∀ z ∈ K, b * z 1 + c * z 2 ≤ b * V 1 + c * V 2) : V 0 = 0 := by
    obtain ⟨W, hW, hW₀⟩ := hL 0
    have hp := hplane V hV
    have hq := hplane W hW
    rw [hW₀] at hq
    have hcomp := hmax W hW
    have hv := (hbox V hV 0).1
    nlinarith only [hp, hq, hcomp, hv, ha]
  have atMin (V : Point) (hV : V ∈ K)
      (hmin : ∀ z ∈ K, b * V 1 + c * V 2 ≤ b * z 1 + c * z 2) : V 0 = 1 := by
    obtain ⟨W, hW, hW₀⟩ := hU 0
    have hp := hplane V hV
    have hq := hplane W hW
    rw [hW₀] at hq
    have hcomp := hmin W hW
    have hv := (hbox V hV 0).2
    nlinarith only [hp, hq, hcomp, hv, ha]
  have cube (V : Point) (hV : V ∈ K) (h₀ : V 0 = 0 ∨ V 0 = 1)
      (h₁ : V 1 = 0 ∨ V 1 = 1) (h₂ : V 2 = 0 ∨ V 2 = 1) :
      ∃ z ∈ K, ∀ i, z i = 0 ∨ z i = 1 := by
    refine ⟨V, hV, ?_⟩
    intro i
    fin_cases i <;> assumption
  rcases hshape with hs | hs | hs | hs
  · obtain ⟨R, hR, hR₁⟩ := hU 1
    obtain ⟨U, hU, hU₂⟩ := hU 2
    have hR₂ : R 2 = 0 := by
      have h := hs R hR
      change R 1 + R 2 ≤ 1 at h
      have hz := (hbox R hR 2).1
      linarith only [h, hR₁, hz]
    have hU₁ : U 1 = 0 := by
      have h := hs U hU
      change U 1 + U 2 ≤ 1 at h
      have hz := (hbox U hU 1).1
      linarith only [h, hU₂, hz]
    by_cases hbc : c ≤ b
    · have hR₀ := atMax R hR (by
        intro z hz
        rw [hR₁, hR₂, mul_one, mul_zero, add_zero]
        have h₁ := mul_le_mul_of_nonneg_right hbc (hbox z hz 2).1
        have h₂ := mul_le_mul_of_nonneg_left (hs z hz) hb.le
        change b * (z 1 + z 2) ≤ b * 1 at h₂
        nlinarith only [h₁, h₂])
      exact cube R hR (Or.inl hR₀) (Or.inr hR₁) (Or.inl hR₂)
    · have hcb := le_of_not_ge hbc
      have hU₀ := atMax U hU (by
        intro z hz
        rw [hU₁, hU₂, mul_zero, mul_one, zero_add]
        have h₁ := mul_le_mul_of_nonneg_right hcb (hbox z hz 1).1
        have h₂ := mul_le_mul_of_nonneg_left (hs z hz) hc.le
        change c * (z 1 + z 2) ≤ c * 1 at h₂
        nlinarith only [h₁, h₂])
      exact cube U hU (Or.inl hU₀) (Or.inl hU₁) (Or.inr hU₂)
  · obtain ⟨R, hR, hR₁⟩ := hU 1
    have hR₂ : R 2 = 1 := by
      have h := hs R hR
      change R 1 ≤ R 2 at h
      exact le_antisymm (hbox R hR 2).2 (hR₁ ▸ h)
    have hR₀ := atMax R hR (by
      intro z hz
      rw [hR₁, hR₂]
      exact add_le_add (mul_le_mul_of_nonneg_left (hbox z hz 1).2 hb.le)
        (mul_le_mul_of_nonneg_left (hbox z hz 2).2 hc.le))
    exact cube R hR (Or.inl hR₀) (Or.inr hR₁) (Or.inr hR₂)
  · obtain ⟨R, hR, hR₂⟩ := hU 2
    have hR₁ : R 1 = 1 := by
      have h := hs R hR
      change R 2 ≤ R 1 at h
      exact le_antisymm (hbox R hR 1).2 (hR₂ ▸ h)
    have hR₀ := atMax R hR (by
      intro z hz
      rw [hR₁, hR₂]
      exact add_le_add (mul_le_mul_of_nonneg_left (hbox z hz 1).2 hb.le)
        (mul_le_mul_of_nonneg_left (hbox z hz 2).2 hc.le))
    exact cube R hR (Or.inl hR₀) (Or.inr hR₁) (Or.inr hR₂)
  · obtain ⟨R, hR, hR₁⟩ := hL 1
    obtain ⟨U, hU, hU₂⟩ := hL 2
    have hR₂ : R 2 = 1 := by
      have h := hs R hR
      change 1 ≤ R 1 + R 2 at h
      have hz := (hbox R hR 2).2
      linarith only [h, hR₁, hz]
    have hU₁ : U 1 = 1 := by
      have h := hs U hU
      change 1 ≤ U 1 + U 2 at h
      have hz := (hbox U hU 1).2
      linarith only [h, hU₂, hz]
    by_cases hbc : b ≤ c
    · have hU₀ := atMin U hU (by
        intro z hz
        rw [hU₁, hU₂, mul_one, mul_zero, add_zero]
        have h₁ := mul_le_mul_of_nonneg_right hbc (hbox z hz 2).1
        have h₂ := mul_le_mul_of_nonneg_left (hs z hz) hb.le
        change b * 1 ≤ b * (z 1 + z 2) at h₂
        nlinarith only [h₁, h₂])
      exact cube U hU (Or.inr hU₀) (Or.inr hU₁) (Or.inl hU₂)
    · have hcb := le_of_not_ge hbc
      have hR₀ := atMin R hR (by
        intro z hz
        rw [hR₁, hR₂, mul_zero, mul_one, zero_add]
        have h₁ := mul_le_mul_of_nonneg_right hcb (hbox z hz 1).1
        have h₂ := mul_le_mul_of_nonneg_left (hs z hz) hc.le
        change c * 1 ≤ c * (z 1 + z 2) at h₂
        nlinarith only [h₁, h₂])
      exact cube R hR (Or.inr hR₀) (Or.inl hR₁) (Or.inr hR₂)

/-- A cube vertex cannot be covered by strictly internal windows. -/
theorem no_cube_vertex_of_strict_cover (K : Set Point) (lo hi : Point)
    (hlo : ∀ i, 0 < lo i) (hhi : ∀ i, hi i < 1)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i) :
    ¬ ∃ z ∈ K, ∀ i, z i = 0 ∨ z i = 1 := by
  rintro ⟨z, hz, hcorner⟩
  obtain ⟨i, hil, hiu⟩ := hcover z hz
  rcases hcorner i with he | he
  · rw [he] at hil
    exact (not_le_of_gt (hlo i)) hil
  · rw [he] at hiu
    exact (not_le_of_gt (hhi i)) hiu

end Plank.Convex.PlanarTight.CornerEnclosure

/-- info: 'Plank.Convex.PlanarTight.CornerEnclosure.exists_cube_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CornerEnclosure.exists_cube_vertex

/-- info: 'Plank.Convex.PlanarTight.CornerEnclosure.no_cube_vertex_of_strict_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CornerEnclosure.no_cube_vertex_of_strict_cover
