/- The lower-sum endpoint case retains the exact apex and zero-base
triangle geometry needed by the explicit window family. -/
module
public import Plank.Convex.PlanarTight.PerspectiveCap
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredLowerSumCap

abbrev Point := Fin 3 → ℝ

/-- An explicit endpoint case of the anchored contraction. In the
opposite-vertex alternative, the displayed points give a common extremal
segment for all three coordinates after orientation. -/
theorem cap_or_opposite_vertices (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (T : Point) (hT : T ∈ K) (hT₀ : T 0 = 1)
    (r g : ℝ) (hr : 0 < r) (hr₁ : r < 1) (hg : 0 < g) (hg₁ : g < 1)
    (hshape : ∀ z ∈ K, z 1 + z 2 ≤ 1)
    (hcover : ∀ z ∈ K, z 0 ≤ r ∨
      (r * T 1 ≤ z 1 ∧ z 1 ≤ r * T 1 + (1 - r) * g) ∨
      (r * T 2 ≤ z 2 ∧ z 2 ≤ r * T 2 + (1 - r) * (1 - g))) :
    AnchoredCapBody.Has K (AffineMap.proj 0) T ∨
      ∃ R ∈ K, ∃ U ∈ K, R 1 = 1 ∧ R 2 = 0 ∧ U 1 = 0 ∧ U 2 = 1 ∧
        ((R 0 = 0 ∧ U 0 = 1) ∨ (R 0 = 1 ∧ U 0 = 0)) := by
  obtain ⟨R, hR, hR₁⟩ := hU 1
  obtain ⟨U, hU, hU₂⟩ := hU 2
  have hR₂ : R 2 = 0 := by
    have hs := hshape R hR
    have hz := (hbox R hR 2).1
    linarith only [hs, hR₁, hz]
  have hU₁ : U 1 = 0 := by
    have hs := hshape U hU
    have hz := (hbox U hU 1).1
    linarith only [hs, hU₂, hz]
  have hpR := hplane R hR
  have hpU := hplane U hU
  have hpT := hplane T hT
  rw [hR₁, hR₂] at hpR
  rw [hU₁, hU₂] at hpU
  rw [hT₀] at hpT
  have hzero : R 0 = 0 ∨ U 0 = 0 := by
    obtain ⟨W, hW, hW₀⟩ := hL 0
    have hpW := hplane W hW
    rw [hW₀] at hpW
    by_cases hbc : c ≤ b
    · apply Or.inl
      have h₁ := mul_le_mul_of_nonneg_right hbc (hbox W hW 2).1
      have h₂ := mul_le_mul_of_nonneg_left (hshape W hW) hb.le
      have hz := (hbox R hR 0).1
      nlinarith only [hpR, hpW, h₁, h₂, hz, ha]
    · apply Or.inr
      have h₁ := mul_le_mul_of_nonneg_right (le_of_not_ge hbc) (hbox W hW 1).1
      have h₂ := mul_le_mul_of_nonneg_left (hshape W hW) hc.le
      have hz := (hbox U hU 0).1
      nlinarith only [hpU, hpW, h₁, h₂, hz, ha]
  by_cases hboth : R 0 = 0 ∧ U 0 = 0
  · have hY : ∀ z ∈ K, T 1 * z 0 ≤ z 1 := by
      apply PerspectiveTriangle.lower_support K hK (AffineMap.proj 0) (AffineMap.proj 1)
        (AffineMap.proj 2) T U hT hU (T 1) r (r * T 2 + (1 - r) * (1 - g))
        hT₀ hboth.2 rfl hU₁ hr hr₁
      · change r * T 2 + (1 - r) * (1 - g) < r * T 2 + (1 - r) * U 2
        rw [hU₂]
        nlinarith only [mul_pos (sub_pos.mpr hr₁) hg]
      · rintro ⟨z, hz, hX, hY, hZ⟩
        rcases hcover z hz with h | h | h
        · exact not_le_of_gt hX h
        · exact not_lt_of_ge h.1 hY
        · exact not_le_of_gt hZ h.2
    have hZ : ∀ z ∈ K, T 2 * z 0 ≤ z 2 := by
      apply PerspectiveTriangle.lower_support K hK (AffineMap.proj 0) (AffineMap.proj 2)
        (AffineMap.proj 1) T R hT hR (T 2) r (r * T 1 + (1 - r) * g)
        hT₀ hboth.1 rfl hR₂ hr hr₁
      · change r * T 1 + (1 - r) * g < r * T 1 + (1 - r) * R 1
        rw [hR₁]
        nlinarith only [mul_pos (sub_pos.mpr hr₁) (sub_pos.mpr hg₁)]
      · rintro ⟨z, hz, hX, hZ, hY⟩
        rcases hcover z hz with h | h | h
        · exact not_le_of_gt hX h
        · exact not_le_of_gt hY h.2
        · exact not_lt_of_ge h.1 hZ
    exact Or.inl (PerspectiveCap.of_supports K hK (fun z hz => (hbox z hz 0).1)
      a b c d hb hplane T R U hT hR hU hT₀ hboth.1 hR₁ hR₂ hboth.2 hU₁ hU₂ hY hZ)
  · have hC : 0 < (AffineMap.proj 0 : Point →ᵃ[ℝ] ℝ) (g • R + (1 - g) • U) := by
      change 0 < g * R 0 + (1 - g) * U 0
      by_cases hR₀ : R 0 = 0
      · have hU₀ : 0 < U 0 := lt_of_le_of_ne (hbox U hU 0).1
          (fun he => hboth ⟨hR₀, he.symm⟩)
        exact add_pos_of_nonneg_of_pos (mul_nonneg hg.le (hbox R hR 0).1)
          (mul_pos (sub_pos.mpr hg₁) hU₀)
      · have hRpos := lt_of_le_of_ne (hbox R hR 0).1 (Ne.symm hR₀)
        exact add_pos_of_pos_of_nonneg (mul_pos hg hRpos)
          (mul_nonneg (sub_pos.mpr hg₁).le (hbox U hU 0).1)
    have hline := AnchoredCorner.on_edge K hK (AffineMap.proj 0)
      (TwoPlankClassification.reflect (AffineMap.proj 1))
      (TwoPlankClassification.reflect (AffineMap.proj 2))
      T R U hT hR hU hT₀ 1 1 g r zero_lt_one hg hg₁ hr hr₁
      (by change 1 - R 1 = 0; rw [hR₁]; ring)
      (by change 1 - R 2 = 1; rw [hR₂]; ring)
      (by change 1 - U 1 = 1; rw [hU₁]; ring)
      (by change 1 - U 2 = 0; rw [hU₂]; ring) hC (by
        rintro ⟨z, hz, hX, hY, hZ⟩
        change 1 - z 1 < r * (1 - T 1) + (1 - r) * ((1 - g) * 1) at hY
        change 1 - z 2 < r * (1 - T 2) + (1 - r) * (g * 1) at hZ
        rcases hcover z hz with h | h | h
        · exact not_le_of_gt hX h
        · nlinarith only [hY, h.2]
        · nlinarith only [hZ, h.2])
    change 1 * (1 - T 1) + 1 * (1 - T 2) = 1 * 1 at hline
    have hsum : T 1 + T 2 = 1 := by linarith only [hline]
    refine Or.inr ⟨R, hR, U, hU, hR₁, hR₂, hU₁, hU₂, ?_⟩
    rcases hzero with hR₀ | hU₀
    · apply Or.inl
      refine ⟨hR₀, ?_⟩
      rw [hR₀] at hpR
      have he : a * (1 - U 0 * T 2) = 0 := by
        linear_combination hpT - T 1 * hpR - T 2 * hpU - d * hsum
      have he' := (mul_eq_zero.mp he).resolve_left ha.ne'
      have hle := mul_le_mul_of_nonneg_left (hbox T hT 2).2 (hbox U hU 0).1
      have hu := (hbox U hU 0).2
      nlinarith only [he', hle, hu]
    · apply Or.inr
      refine ⟨?_, hU₀⟩
      rw [hU₀] at hpU
      have he : a * (1 - R 0 * T 1) = 0 := by
        linear_combination hpT - T 1 * hpR - T 2 * hpU - d * hsum
      have he' := (mul_eq_zero.mp he).resolve_left ha.ne'
      have hle := mul_le_mul_of_nonneg_left (hbox T hT 1).2 (hbox R hR 0).1
      have hu := (hbox R hR 0).2
      nlinarith only [he', hle, hu]

end Plank.Convex.PlanarTight.AnchoredLowerSumCap

/-- info: 'Plank.Convex.PlanarTight.AnchoredLowerSumCap.cap_or_opposite_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredLowerSumCap.cap_or_opposite_vertices
