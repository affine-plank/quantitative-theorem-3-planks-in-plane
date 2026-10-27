/- The upper-sum endpoint enclosure in an anchored contraction forces
an opposite pair of cube vertices, hence a common extremal segment. -/
module
public import Plank.Convex.PlanarTight.CornerPropagation
public import Plank.Convex.PlanarTight.AnchoredCorner
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.AnchoredUpperSum

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The last plank cannot start late on the segment between the two
opposite Y/Z corners. A hypothetical gap gives two strict cuts at an
interior point and would force Y below its attained maximum. -/
theorem zero_at_other_corner (K : Set E) (hK : Convex ℝ K) (X Y Z : E →ᵃ[ℝ] ℝ)
    (A B : E) (hA : A ∈ K) (hB : B ∈ K)
    (hXA : X A = 1) (hYA : Y A = 0) (hZA : Z A = 1)
    (hXB : 0 ≤ X B) (hYB : Y B = 1) (hZB : Z B = 0)
    (r g : ℝ) (hr : 0 < r) (hr₁ : r < 1) (hg : 0 < g)
    (hcover : ∀ z ∈ K, X z ≤ r ∨
      ((1 - r) * (1 - g) ≤ Y z ∧ Y z ≤ 1 - r) ∨
      (r + (1 - r) * g ≤ Z z ∧ Z z ≤ 1)) : X B = 0 := by
  by_contra hn
  have hXBpos := lt_of_le_of_ne hXB (Ne.symm hn)
  let Q := r • A + (1 - r) • B
  have hQ : Q ∈ K := hK hA hB hr.le (sub_pos.mpr hr₁).le (by ring)
  have hXQ : X Q = r + (1 - r) * X B := by
    rw [AnchoredCorner.map_contract, hXA, mul_one]
  have hYQ : Y Q = 1 - r := by rw [AnchoredCorner.map_contract, hYA, hYB]; ring
  have hZQ : Z Q = r := by rw [AnchoredCorner.map_contract, hZA, hZB]; ring
  let f : Fin 3 → E →ᵃ[ℝ] ℝ := ![
    X - AffineMap.const ℝ E r,
    Y - AffineMap.const ℝ E (1 - r),
    AffineMap.const ℝ E (r + (1 - r) * g) - Z]
  have hf := CornerPropagation.support K hK f Q hQ (by
      change 0 < X Q - r
      rw [hXQ]
      nlinarith only [mul_pos (sub_pos.mpr hr₁) hXBpos])
    (by change Y Q - (1 - r) = 0; rw [hYQ]; ring) (by
      change 0 < r + (1 - r) * g - Z Q
      rw [hZQ]
      nlinarith only [mul_pos (sub_pos.mpr hr₁) hg]) (by
      rintro ⟨z, hz, hcuts⟩
      have hX : r < X z := sub_pos.mp (hcuts 0)
      have hY : 1 - r < Y z := sub_pos.mp (hcuts 1)
      have hZ : Z z < r + (1 - r) * g := sub_pos.mp (hcuts 2)
      rcases hcover z hz with h | h | h
      · exact not_le_of_gt hX h
      · exact not_le_of_gt hY h.2
      · exact not_lt_of_ge h.1 hZ)
  have hb := hf B hB
  change Y B - (1 - r) ≤ 0 at hb
  rw [hYB] at hb
  linarith only [hb, hr]

abbrev Point := Fin 3 → ℝ

/-- The two actual Y/Z corners are opposite vertices of the full unit
cube in this endpoint normal form. -/
theorem opposite_vertices (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (T : Point) (hT : T ∈ K) (hT₀ : T 0 = 1)
    (r g : ℝ) (hr : 0 < r) (hr₁ : r < 1) (hg : 0 < g) (hg₁ : g < 1)
    (hshape : ∀ z ∈ K, 1 ≤ z 1 + z 2)
    (hcover : ∀ z ∈ K, z 0 ≤ r ∨
      (r * T 1 + (1 - r) * (1 - g) ≤ z 1 ∧ z 1 ≤ r * T 1 + (1 - r)) ∨
      (r * T 2 + (1 - r) * g ≤ z 2 ∧ z 2 ≤ r * T 2 + (1 - r))) :
    ∃ R ∈ K, ∃ U ∈ K, R 1 = 0 ∧ R 2 = 1 ∧ U 1 = 1 ∧ U 2 = 0 ∧
      ((R 0 = 1 ∧ U 0 = 0) ∨ (R 0 = 0 ∧ U 0 = 1)) := by
  obtain ⟨R, hR, hR₁⟩ := hL 1
  obtain ⟨U, hU, hU₂⟩ := hL 2
  have hR₂ : R 2 = 1 := by
    have hs := hshape R hR
    have hz := (hbox R hR 2).2
    linarith only [hs, hR₁, hz]
  have hU₁ : U 1 = 1 := by
    have hs := hshape U hU
    have hz := (hbox U hU 1).2
    linarith only [hs, hU₂, hz]
  have hpR := hplane R hR
  have hpU := hplane U hU
  have hpT := hplane T hT
  rw [hR₁, hR₂] at hpR
  rw [hU₁, hU₂] at hpU
  rw [hT₀] at hpT
  have hmax : R 0 = 1 ∨ U 0 = 1 := by
    by_cases hbc : b ≤ c
    · apply Or.inr
      have h₁ := mul_le_mul_of_nonneg_right hbc (hbox T hT 2).1
      have h₂ := mul_le_mul_of_nonneg_left (hshape T hT) hb.le
      have hz := (hbox U hU 0).2
      nlinarith only [hpU, hpT, h₁, h₂, hz, ha]
    · apply Or.inl
      have h₁ := mul_le_mul_of_nonneg_right (le_of_not_ge hbc) (hbox T hT 1).1
      have h₂ := mul_le_mul_of_nonneg_left (hshape T hT) hc.le
      have hz := (hbox R hR 0).2
      nlinarith only [hpR, hpT, h₁, h₂, hz, ha]
  refine ⟨R, hR, U, hU, hR₁, hR₂, hU₁, hU₂, ?_⟩
  rcases hmax with hR₀ | hU₀
  · have hT₂ : T 2 = 1 := by
      rcases hcover R hR with h | h | h
      · rw [hR₀] at h
        exact False.elim (not_le_of_gt hr₁ h)
      · rw [hR₁] at h
        have hnn := mul_nonneg hr.le (hbox T hT 1).1
        have hpos := mul_pos (sub_pos.mpr hr₁) (sub_pos.mpr hg₁)
        nlinarith only [h.1, hnn, hpos]
      · rw [hR₂] at h
        have hbound := (hbox T hT 2).2
        nlinarith only [h.2, hbound, hr]
    have hT₁ : T 1 = 0 := by
      rw [hR₀] at hpR
      rw [hT₂] at hpT
      nlinarith only [hpR, hpT, hb]
    have hU₀ := zero_at_other_corner K hK (AffineMap.proj 0) (AffineMap.proj 1)
      (AffineMap.proj 2) R U hR hU hR₀ hR₁ hR₂ (hbox U hU 0).1 hU₁ hU₂ r g hr hr₁ hg (by
        intro z hz
        have h := hcover z hz
        rw [hT₁, hT₂] at h
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (by
            change (1 - r) * (1 - g) ≤ z 1 ∧ z 1 ≤ 1 - r
            constructor <;> nlinarith only [h.1, h.2]))
        · exact Or.inr (Or.inr (by
            change r + (1 - r) * g ≤ z 2 ∧ z 2 ≤ 1
            constructor <;> nlinarith only [h.1, h.2])))
    exact Or.inl ⟨hR₀, hU₀⟩
  · have hT₁ : T 1 = 1 := by
      rcases hcover U hU with h | h | h
      · rw [hU₀] at h
        exact False.elim (not_le_of_gt hr₁ h)
      · rw [hU₁] at h
        have hbound := (hbox T hT 1).2
        nlinarith only [h.2, hbound, hr]
      · rw [hU₂] at h
        have hnn := mul_nonneg hr.le (hbox T hT 2).1
        have hpos := mul_pos (sub_pos.mpr hr₁) hg
        nlinarith only [h.1, hnn, hpos]
    have hT₂ : T 2 = 0 := by
      rw [hU₀] at hpU
      rw [hT₁] at hpT
      nlinarith only [hpU, hpT, hc]
    have hR₀ := zero_at_other_corner K hK (AffineMap.proj 0) (AffineMap.proj 2)
      (AffineMap.proj 1) U R hU hR hU₀ hU₂ hU₁ (hbox R hR 0).1 hR₂ hR₁ r (1 - g)
      hr hr₁ (sub_pos.mpr hg₁) (by
        intro z hz
        have h := hcover z hz
        rw [hT₁, hT₂] at h
        rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (by
            change r + (1 - r) * (1 - g) ≤ z 1 ∧ z 1 ≤ 1
            constructor <;> nlinarith only [h.1, h.2]))
        · exact Or.inr (Or.inl (by
            change (1 - r) * (1 - (1 - g)) ≤ z 2 ∧ z 2 ≤ 1 - r
            constructor <;> nlinarith only [h.1, h.2])))
    exact Or.inr ⟨hR₀, hU₀⟩

end Plank.Convex.PlanarTight.AnchoredUpperSum

/-- info: 'Plank.Convex.PlanarTight.AnchoredUpperSum.opposite_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredUpperSum.opposite_vertices
