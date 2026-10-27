/- The upper corner of a tight two-window cover, including boundary cases. -/
module
public import Plank.Convex.PlanarTight.TwoPlankClassification
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Plank.Convex.TwoWindowUpperCorner
open Plank.TwoPlankBody PlanarTight

/-- The upper corner is a convex combination of two aligned directional realizers. -/
theorem interior_corner {E : Type*} (C : Coords E)
    (hl : 0 < C.l1) (hu : C.h1 < 1) (hm : 0 < C.l2) (hv : C.h2 < 1)
    (hw₁ : C.l1 < C.h1) (hw₂ : C.l2 < C.h2)
    (hsum : (C.h1 - C.l1) + (C.h2 - C.l2) = 1) :
    ∃ z ∈ C.T, C.X z = C.h1 ∧ C.Y z = C.h2 := by
  obtain ⟨L, hL, hXL⟩ := C.pL
  obtain ⟨R, hR, hXR⟩ := C.pR
  obtain ⟨B, hB, hYB⟩ := C.qD
  obtain ⟨T, hT, hYT⟩ := C.qU
  obtain ⟨hLR, hBT, hp, hq⟩ := TwoPlankContacts.realisers C hl hu hm hv hw₂ hsum
    L R B T hL hR hB hT hXL hXR hYB hYT
  have ht : 0 ≤ C.h2 - C.l2 := sub_nonneg.mpr C.le2
  have ht₁ : C.h2 - C.l2 ≤ 1 := by linarith only [hsum, hw₁]
  obtain ⟨z, hz, hx, hy⟩ := C.seg R hR T hT (C.h2 - C.l2) ht ht₁
  refine ⟨z, hz, ?_, ?_⟩
  · rw [hXR, ← hBT] at hx
    nlinarith only [hx, hq, hsum]
  · rw [hYT, ← hLR] at hy
    have he : C.h1 - C.l1 = 1 - (C.h2 - C.l2) := by linarith only [hsum]
    rw [he] at hp
    nlinarith only [hy, hp]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The unit diagonal and its two attained endpoints. -/
def Diagonal (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) : Prop :=
  (∀ z ∈ K, 1 ≤ X z + Y z) ∧
    (∃ z ∈ K, X z = 0 ∧ Y z = 1) ∧ (∃ z ∈ K, X z = 1 ∧ Y z = 0)

theorem anchored_corner_or_diagonal (K : Set E) (hK : Convex ℝ K)
    (X Y : E →ᵃ[ℝ] ℝ) (H : TwoPlankClassification.Ranges K X Y)
    (l m v : ℝ) (hl : 0 < l) (hl₁ : l < 1) (hm : 0 < m) (hv : v ≤ 1)
    (hsum : (1 - l) + (v - m) = 1)
    (hcover : ∀ z ∈ K, (l ≤ X z ∧ X z ≤ 1) ∨ (m ≤ Y z ∧ Y z ≤ v)) :
    (∃ z ∈ K, X z = 1 ∧ Y z = v) ∨ (v = 1 ∧ Diagonal K X Y) := by
  let X' : E →ᵃ[ℝ] ℝ := TwoPlankClassification.reflect X
  have hx (z : E) : X' z = 1 - X z := rfl
  have hg : 0 < 1 - l := sub_pos.mpr hl₁
  have hg₁ : 1 - l < 1 := by linarith only [hl]
  obtain ⟨c, hc, hc₁, hmform, hvform, hshape⟩ :=
    (TwoPlankBoundary.tight_iff K hK X' Y H.reflect.box H.reflect.maxX H.minY H.maxY
      (1 - l) m v hg hg₁ hm.le hv).mp ⟨hsum, by
        intro z hz
        rcases hcover z hz with h | h
        · exact Or.inl (by rw [hx]; constructor <;> linarith only [h.1, h.2])
        · exact Or.inr h⟩
  have hcpos : 0 < c := by nlinarith only [hm, hmform, hg, hc]
  by_cases hcstrict : c < 1
  · obtain ⟨B, hB, hYB⟩ := H.minY
    obtain ⟨T, hT, hYT⟩ := H.maxY
    have hXB : X B = 1 := by
      have h := (hshape B hB).1
      rw [hx, hYB] at h
      have hh := (H.box B hB).1.2
      nlinarith only [h, hh, hcpos]
    have hXT : X T = 1 := by
      have h := (hshape T hT).2
      rw [hx, hYT] at h
      have hh := (H.box T hT).1.2
      nlinarith only [h, hh, hcstrict]
    have hv₀ : 0 ≤ v := by linarith only [hm, hsum, hl]
    refine Or.inl ⟨B + v • (T - B), hK.add_smul_sub_mem hB hT ⟨hv₀, hv⟩, ?_, ?_⟩
    · rw [Plank.Body.map_add_smul_sub, hXB, hXT]
      ring
    · rw [Plank.Body.map_add_smul_sub, hYB, hYT]
      ring
  · have hc1 : c = 1 := le_antisymm hc₁ (le_of_not_gt hcstrict)
    have hv1 : v = 1 := by rw [hc1] at hvform; linarith only [hvform]
    have hd : ∀ z ∈ K, 1 ≤ X z + Y z := by
      intro z hz
      have h := (hshape z hz).1
      rw [hx, hc1, one_mul] at h
      linarith only [h]
    obtain ⟨L, hL, hXL⟩ := H.minX
    obtain ⟨B, hB, hYB⟩ := H.minY
    have hYL : Y L = 1 := by
      have h := hd L hL
      rw [hXL, zero_add] at h
      exact le_antisymm (H.box L hL).2.2 h
    have hXB : X B = 1 := by
      have h := hd B hB
      rw [hYB, add_zero] at h
      exact le_antisymm (H.box B hB).1.2 h
    exact Or.inr ⟨hv1, hd, ⟨L, hL, hXL, hYL⟩, ⟨B, hB, hXB, hYB⟩⟩

/-- The upper corner is present, except possibly when both windows end at one;
that exception has the explicit diagonal enclosure. -/
theorem upper_corner_or_diagonal (K : Set E) (hK : Convex ℝ K)
    (X Y : E →ᵃ[ℝ] ℝ) (H : TwoPlankClassification.Ranges K X Y)
    (l u m v : ℝ) (hl : 0 < l) (hu : u ≤ 1) (hm : 0 < m) (hv : v ≤ 1)
    (hlu : l < u) (hmv : m < v) (hsum : (u - l) + (v - m) = 1)
    (hcover : ∀ z ∈ K, (l ≤ X z ∧ X z ≤ u) ∨ (m ≤ Y z ∧ Y z ≤ v)) :
    (∃ z ∈ K, X z = u ∧ Y z = v) ∨ (u = 1 ∧ v = 1 ∧ Diagonal K X Y) := by
  by_cases hu1 : u = 1
  · subst u
    rcases anchored_corner_or_diagonal K hK X Y H l m v hl hlu hm hv hsum hcover with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩
  by_cases hv1 : v = 1
  · subst v
    have hsum' : (1 - m) + (u - l) = 1 := by linarith only [hsum]
    rcases anchored_corner_or_diagonal K hK Y X H.swap m l u hm hmv hl hu hsum'
      (fun z hz => (hcover z hz).symm) with h | h
    · obtain ⟨z, hz, hy, hx⟩ := h
      exact Or.inl ⟨z, hz, hx, hy⟩
    · exact False.elim (hu1 h.1)
  let C : Coords E :=
    { T := K, X := X, Y := Y
      seg := fun P hP Q hQ t ht₀ ht₁ =>
        ⟨P + t • (Q - P), hK.add_smul_sub_mem hP hQ ⟨ht₀, ht₁⟩,
          Plank.Body.map_add_smul_sub X P Q t, Plank.Body.map_add_smul_sub Y P Q t⟩
      range := H.box, l1 := l, h1 := u, l2 := m, h2 := v
      le1 := hlu.le, le2 := hmv.le, cov := hcover
      pL := H.minX, pR := H.maxX, qD := H.minY, qU := H.maxY }
  exact Or.inl (interior_corner C hl (lt_of_le_of_ne hu hu1) hm
    (lt_of_le_of_ne hv hv1) hlu hmv hsum)

end Plank.Convex.TwoWindowUpperCorner

/-- info: 'Plank.Convex.TwoWindowUpperCorner.upper_corner_or_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.TwoWindowUpperCorner.upper_corner_or_diagonal
