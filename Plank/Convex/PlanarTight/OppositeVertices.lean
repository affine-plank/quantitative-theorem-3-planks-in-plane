/- Opposite vertices of the coordinate cube give a common extremal
segment after reflecting the coordinates which decrease along it. -/
module
public import Plank.Convex.PlanarTight.CornerEnclosure
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.OppositeVertices

abbrev Point := Fin 3 → ℝ

def Has (K : Set Point) : Prop :=
  ∃ A ∈ K, ∃ B ∈ K, (∀ i, A i = 0 ∨ A i = 1) ∧ ∀ i, B i = 1 - A i

theorem cross (K : Set Point) (R U : Point) (hR : R ∈ K) (hU : U ∈ K)
    (hR₁ : R 1 = 1) (hR₂ : R 2 = 0) (hU₁ : U 1 = 0) (hU₂ : U 2 = 1)
    (hends : (R 0 = 0 ∧ U 0 = 1) ∨ (R 0 = 1 ∧ U 0 = 0)) : Has K := by
  refine ⟨R, hR, U, hU, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hends.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    · exact Or.inr hR₁
    · exact Or.inl hR₂
  · intro i
    fin_cases i <;> dsimp
    · rcases hends with h | h <;> rw [h.1, h.2] <;> ring
    · rw [hR₁, hU₁]; ring
    · rw [hR₂, hU₂]; ring

/-- Either coordinate order forces both opposite coordinate corners;
the positive plane relation supplies the remaining extreme coordinates. -/
theorem of_order (K : Set Point)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (horder : (∀ z ∈ K, z 1 ≤ z 2) ∨ (∀ z ∈ K, z 2 ≤ z 1)) : Has K := by
  have hcontacts : (∃ A ∈ K, A 1 = 0 ∧ A 2 = 0) ∧
      (∃ B ∈ K, B 1 = 1 ∧ B 2 = 1) := by
    rcases horder with h | h
    · obtain ⟨A, hA, hA₂⟩ := hL 2
      obtain ⟨B, hB, hB₁⟩ := hU 1
      refine ⟨⟨A, hA, ?_, hA₂⟩, ⟨B, hB, hB₁, ?_⟩⟩
      · have hle := h A hA
        have hn := (hbox A hA 1).1
        linarith only [hle, hn, hA₂]
      · have hle := h B hB
        have hn := (hbox B hB 2).2
        linarith only [hle, hn, hB₁]
    · obtain ⟨A, hA, hA₁⟩ := hL 1
      obtain ⟨B, hB, hB₂⟩ := hU 2
      refine ⟨⟨A, hA, hA₁, ?_⟩, ⟨B, hB, ?_, hB₂⟩⟩
      · have hle := h A hA
        have hn := (hbox A hA 2).1
        linarith only [hle, hn, hA₁]
      · have hle := h B hB
        have hn := (hbox B hB 1).2
        linarith only [hle, hn, hB₂]
  obtain ⟨⟨A, hA, hA₁, hA₂⟩, ⟨B, hB, hB₁, hB₂⟩⟩ := hcontacts
  have hA₀ : A 0 = 1 := by
    obtain ⟨M, hM, hM₀⟩ := hU 0
    have hp := hplane A hA
    have hq := hplane M hM
    rw [hA₁, hA₂] at hp
    rw [hM₀] at hq
    have h₁ := mul_nonneg hb.le (hbox M hM 1).1
    have h₂ := mul_nonneg hc.le (hbox M hM 2).1
    have hz := (hbox A hA 0).2
    nlinarith only [hp, hq, h₁, h₂, hz, ha]
  have hB₀ : B 0 = 0 := by
    obtain ⟨M, hM, hM₀⟩ := hL 0
    have hp := hplane B hB
    have hq := hplane M hM
    rw [hB₁, hB₂] at hp
    rw [hM₀] at hq
    have h₁ := mul_le_mul_of_nonneg_left (hbox M hM 1).2 hb.le
    have h₂ := mul_le_mul_of_nonneg_left (hbox M hM 2).2 hc.le
    have hz := (hbox B hB 0).1
    nlinarith only [hp, hq, h₁, h₂, hz, ha]
  refine ⟨A, hA, B, hB, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Or.inr hA₀
    · exact Or.inl hA₁
    · exact Or.inl hA₂
  · intro i
    fin_cases i <;> simp [hA₀, hA₁, hA₂, hB₀, hB₁, hB₂]

end Plank.Convex.PlanarTight.OppositeVertices

/-- info: 'Plank.Convex.PlanarTight.OppositeVertices.of_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.OppositeVertices.of_order
