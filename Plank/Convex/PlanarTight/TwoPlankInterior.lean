/- Complete interior two-plank equality normal form in unit affine coordinates. -/
module
public import Plank.Convex.PlanarTight.TwoPlankContacts
public import Plank.Convex.PlanarTight.TwoPlankQuadrilateral
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoPlankInterior
open TwoPlankQuadrilateral

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An explicit quadrilateral enclosure and endpoint equations. The three
parameters are the first width and the two coordinates of the crossing
directional diagonals. -/
def Normal (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l u m v : ℝ) : Prop :=
  ∃ g q p : ℝ, 0 < g ∧ g < 1 ∧ 0 < q ∧ q < 1 ∧ 0 < p ∧ p < 1 ∧
    l = (1 - g) * q ∧ u = (1 - g) * q + g ∧
    m = g * p ∧ v = g * p + (1 - g) ∧
    ∀ z ∈ K, InQuadrilateral (X z) (Y z) q p

/-- All tight covers by two positive, strictly internal windows have the
explicit quadrilateral normal form, and every such form is tight. No
coverage or tightness condition occurs inside `Normal`. -/
theorem tight_iff (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ z ∈ K, (0 ≤ X z ∧ X z ≤ 1) ∧ (0 ≤ Y z ∧ Y z ≤ 1))
    (hX₀ : ∃ z ∈ K, X z = 0) (hX₁ : ∃ z ∈ K, X z = 1)
    (hY₀ : ∃ z ∈ K, Y z = 0) (hY₁ : ∃ z ∈ K, Y z = 1)
    (l u m v : ℝ) (hl : 0 < l) (hu : u < 1) (hm : 0 < m) (hv : v < 1)
    (hlu : l < u) (hmv : m < v) :
    ((u - l) + (v - m) = 1 ∧
      ∀ z ∈ K, (l ≤ X z ∧ X z ≤ u) ∨ (m ≤ Y z ∧ Y z ≤ v)) ↔
    Normal K X Y l u m v := by
  constructor
  · rintro ⟨hsum, hcover⟩
    let C : Plank.TwoPlankBody.Coords E :=
      { T := K, X := X, Y := Y
        seg := fun P hP Q hQ t ht₀ ht₁ =>
          ⟨P + t • (Q - P), hK.add_smul_sub_mem hP hQ ⟨ht₀, ht₁⟩,
            Plank.Body.map_add_smul_sub X P Q t, Plank.Body.map_add_smul_sub Y P Q t⟩
        range := hbox
        l1 := l, h1 := u, l2 := m, h2 := v
        le1 := hlu.le, le2 := hmv.le, cov := hcover
        pL := hX₀, pR := hX₁, qD := hY₀, qU := hY₁ }
    obtain ⟨L, hL, hXL⟩ := hX₀
    obtain ⟨R, hR, hXR⟩ := hX₁
    obtain ⟨B, hB, hYB⟩ := hY₀
    obtain ⟨T, hT, hYT⟩ := hY₁
    have hc : Y L = Y R ∧ X B = X T ∧ (u - l) * Y L = m ∧ (v - m) * X B = l :=
      TwoPlankContacts.realisers C hl hu hm hv hmv hsum L R B T hL hR hB hT hXL hXR hYB hYT
    let g := u - l
    let q := X B
    let p := Y L
    have hYL : m ≤ p ∧ p ≤ v := by
      rcases hcover L hL with h | h
      · exact False.elim (by rw [hXL] at h; linarith only [h.1, hl])
      · exact h
    have hXB : l ≤ q ∧ q ≤ u := by
      rcases hcover B hB with h | h
      · exact h
      · exact False.elim (by rw [hYB] at h; linarith only [h.1, hm])
    have hg : 0 < g := sub_pos.mpr hlu
    have hg₁ : g < 1 := by dsimp [g]; linarith only [hsum, hmv]
    have hq : 0 < q := hl.trans_le hXB.1
    have hq₁ : q < 1 := hXB.2.trans_lt hu
    have hp : 0 < p := hm.trans_le hYL.1
    have hp₁ : p < 1 := hYL.2.trans_lt hv
    have hwidth : v - m = 1 - g := by dsimp [g]; linarith only [hsum]
    have hlform : l = (1 - g) * q := by
      have he := hc.2.2.2
      rw [hwidth] at he
      exact he.symm
    have huform : u = (1 - g) * q + g := by dsimp [g] at *; linarith only [hlform]
    have hmform : m = g * p := hc.2.2.1.symm
    have hvform : v = g * p + (1 - g) := by linarith only [hmform, hwidth]
    refine ⟨g, q, p, hg, hg₁, hq, hq₁, hp, hp₁, hlform, huform, hmform, hvform, ?_⟩
    apply enclosure_of_contacts K hK X Y g q p hg hg₁ hq hq₁ hp hp₁
      L R B T hL hR hB hT hXL rfl hXR hc.1.symm rfl hYB hc.2.1.symm hYT
    intro z hz
    simpa only [hlform, huform, hmform, hvform] using hcover z hz
  · rintro ⟨g, q, p, _, _, hq, hq₁, hp, hp₁, hlform, huform, hmform, hvform, hshape⟩
    refine ⟨?_, ?_⟩
    · rw [hlform, huform, hmform, hvform]
      ring
    · intro z hz
      rw [hlform, huform, hmform, hvform]
      exact covered_of_enclosure K X Y g q p hq hq₁ hp hp₁ hshape z hz

end Plank.Convex.PlanarTight.TwoPlankInterior

/-- info: 'Plank.Convex.PlanarTight.TwoPlankInterior.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankInterior.tight_iff
