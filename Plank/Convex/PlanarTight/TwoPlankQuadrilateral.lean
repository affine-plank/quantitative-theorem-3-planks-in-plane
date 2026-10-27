/- The explicit quadrilateral family of tight two-plank covers. -/
module
public import Plank.Convex.ConvexCellSeparation
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoPlankQuadrilateral

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- For `0<p,q<1`, the quadrilateral with vertices `(0,p)`, `(q,0)`,
`(1,p)`, `(q,1)`, expressed by its four supporting inequalities. -/
def InQuadrilateral (x y q p : ℝ) : Prop :=
  p * q ≤ p * x + q * y ∧
  p * (1 - q) ≤ p * (1 - x) + (1 - q) * y ∧
  (1 - p) * q ≤ (1 - p) * x + q * (1 - y) ∧
  (1 - p) * (1 - q) ≤ (1 - p) * (1 - x) + (1 - q) * (1 - y)

/-- The two explicitly parameterized windows associated to the quadrilateral. -/
def Covered (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (g q p : ℝ) : Prop :=
  ∀ z ∈ K, ((1 - g) * q ≤ X z ∧ X z ≤ (1 - g) * q + g) ∨
    (g * p ≤ Y z ∧ Y z ≤ g * p + (1 - g))

private theorem lower_corner_support (K : Set E) (hK : Convex ℝ K)
    (X Y : E →ᵃ[ℝ] ℝ) (L B : E) (hL : L ∈ K) (hB : B ∈ K)
    (q p t : ℝ) (hq : 0 < q) (hp : 0 < p) (ht : 0 < t) (ht₁ : t < 1)
    (hXL : X L = 0) (hYL : Y L = p) (hXB : X B = q) (hYB : Y B = 0)
    (hcap : ¬ ∃ z ∈ K, X z < t * q ∧ Y z < (1 - t) * p) :
    ∀ z ∈ K, p * q ≤ p * X z + q * Y z := by
  obtain ⟨s, _, hrow⟩ := ConvexCellSeparation.exists_lower_support K hK X Y
    (t * q) ((1 - t) * p) (mul_pos ht hq) (mul_pos (sub_pos.mpr ht₁) hp)
    ⟨L, hL, hXL⟩ ⟨B, hB, hYB⟩ hcap
  have hleft := hrow L hL
  have hbottom := hrow B hB
  rw [hXL, hYL, zero_add] at hleft
  rw [hXB, hYB, mul_zero, add_zero] at hbottom
  have hprod : s * p = q := by
    have h₀ : t * (q - s * p) ≤ 0 := by nlinarith only [hleft]
    have h₁ : (1 - t) * (s * p - q) ≤ 0 := by nlinarith only [hbottom]
    have h₀' := nonpos_of_mul_nonpos_right h₀ ht
    have h₁' := nonpos_of_mul_nonpos_right h₁ (sub_pos.mpr ht₁)
    linarith only [h₀', h₁']
  have hconst : t * q + s * ((1 - t) * p) = q := by
    calc
      _ = t * q + (1 - t) * (s * p) := by ring
      _ = q := by rw [hprod]; ring
  intro z hz
  have hzrow := hrow z hz
  rw [hconst] at hzrow
  calc
    p * q ≤ p * (X z + s * Y z) := mul_le_mul_of_nonneg_left hzrow hp.le
    _ = p * X z + (s * p) * Y z := by ring
    _ = p * X z + q * Y z := by rw [hprod]

private theorem cover_flipX (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (g q p : ℝ)
    (hc : Covered K X Y g q p) :
    Covered K (AffineMap.const ℝ E 1 - X) Y g (1 - q) p := by
  intro z hz
  rcases hc z hz with h | h
  · left
    change (1 - g) * (1 - q) ≤ 1 - X z ∧ 1 - X z ≤ (1 - g) * (1 - q) + g
    constructor <;> nlinarith only [h.1, h.2]
  · exact Or.inr h

private theorem cover_flipY (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (g q p : ℝ)
    (hc : Covered K X Y g q p) :
    Covered K X (AffineMap.const ℝ E 1 - Y) g q (1 - p) := by
  intro z hz
  rcases hc z hz with h | h
  · exact Or.inl h
  · right
    change g * (1 - p) ≤ 1 - Y z ∧ 1 - Y z ≤ g * (1 - p) + (1 - g)
    constructor <;> nlinarith only [h.1, h.2]

private theorem lower_of_covered (K : Set E) (hK : Convex ℝ K)
    (X Y : E →ᵃ[ℝ] ℝ) (L B : E) (hL : L ∈ K) (hB : B ∈ K)
    (g q p : ℝ) (hg : 0 < g) (hg₁ : g < 1) (hq : 0 < q) (hp : 0 < p)
    (hXL : X L = 0) (hYL : Y L = p) (hXB : X B = q) (hYB : Y B = 0)
    (hc : Covered K X Y g q p) :
    ∀ z ∈ K, p * q ≤ p * X z + q * Y z := by
  apply lower_corner_support K hK X Y L B hL hB q p (1 - g) hq hp
    (sub_pos.mpr hg₁) (by linarith only [hg]) hXL hYL hXB hYB
  rintro ⟨z, hz, hx, hy⟩
  rcases hc z hz with h | h
  · exact not_lt_of_ge h.1 hx
  · have hy' : Y z < g * p := by nlinarith only [hy]
    exact not_lt_of_ge h.1 hy'

/-- The four aligned contacts and their tight covering windows force the
whole body into the explicit quadrilateral. -/
theorem enclosure_of_contacts (K : Set E) (hK : Convex ℝ K)
    (X Y : E →ᵃ[ℝ] ℝ) (g q p : ℝ)
    (hg : 0 < g) (hg₁ : g < 1) (hq : 0 < q) (hq₁ : q < 1) (hp : 0 < p) (hp₁ : p < 1)
    (L R B T : E) (hL : L ∈ K) (hR : R ∈ K) (hB : B ∈ K) (hT : T ∈ K)
    (hXL : X L = 0) (hYL : Y L = p) (hXR : X R = 1) (hYR : Y R = p)
    (hXB : X B = q) (hYB : Y B = 0) (hXT : X T = q) (hYT : Y T = 1)
    (hc : Covered K X Y g q p) : ∀ z ∈ K, InQuadrilateral (X z) (Y z) q p := by
  let X' : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E 1 - X
  let Y' : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E 1 - Y
  have hx (z : E) : X' z = 1 - X z := rfl
  have hy (z : E) : Y' z = 1 - Y z := rfl
  have h₀ := lower_of_covered K hK X Y L B hL hB g q p hg hg₁ hq hp hXL hYL hXB hYB hc
  have h₁ := lower_of_covered K hK X' Y R B hR hB g (1 - q) p hg hg₁
    (sub_pos.mpr hq₁) hp (by rw [hx, hXR]; ring) hYR (by rw [hx, hXB]) hYB
    (cover_flipX K X Y g q p hc)
  have h₂ := lower_of_covered K hK X Y' L T hL hT g q (1 - p) hg hg₁
    hq (sub_pos.mpr hp₁) hXL (by rw [hy, hYL]) hXT (by rw [hy, hYT]; ring)
    (cover_flipY K X Y g q p hc)
  have h₃ := lower_of_covered K hK X' Y' R T hR hT g (1 - q) (1 - p) hg hg₁
    (sub_pos.mpr hq₁) (sub_pos.mpr hp₁) (by rw [hx, hXR]; ring) (by rw [hy, hYR])
    (by rw [hx, hXT]) (by rw [hy, hYT]; ring)
    (cover_flipY K X' Y g (1 - q) p (cover_flipX K X Y g q p hc))
  exact fun z hz => ⟨h₀ z hz, h₁ z hz, h₂ z hz, h₃ z hz⟩

private theorem corner_contradiction (x y q p t : ℝ) (hq : 0 < q) (hp : 0 < p)
    (hrow : p * q ≤ p * x + q * y) (hx : x < t * q) (hy : y < (1 - t) * p) : False := by
  have h₀ := mul_lt_mul_of_pos_left hx hp
  have h₁ := mul_lt_mul_of_pos_left hy hq
  nlinarith only [hrow, h₀, h₁]

/-- Every subset of the explicit quadrilateral is covered by its two
parameterized windows. The relative widths are `g` and `1-g` when the
coordinate ranges are normalized. -/
theorem covered_of_enclosure (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (g q p : ℝ)
    (hq : 0 < q) (hq₁ : q < 1) (hp : 0 < p) (hp₁ : p < 1)
    (hshape : ∀ z ∈ K, InQuadrilateral (X z) (Y z) q p) : Covered K X Y g q p := by
  intro z hz
  by_contra h
  have hx : X z < (1 - g) * q ∨ (1 - g) * q + g < X z := by
    by_cases hl : (1 - g) * q ≤ X z
    · exact Or.inr (lt_of_not_ge (fun hu => h (Or.inl ⟨hl, hu⟩)))
    · exact Or.inl (lt_of_not_ge hl)
  have hy : Y z < g * p ∨ g * p + (1 - g) < Y z := by
    by_cases hl : g * p ≤ Y z
    · exact Or.inr (lt_of_not_ge (fun hu => h (Or.inr ⟨hl, hu⟩)))
    · exact Or.inl (lt_of_not_ge hl)
  obtain ⟨h₀, h₁, h₂, h₃⟩ := hshape z hz
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact corner_contradiction _ _ q p (1 - g) hq hp h₀ hx (by nlinarith only [hy])
  · exact corner_contradiction _ _ q (1 - p) (1 - g) hq (sub_pos.mpr hp₁) h₂ hx
      (by nlinarith only [hy])
  · exact corner_contradiction _ _ (1 - q) p (1 - g) (sub_pos.mpr hq₁) hp h₁
      (by nlinarith only [hx]) (by nlinarith only [hy])
  · exact corner_contradiction _ _ (1 - q) (1 - p) (1 - g)
      (sub_pos.mpr hq₁) (sub_pos.mpr hp₁) h₃ (by nlinarith only [hx]) (by nlinarith only [hy])

end Plank.Convex.PlanarTight.TwoPlankQuadrilateral

/-- info: 'Plank.Convex.PlanarTight.TwoPlankQuadrilateral.enclosure_of_contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankQuadrilateral.enclosure_of_contacts

/-- info: 'Plank.Convex.PlanarTight.TwoPlankQuadrilateral.covered_of_enclosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankQuadrilateral.covered_of_enclosure
