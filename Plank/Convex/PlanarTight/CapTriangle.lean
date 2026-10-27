/- Equality in a one-cap width bound gives an explicit triangular enclosure. -/
module
public import Plank.Convex.ConvexCellSeparation
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.CapTriangle

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A lower cap of height `a` attaining the minimum possible horizontal
width `a` forces the entire body into a triangle with apex `(c,0)` and
upper edge from `(0,1)` to `(1,1)`. The window endpoints are explicit.
Endpoint apexes `c = 0` and `c = 1` are included. -/
theorem lower (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ p ∈ K, (0 ≤ X p ∧ X p ≤ 1) ∧ (0 ≤ Y p ∧ Y p ≤ 1))
    (hL : ∃ p ∈ K, X p = 0) (hR : ∃ p ∈ K, X p = 1)
    (hB : ∃ p ∈ K, Y p = 0)
    (a l h : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hl : 0 ≤ l) (hh : h ≤ 1)
    (hwidth : h - l = a)
    (hcap : ∀ p ∈ K, Y p < a → l ≤ X p ∧ X p ≤ h) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ l = (1 - a) * c ∧ h = (1 - a) * c + a ∧
      (∀ p ∈ K, c * (1 - Y p) ≤ X p ∧ X p ≤ c + (1 - c) * Y p) := by
  have hleft : ∃ t : ℝ, 0 ≤ t ∧ ∀ p ∈ K, l + t * a ≤ X p + t * Y p := by
    by_cases hl₀ : l = 0
    · refine ⟨0, le_rfl, ?_⟩
      intro p hp
      simpa only [hl₀, zero_mul, zero_add, add_zero] using (hbox p hp).1.1
    · obtain ⟨t, ht, hrow⟩ := ConvexCellSeparation.exists_lower_support K hK
        X Y l a (lt_of_le_of_ne hl (Ne.symm hl₀)) ha
        hL hB (by
          rintro ⟨p, hp, hpl, hpa⟩
          exact (not_lt_of_ge (hcap p hp hpa).1) hpl)
      exact ⟨t, ht.le, hrow⟩
  have hright : ∃ s : ℝ, 0 ≤ s ∧ ∀ p ∈ K, X p - s * Y p ≤ h - s * a := by
    by_cases hh₁ : h = 1
    · refine ⟨0, le_rfl, ?_⟩
      intro p hp
      simpa only [hh₁, zero_mul, sub_zero] using (hbox p hp).1.2
    · obtain ⟨s, hs, hrow⟩ := ConvexCellSeparation.exists_mixed_support K hK
        X Y h a (lt_of_le_of_ne hh hh₁) ha
        hR hB (by
          rintro ⟨p, hp, hph, hpa⟩
          exact (not_lt_of_ge (hcap p hp hpa).2) hph)
      exact ⟨s, hs.le, hrow⟩
  obtain ⟨t, ht, hleft⟩ := hleft
  obtain ⟨s, hs, hright⟩ := hright
  obtain ⟨L, hL, hL₀⟩ := hL
  obtain ⟨R, hR, hR₁⟩ := hR
  obtain ⟨B, hB, hB₀⟩ := hB
  have hlower : l ≤ t * (1 - a) := by
    have hrow := hleft L hL
    rw [hL₀, zero_add] at hrow
    have htop := mul_le_mul_of_nonneg_left (hbox L hL).2.2 ht
    nlinarith only [hrow, htop]
  have hupper : 1 - h ≤ s * (1 - a) := by
    have hrow := hright R hR
    rw [hR₁] at hrow
    have htop := mul_le_mul_of_nonneg_left (hbox R hR).2.2 hs
    nlinarith only [hrow, htop]
  have hbottom : l + (t + s) * a ≤ h := by
    have hrow₀ := hleft B hB
    have hrow₁ := hright B hB
    rw [hB₀, mul_zero, add_zero] at hrow₀
    rw [hB₀, mul_zero, sub_zero] at hrow₁
    nlinarith only [hrow₀, hrow₁]
  have hsum : t + s = 1 := by
    have hle : t + s ≤ 1 := by nlinarith only [hbottom, hwidth, ha]
    have hge : 1 ≤ t + s := by nlinarith only [hlower, hupper, hwidth, ha₁]
    exact le_antisymm hle hge
  have hsval : s = 1 - t := by linarith only [hsum]
  rw [hsval] at hupper hright hs
  have hloweq : l = (1 - a) * t := by nlinarith only [hlower, hupper, hwidth]
  have hupeq : h = (1 - a) * t + a := by linarith only [hloweq, hwidth]
  refine ⟨t, ht, by linarith only [hs], hloweq, hupeq, ?_⟩
  intro p hp
  have hrow₀ := hleft p hp
  have hrow₁ := hright p hp
  constructor
  · nlinarith only [hrow₀, hloweq]
  · nlinarith only [hrow₁, hupeq]

/-- The reflected upper-cap enclosure, including both endpoint apexes. -/
theorem upper (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ p ∈ K, (0 ≤ X p ∧ X p ≤ 1) ∧ (0 ≤ Y p ∧ Y p ≤ 1))
    (hL : ∃ p ∈ K, X p = 0) (hR : ∃ p ∈ K, X p = 1)
    (hT : ∃ p ∈ K, Y p = 1)
    (b l h : ℝ) (hb : 0 < b) (hb₁ : b < 1) (hl : 0 ≤ l) (hh : h ≤ 1)
    (hwidth : h - l = 1 - b)
    (hcap : ∀ p ∈ K, b < Y p → l ≤ X p ∧ X p ≤ h) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ l = b * c ∧ h = b * c + (1 - b) ∧
      (∀ p ∈ K, c * Y p ≤ X p ∧ X p ≤ 1 - (1 - c) * Y p) := by
  let Y' : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E 1 - Y
  have hy (p : E) : Y' p = 1 - Y p := rfl
  obtain ⟨c, hc₀, hc₁, hlc, hhc, hshape⟩ := lower K hK X Y'
    (fun p hp => ⟨(hbox p hp).1, by rw [hy]; constructor <;> linarith [(hbox p hp).2]⟩)
    hL hR (by obtain ⟨p, hp, hy₁⟩ := hT; exact ⟨p, hp, by rw [hy, hy₁]; ring⟩)
    (1 - b) l h (by linarith only [hb₁]) (by linarith only [hb]) hl hh hwidth
    (by intro p hp hpa; apply hcap p hp; rw [hy] at hpa; linarith only [hpa])
  refine ⟨c, hc₀, hc₁, ?_, ?_, ?_⟩
  · nlinarith only [hlc]
  · nlinarith only [hhc]
  · intro p hp
    have hs := hshape p hp
    rw [hy] at hs
    constructor <;> nlinarith only [hs.1, hs.2]

/-- A complete normal form for a lower cap that uses exactly its height in
horizontal width. The right side specifies endpoints and a triangular body
enclosure, without a coverage or width hypothesis. -/
theorem lower_iff (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ p ∈ K, (0 ≤ X p ∧ X p ≤ 1) ∧ (0 ≤ Y p ∧ Y p ≤ 1))
    (hL : ∃ p ∈ K, X p = 0) (hR : ∃ p ∈ K, X p = 1)
    (hB : ∃ p ∈ K, Y p = 0)
    (a l h : ℝ) (ha : 0 < a) (ha₁ : a < 1) (hl : 0 ≤ l) (hh : h ≤ 1) :
    (h - l = a ∧ ∀ p ∈ K, Y p < a → l ≤ X p ∧ X p ≤ h) ↔
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ l = (1 - a) * c ∧ h = (1 - a) * c + a ∧
        (∀ p ∈ K, c * (1 - Y p) ≤ X p ∧ X p ≤ c + (1 - c) * Y p) := by
  constructor
  · rintro ⟨hw, hc⟩
    exact lower K hK X Y hbox hL hR hB a l h ha ha₁ hl hh hw hc
  · rintro ⟨c, hc₀, hc₁, hlc, hhc, hshape⟩
    refine ⟨by linarith only [hlc, hhc], ?_⟩
    intro p hp hpa
    obtain ⟨hleft, hright⟩ := hshape p hp
    constructor
    · nlinarith only [hleft, hlc, mul_nonneg hc₀ (sub_nonneg.mpr hpa.le)]
    · nlinarith only [hright, hhc,
        mul_nonneg (sub_nonneg.mpr hc₁) (sub_nonneg.mpr hpa.le)]

/-- Two opposite caps with their minimum possible widths, assigned to
separated horizontal windows, force the two affine coordinates to coincide
on the entire set. This retains the possible segment degeneracy. -/
theorem opposite_caps_collapse (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ p ∈ K, (0 ≤ X p ∧ X p ≤ 1) ∧ (0 ≤ Y p ∧ Y p ≤ 1))
    (hL : ∃ p ∈ K, X p = 0) (hR : ∃ p ∈ K, X p = 1)
    (hB : ∃ p ∈ K, Y p = 0) (hT : ∃ p ∈ K, Y p = 1)
    (a b l₀ u₀ l₁ u₁ : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hl₀ : 0 ≤ l₀) (hu₀ : u₀ ≤ 1) (hl₁ : 0 ≤ l₁) (hu₁ : u₁ ≤ 1)
    (hw₀ : u₀ - l₀ = a) (hw₁ : u₁ - l₁ = 1 - b) (hgap : u₀ < l₁)
    (hlo : ∀ p ∈ K, Y p < a → l₀ ≤ X p ∧ X p ≤ u₀)
    (hhi : ∀ p ∈ K, b < Y p → l₁ ≤ X p ∧ X p ≤ u₁) :
    ∀ p ∈ K, X p = Y p := by
  obtain ⟨c, hc₀, hc₁, hlc, huc, hshape₀⟩ :=
    lower K hK X Y hbox hL hR hB a l₀ u₀ ha (hab.trans hb) hl₀ hu₀ hw₀ hlo
  obtain ⟨d, hd₀, hd₁, hld, hud, hshape₁⟩ :=
    upper K hK X Y hbox hL hR hT b l₁ u₁ (ha.trans hab) hb hl₁ hu₁ hw₁ hhi
  have hdpos : 0 < d := by
    by_contra! hdn
    have hd : d = 0 := le_antisymm hdn hd₀
    rw [hd, mul_zero] at hld
    linarith only [hld, hw₀, hl₀, ha, hgap]
  obtain ⟨L, hL, hXL⟩ := hL
  have hYL : Y L = 0 := by
    have hlower := (hshape₁ L hL).1
    rw [hXL] at hlower
    nlinarith only [hlower, hdpos, (hbox L hL).2.1]
  have hc : c = 0 := by
    have hlower := (hshape₀ L hL).1
    rw [hXL, hYL] at hlower
    nlinarith only [hlower, hc₀]
  obtain ⟨R, hR, hXR⟩ := hR
  have hYR : Y R = 1 := by
    have hupper := (hshape₀ R hR).2
    rw [hc, hXR] at hupper
    nlinarith only [hupper, (hbox R hR).2.2]
  have hd : d = 1 := by
    have hupper := (hshape₁ R hR).2
    rw [hXR, hYR] at hupper
    nlinarith only [hupper, hd₁]
  intro p hp
  have hupper := (hshape₀ p hp).2
  have hlower := (hshape₁ p hp).1
  rw [hc] at hupper
  rw [hd] at hlower
  nlinarith only [hupper, hlower]

end Plank.Convex.PlanarTight.CapTriangle

/-- info: 'Plank.Convex.PlanarTight.CapTriangle.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CapTriangle.lower

/-- info: 'Plank.Convex.PlanarTight.CapTriangle.upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CapTriangle.upper

/-- info: 'Plank.Convex.PlanarTight.CapTriangle.lower_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CapTriangle.lower_iff

/-- info: 'Plank.Convex.PlanarTight.CapTriangle.opposite_caps_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CapTriangle.opposite_caps_collapse
