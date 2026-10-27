/- Four contact segments and Cauchy--Schwarz prove the two-window bound.
Clipped transverse coordinates include zero outside margins and boundary windows. -/
module
public import Plank.Convex.AffineSlabNormalization
public import Plank.Convex.ConvexPairSegments
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Plank.Convex.TwoAffineWindows
open AffineSlabNormalization
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Cauchy--Schwarz for two product bounds, without square roots. -/
private theorem row_bound {a b c x y u v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h₁ : a * c ≤ u * x) (h₂ : b * c ≤ v * y) :
    c * (a + b) ^ 2 ≤ (u + v) * (a * x + b * y) := by
  have H := mul_le_mul h₁ h₂ (mul_nonneg hb hc)
    ((mul_nonneg ha hc).trans h₁)
  have hp : (a * b * c) ^ 2 ≤ (u * b * y) * (v * a * x) := by
    have h := mul_le_mul_of_nonneg_left H (mul_nonneg ha hb)
    nlinarith only [h]
  have hh := two_mul_le_add_of_sq_le_mul
    (mul_nonneg (mul_nonneg hu hb) hy) (mul_nonneg (mul_nonneg hv ha) hx) hp
  nlinarith only [hh, mul_le_mul_of_nonneg_left h₁ ha,
    mul_le_mul_of_nonneg_left h₂ hb]

/-- Add the two escape-side Cauchy bounds; the contact offsets cancel. -/
private theorem four_corners (a b c d w h s t u v : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hsh : s ≤ h) (ht : 0 ≤ t) (hth : t ≤ h)
    (hu : 0 ≤ u) (huw : u ≤ w) (hv : 0 ≤ v) (hvw : v ≤ w)
    (h₁ : a * c ≤ u * s) (h₂ : b * c ≤ (w - u) * t)
    (h₃ : a * d ≤ v * (h - s)) (h₄ : b * d ≤ (w - v) * (h - t))
    (hX : a + b = 1 - w) (hY : c + d = 1 - h) : 1 ≤ w + h := by
  by_contra! hdef
  have hab : 0 < a + b := by linarith only [hX, hdef, hs, hsh]
  have hL := row_bound ha hb hc hs ht hu (sub_nonneg.mpr huw) h₁ h₂
  have hU := row_bound ha hb hd (sub_nonneg.mpr hsh) (sub_nonneg.mpr hth)
    hv (sub_nonneg.mpr hvw) h₃ h₄
  have H : ((c + d) * (a + b)) * (a + b) ≤ (w * h) * (a + b) := by
    nlinarith only [hL, hU]
  have hAB := (mul_le_mul_iff_left₀ hab).mp H
  rw [hX, hY] at hAB
  nlinarith only [hAB, hdef]

private def clip (l h x : ℝ) : ℝ := max l (min h x)

private theorem clip_bounds (l h x : ℝ) (hlh : l ≤ h) : l ≤ clip l h x ∧ clip l h x ≤ h :=
  ⟨le_max_left _ _, max_le hlh (min_le_left _ _)⟩

private theorem clip_self (l h x : ℝ) (hx : l ≤ x ∧ x ≤ h) : clip l h x = x := by
  rw [clip, min_eq_right hx.2, max_eq_right hx.1]

/-- Signed excess beyond the selected endpoint of a window. -/
private def gap (upper : Bool) (l h : ℝ) : ℝ →ᵃ[ℝ] ℝ :=
  if upper then AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ h
  else AffineMap.const ℝ ℝ l - AffineMap.id ℝ ℝ

private theorem gap_nonpos (upper : Bool) (l h x : ℝ) (hx : l ≤ x ∧ x ≤ h) :
    gap upper l h x ≤ 0 := by
  cases upper <;> dsimp [gap] <;> linarith only [hx.1, hx.2]

/-- One corner inequality, for any independently chosen pair of sides.
Clipping the transverse coordinates only changes a zero-margin case. -/
private theorem corner_bound (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (l₁ h₁ l₂ h₂ : ℝ) (hle₁ : l₁ ≤ h₁) (hle₂ : l₂ ≤ h₂)
    (sx sy : Bool) (p q : E) (hp : p ∈ K) (hq : q ∈ K)
    (hXp : 0 ≤ gap sx l₁ h₁ (X p)) (hYq : 0 ≤ gap sy l₂ h₂ (Y q))
    (hcover : ∀ x ∈ K, (l₁ ≤ X x ∧ X x ≤ h₁) ∨ (l₂ ≤ Y x ∧ Y x ≤ h₂)) :
    gap sx l₁ h₁ (X p) * gap sy l₂ h₂ (Y q) ≤
      gap sx l₁ h₁ (clip l₁ h₁ (X q)) * gap sy l₂ h₂ (clip l₂ h₂ (Y p)) := by
  by_cases hpos : 0 < gap sx l₁ h₁ (X p) * gap sy l₂ h₂ (Y q)
  · have hgp := pos_of_mul_pos_left hpos hYq
    have hhq := pos_of_mul_pos_right hpos hXp
    have hpY := (hcover p hp).resolve_left (fun H => hgp.not_ge (gap_nonpos _ _ _ _ H))
    have hqX := (hcover q hq).resolve_right (fun H => hhq.not_ge (gap_nonpos _ _ _ _ H))
    rw [clip_self _ _ _ hqX, clip_self _ _ _ hpY]
    exact ConvexCellSeparation.cross_bound K hK ((gap sx l₁ h₁).comp X)
      ((gap sy l₂ h₂).comp Y) p q hp hq hgp hhq (by
        rintro ⟨x, hx, hg, hh⟩
        exact (hcover x hx).elim (fun hc => hg.not_ge (gap_nonpos _ _ _ _ hc))
          (fun hc => hh.not_ge (gap_nonpos _ _ _ _ hc)))
  · exact (le_of_not_gt hpos).trans (mul_nonneg_of_nonpos_of_nonpos
      (gap_nonpos _ _ _ _ (clip_bounds _ _ _ hle₁))
      (gap_nonpos _ _ _ _ (clip_bounds _ _ _ hle₂)))

/-- Four clipped contact coordinates handle both boundary and interior windows. -/
private theorem clipped_bound (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (l₁ h₁ l₂ h₂ : ℝ) (hle₁ : l₁ ≤ h₁) (hle₂ : l₂ ≤ h₂)
    (hl₁ : 0 ≤ l₁) (hh₁ : h₁ ≤ 1) (hl₂ : 0 ≤ l₂) (hh₂ : h₂ ≤ 1)
    (hX₀ : ∃ x ∈ K, X x = 0) (hX₁ : ∃ x ∈ K, X x = 1)
    (hY₀ : ∃ x ∈ K, Y x = 0) (hY₁ : ∃ x ∈ K, Y x = 1)
    (hcover : ∀ x ∈ K, (l₁ ≤ X x ∧ X x ≤ h₁) ∨ (l₂ ≤ Y x ∧ Y x ≤ h₂)) :
    1 ≤ (h₁ - l₁) + (h₂ - l₂) := by
  obtain ⟨L, hL, hXL⟩ := hX₀
  obtain ⟨R, hR, hXR⟩ := hX₁
  obtain ⟨B, hB, hYB⟩ := hY₀
  obtain ⟨T, hT, hYT⟩ := hY₁
  have corner (sx sy : Bool) := corner_bound K hK X Y l₁ h₁ l₂ h₂ hle₁ hle₂
    sx sy (if sx then R else L) (if sy then T else B)
    (by cases sx <;> assumption) (by cases sy <;> assumption)
    (by cases sx <;> dsimp [gap] <;> linarith only [hXL, hXR, hl₁, hh₁])
    (by cases sy <;> dsimp [gap] <;> linarith only [hYB, hYT, hl₂, hh₂]) hcover
  have hLL := corner false false
  have hRL := corner true false
  have hLU := corner false true
  have hRU := corner true true
  dsimp [gap] at hLL hRL hLU hRU
  simp only [hXL, hXR, hYB, hYT] at hLL hRL hLU hRU
  have hs := clip_bounds l₂ h₂ (Y L) hle₂
  have ht := clip_bounds l₂ h₂ (Y R) hle₂
  have hu := clip_bounds l₁ h₁ (X B) hle₁
  have hv := clip_bounds l₁ h₁ (X T) hle₁
  apply four_corners l₁ (1 - h₁) l₂ (1 - h₂) (h₁ - l₁) (h₂ - l₂)
    (clip l₂ h₂ (Y L) - l₂) (clip l₂ h₂ (Y R) - l₂)
    (clip l₁ h₁ (X B) - l₁) (clip l₁ h₁ (X T) - l₁)
    hl₁ (sub_nonneg.mpr hh₁) hl₂ (sub_nonneg.mpr hh₂)
    (sub_nonneg.mpr hs.1) (by linarith only [hs.2])
    (sub_nonneg.mpr ht.1) (by linarith only [ht.2])
    (sub_nonneg.mpr hu.1) (by linarith only [hu.2])
    (sub_nonneg.mpr hv.1) (by linarith only [hv.2])
    (by nlinarith only [hLL]) (by nlinarith only [hRL])
    (by nlinarith only [hLU]) (by nlinarith only [hRU]) (by ring) (by ring)

/-- Two closed affine windows covering a convex set have total width at least
one when both coordinates have attained range `[0,1]`. The windows need only
be ordered; the affine maps and contact points need not be distinct. -/
theorem width_bound (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ x ∈ K, (0 ≤ X x ∧ X x ≤ 1) ∧ (0 ≤ Y x ∧ Y x ≤ 1))
    (l₁ h₁ l₂ h₂ : ℝ) (hle₁ : l₁ ≤ h₁) (hle₂ : l₂ ≤ h₂)
    (hX₀ : ∃ x ∈ K, X x = 0) (hX₁ : ∃ x ∈ K, X x = 1)
    (hY₀ : ∃ x ∈ K, Y x = 0) (hY₁ : ∃ x ∈ K, Y x = 1)
    (hcover : ∀ x ∈ K, (l₁ ≤ X x ∧ X x ≤ h₁) ∨ (l₂ ≤ Y x ∧ Y x ≤ h₂)) :
    1 ≤ (h₁ - l₁) + (h₂ - l₂) := by
  have htrim : ∀ x ∈ K,
      (clamp l₁ ≤ X x ∧ X x ≤ clamp h₁) ∨
        (clamp l₂ ≤ Y x ∧ Y x ≤ clamp h₂) := by
    intro x hx
    rcases hcover x hx with h | h
    · exact Or.inl (clamp_interval _ _ _ (hbox x hx).1 h)
    · exact Or.inr (clamp_interval _ _ _ (hbox x hx).2 h)
  have hbound := clipped_bound K hK X Y
    (clamp l₁) (clamp h₁) (clamp l₂) (clamp h₂) (clamp_mono hle₁) (clamp_mono hle₂)
    (clamp_nonneg l₁) (clamp_le_one h₁) (clamp_nonneg l₂) (clamp_le_one h₂)
    hX₀ hX₁ hY₀ hY₁ htrim
  exact hbound.trans (add_le_add (clamp_sub_le _ _ hle₁) (clamp_sub_le _ _ hle₂))

end Plank.Convex.TwoAffineWindows

/-- info: 'Plank.Convex.TwoAffineWindows.width_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.TwoAffineWindows.width_bound
