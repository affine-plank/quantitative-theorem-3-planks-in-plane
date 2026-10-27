/- Equality in the two-plank row bound aligns the four directional contacts. -/
module
public import Plank.Proofs.TwoPlankBodyCS
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoPlankAlgebra

/-- A quantitative square remainder for the two-plank row inequality. -/
theorem row_square_slack (a b c x y α β : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h₁ : a * c ≤ α * x) (h₂ : b * c ≤ β * y) :
    c * a * b * (x - y) ^ 2 ≤
      ((α + β) * (a * x + b * y) - c * (a + b) ^ 2) * x * y := by
  have hsum : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hslack₁ := mul_nonneg (mul_nonneg (sub_nonneg.mpr h₁) hy) hsum
  have hslack₂ := mul_nonneg (mul_nonneg (sub_nonneg.mpr h₂) hx) hsum
  nlinarith only [hslack₁, hslack₂]

/-- Positive escape margins and zero row slack force the two offsets equal. -/
theorem row_align (a b c x y α β : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h₁ : a * c ≤ α * x) (h₂ : b * c ≤ β * y)
    (heq : (α + β) * (a * x + b * y) = c * (a + b) ^ 2) : x = y := by
  have hslack := row_square_slack a b c x y α β ha.le hb.le hx hy h₁ h₂
  rw [heq, sub_self, zero_mul, zero_mul] at hslack
  have hcoef : 0 < c * a * b := mul_pos (mul_pos hc ha) hb
  have hsq : (x - y) ^ 2 = 0 := le_antisymm
    (nonpos_of_mul_nonpos_right hslack hcoef) (sq_nonneg _)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

private theorem split_of_equality (a b c g s α : ℝ) (hc : c ≠ 0)
    (h₁ : a * c ≤ α * s) (h₂ : b * c ≤ (g - α) * s)
    (hs : g * s = c * (a + b)) : (a + b) * α = a * g := by
  have hcontact : α * s = a * c := by nlinarith only [h₁, h₂, hs]
  have hm : c * ((a + b) * α - a * g) = 0 := by
    linear_combination g * hcontact - α * hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hc)

/-- All four margins are positive. At total width one, the four corner
inequalities force equal left/right offsets and an equal lower/upper split.
The equations are division-free and determine the contact coordinates. -/
theorem contacts (a b c d sL sR αU αD : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hsL : 0 ≤ sL) (hsL₁ : sL ≤ a + b) (hsR : 0 ≤ sR) (hsR₁ : sR ≤ a + b)
    (hαU : 0 ≤ αU) (hαU₁ : αU ≤ c + d) (hαD : 0 ≤ αD) (hαD₁ : αD ≤ c + d)
    (hLU : a * d ≤ αU * (a + b - sL))
    (hRU : b * d ≤ (c + d - αU) * (a + b - sR))
    (hLD : a * c ≤ αD * sL) (hRD : b * c ≤ (c + d - αD) * sR) :
    sL = sR ∧ (c + d) * sL = c * (a + b) ∧
      (a + b) * αD = a * (c + d) ∧ (a + b) * αU = a * (c + d) := by
  have hup := Plank.TwoPlankBodyCS.row_bound ha.le hb.le hd.le
    (sub_nonneg.mpr hsL₁) (sub_nonneg.mpr hsR₁)
    hαU (sub_nonneg.mpr hαU₁) hLU hRU
  have hdown := Plank.TwoPlankBodyCS.row_bound ha.le hb.le hc.le hsL hsR
    hαD (sub_nonneg.mpr hαD₁) hLD hRD
  have hrow : (αD + (c + d - αD)) * (a * sL + b * sR) = c * (a + b) ^ 2 := by
    nlinarith only [hup, hdown]
  have halign := row_align a b c sL sR αD (c + d - αD) ha hb hc hsL hsR hLD hRD hrow
  rw [← halign] at hrow hRD hRU
  have hoffset : (c + d) * sL = c * (a + b) := by
    have hm : (a + b) * ((c + d) * sL - c * (a + b)) = 0 := by
      nlinarith only [hrow]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (ne_of_gt (add_pos ha hb)))
  refine ⟨halign, hoffset, split_of_equality a b c (c + d) sL αD hc.ne' hLD hRD hoffset, ?_⟩
  apply split_of_equality a b d (c + d) (a + b - sL) αU hd.ne' hLU hRU
  nlinarith only [hoffset]

end Plank.Convex.PlanarTight.TwoPlankAlgebra

/-- info: 'Plank.Convex.PlanarTight.TwoPlankAlgebra.row_square_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankAlgebra.row_square_slack

/-- info: 'Plank.Convex.PlanarTight.TwoPlankAlgebra.contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankAlgebra.contacts
