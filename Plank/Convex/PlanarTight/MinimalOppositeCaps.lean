/- Opposite caps at minimum width cannot occupy two distinct planar directions
when the lower-cap window is strictly internal. -/
module
public import Plank.Convex.PlanarTight.CapTriangle
public import Plank.Convex.ConvexCapWidth
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.MinimalOppositeCaps

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Two minimum-width caps force the horizontal extreme contacts onto the
same upper face and the same third-coordinate fiber. A nonzero horizontal
coefficient in the plane equation rules this out. -/
theorem incompatible (K : Set E) (hK : Convex ℝ K) (X Y Z : E →ᵃ[ℝ] ℝ)
    (hX : ∀ p ∈ K, 0 ≤ X p ∧ X p ≤ 1)
    (hY : ∀ p ∈ K, 0 ≤ Y p ∧ Y p ≤ 1)
    (hZ : ∀ p ∈ K, 0 ≤ Z p ∧ Z p ≤ 1)
    (hXL : ∃ p ∈ K, X p = 0) (hXR : ∃ p ∈ K, X p = 1)
    (hYB : ∃ p ∈ K, Y p = 0) (hYT : ∃ p ∈ K, Y p = 1)
    (hZL : ∃ p ∈ K, Z p = 0) (hZR : ∃ p ∈ K, Z p = 1)
    (a b lX uX lZ uZ : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1) (hlX : 0 < lX) (huX : uX < 1)
    (hlZ : 0 ≤ lZ) (huZ : uZ ≤ 1)
    (hwX : uX - lX = a) (hwZ : uZ - lZ = 1 - b)
    (hlower : ∀ p ∈ K, Y p < a → lX ≤ X p ∧ X p ≤ uX)
    (hupper : ∀ p ∈ K, b < Y p → lZ ≤ Z p ∧ Z p ≤ uZ)
    (A B C D : ℝ) (hA : A ≠ 0)
    (hplane : ∀ p ∈ K, A * X p + B * Y p + C * Z p = D) : False := by
  obtain ⟨c, hc0, hc1, hlc, huc, hshapeX⟩ := CapTriangle.lower K hK X Y
    (fun p hp => ⟨hX p hp, hY p hp⟩) hXL hXR hYB
    a lX uX ha ha1 hlX.le huX.le hwX hlower
  obtain ⟨d, _, _, _, _, hshapeZ⟩ := CapTriangle.upper K hK Z Y
    (fun p hp => ⟨hZ p hp, hY p hp⟩) hZL hZR hYT
    b lZ uZ hb hb1 hlZ huZ hwZ hupper
  have hcpos : 0 < c := by
    by_contra! hn
    have he : c = 0 := le_antisymm hn hc0
    rw [he, mul_zero] at hlc
    exact (ne_of_gt hlX) hlc
  have hclt : c < 1 := by
    by_contra! hn
    have he : c = 1 := le_antisymm hc1 hn
    rw [he, mul_one] at huc
    linarith only [huc, huX]
  obtain ⟨L, hL, hL0⟩ := hXL
  obtain ⟨R, hR, hR1⟩ := hXR
  have hLY : Y L = 1 := by
    have hs := (hshapeX L hL).1
    rw [hL0] at hs
    have hy := (hY L hL).2
    nlinarith only [hs, hy, hcpos]
  have hRY : Y R = 1 := by
    have hs := (hshapeX R hR).2
    rw [hR1] at hs
    have hy := (hY R hR).2
    nlinarith only [hs, hy, hclt]
  have hLZ : Z L = d := by
    have hs := hshapeZ L hL
    rw [hLY, mul_one, mul_one] at hs
    linarith only [hs.1, hs.2]
  have hRZ : Z R = d := by
    have hs := hshapeZ R hR
    rw [hRY, mul_one, mul_one] at hs
    linarith only [hs.1, hs.2]
  have hpL := hplane L hL
  have hpR := hplane R hR
  rw [hL0, hLY, hLZ, mul_zero, mul_one, zero_add] at hpL
  rw [hR1, hRY, hRZ, mul_one, mul_one] at hpR
  apply hA
  linarith only [hpL, hpR]

/-- Assigning the two opposite caps to different windows costs strictly
more than one in three nonparallel planar directions. Only the lower-cap
window needs both endpoints strictly inside the unit interval. -/
theorem not_tight (K : Set E) (hK : Convex ℝ K) (X Y Z : E →ᵃ[ℝ] ℝ)
    (hX : ∀ p ∈ K, 0 ≤ X p ∧ X p ≤ 1)
    (hY : ∀ p ∈ K, 0 ≤ Y p ∧ Y p ≤ 1)
    (hZ : ∀ p ∈ K, 0 ≤ Z p ∧ Z p ≤ 1)
    (hXL : ∃ p ∈ K, X p = 0) (hXR : ∃ p ∈ K, X p = 1)
    (hYB : ∃ p ∈ K, Y p = 0) (hYT : ∃ p ∈ K, Y p = 1)
    (hZL : ∃ p ∈ K, Z p = 0) (hZR : ∃ p ∈ K, Z p = 1)
    (a b lX uX lZ uZ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb1 : b < 1)
    (hlX : 0 < lX) (huX : uX < 1) (hXord : lX ≤ uX)
    (hlZ : 0 ≤ lZ) (huZ : uZ ≤ 1) (hZord : lZ ≤ uZ)
    (hlower : ∀ p ∈ K, Y p < a → lX ≤ X p ∧ X p ≤ uX)
    (hupper : ∀ p ∈ K, b < Y p → lZ ≤ Z p ∧ Z p ≤ uZ)
    (A B C D : ℝ) (hA : A ≠ 0)
    (hplane : ∀ p ∈ K, A * X p + B * Y p + C * Z p = D) :
    (uX - lX) + (b - a) + (uZ - lZ) ≠ 1 := by
  intro hsum
  obtain ⟨L, hL, hL0⟩ := hXL
  obtain ⟨R, hR, hR1⟩ := hXR
  obtain ⟨Q, hQ, hQ0⟩ := hYB
  obtain ⟨S, hS, hS0⟩ := hZL
  obtain ⟨T, hT, hT1⟩ := hZR
  obtain ⟨U, hU, hU1⟩ := hYT
  have hwX := ConvexCapWidth.cap_bound_lower_affine K hK X Y L R Q
    hL hR hQ hL0 hR1 hQ0 (hY L hL).2 (hY R hR).2
    a ha.le (hab.trans hb1.le) lX uX hXord hlower
  have hwZ := ConvexCapWidth.cap_bound_upper_affine K hK Z Y S T U
    hS hT hU hS0 hT1 hU1 (hY S hS).1 (hY T hT).1
    b (ha.le.trans hab) hb1.le lZ uZ hZord hupper
  exact incompatible K hK X Y Z hX hY hZ
    ⟨L, hL, hL0⟩ ⟨R, hR, hR1⟩ ⟨Q, hQ, hQ0⟩ ⟨U, hU, hU1⟩
    ⟨S, hS, hS0⟩ ⟨T, hT, hT1⟩ a b lX uX lZ uZ ha (hab.trans_lt hb1)
    (ha.trans_le hab) hb1 hlX huX hlZ huZ
    (by linarith only [hwX, hwZ, hsum]) (by linarith only [hwX, hwZ, hsum])
    hlower hupper A B C D hA hplane

end Plank.Convex.PlanarTight.MinimalOppositeCaps

/-- info: 'Plank.Convex.PlanarTight.MinimalOppositeCaps.incompatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.MinimalOppositeCaps.incompatible

/-- info: 'Plank.Convex.PlanarTight.MinimalOppositeCaps.not_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.MinimalOppositeCaps.not_tight
