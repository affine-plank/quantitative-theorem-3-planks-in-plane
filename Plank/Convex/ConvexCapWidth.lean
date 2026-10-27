/- A cap in a convex set needs a window at least as wide as its height.
The two coordinates may be arbitrary affine maps on a real vector space.
Only three actual points and two one-sided height bounds are used. -/
module
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.ConvexCapWidth

abbrev Point2 := Fin 2 → ℝ

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Three contacts suffice for the lower-cap width bound. Only the two
width contacts need an upper height bound; all other values are unrestricted. -/
theorem cap_bound_lower_affine (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (L R B : E) (hL : L ∈ K) (hR : R ∈ K) (hB : B ∈ K)
    (hXL : X L = 0) (hXR : X R = 1) (hYB : Y B = 0)
    (hYL : Y L ≤ 1) (hYR : Y R ≤ 1)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (l h : ℝ) (hlh : l ≤ h)
    (hcap : ∀ p ∈ K, Y p < a → l ≤ X p ∧ X p ≤ h) :
    a ≤ h - l := by
  by_contra hfail
  have hsmall : h - l < a := lt_of_not_ge hfail
  have hwidth : 0 ≤ h - l := sub_nonneg.mpr hlh
  let t : ℝ := (a + (h - l)) / 2
  have ht0 : 0 ≤ t := by dsimp [t]; linarith only [ha0, hwidth]
  have hta : t < a := by dsimp [t]; linarith only [hsmall]
  have hwt : h - l < t := by dsimp [t]; linarith only [hsmall]
  have ht1 : t ≤ 1 := hta.le.trans ha1
  have hbelow (p : E) (hyp : Y p ≤ 1) : Y (AffineMap.lineMap B p t) < a := by
    rw [Y.apply_lineMap, AffineMap.lineMap_apply_ring, hYB, mul_zero, zero_add]
    have hheight := mul_le_mul_of_nonneg_left hyp ht0
    exact lt_of_le_of_lt (by simpa only [mul_one] using hheight) hta
  have hleft := (hcap (AffineMap.lineMap B L t)
    (hK.lineMap_mem hB hL ⟨ht0, ht1⟩) (hbelow L hYL)).1
  have hright := (hcap (AffineMap.lineMap B R t)
    (hK.lineMap_mem hB hR ⟨ht0, ht1⟩) (hbelow R hYR)).2
  have hgap : X (AffineMap.lineMap B R t) - X (AffineMap.lineMap B L t) = t := by
    rw [X.apply_lineMap, X.apply_lineMap, AffineMap.lineMap_apply_ring,
      AffineMap.lineMap_apply_ring, hXL, hXR]
    ring
  linarith only [hleft, hright, hgap, hwt]

/-- The upper-cap bound is the lower-cap bound after reflecting the height.
Only the two width contacts need a lower height bound. -/
theorem cap_bound_upper_affine (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (L R T : E) (hL : L ∈ K) (hR : R ∈ K) (hT : T ∈ K)
    (hXL : X L = 0) (hXR : X R = 1) (hYT : Y T = 1)
    (hYL : 0 ≤ Y L) (hYR : 0 ≤ Y R)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (l h : ℝ) (hlh : l ≤ h)
    (hcap : ∀ p ∈ K, b < Y p → l ≤ X p ∧ X p ≤ h) :
    1 - b ≤ h - l := by
  refine cap_bound_lower_affine K hK X (AffineMap.const ℝ E (1 : ℝ) - Y)
    L R T hL hR hT hXL hXR ?_ ?_ ?_ (1 - b) (sub_nonneg.mpr hb1)
    (by linarith only [hb0]) l h hlh ?_
  · change 1 - Y T = 0
    rw [hYT, sub_self]
  · change 1 - Y L ≤ 1
    linarith only [hYL]
  · change 1 - Y R ≤ 1
    linarith only [hYR]
  · intro p hp hbelow
    change 1 - Y p < 1 - b at hbelow
    exact hcap p hp (by linarith only [hbelow])


variable {ι : Type*}

/-- A window containing the entire strict lower cap has width at least a.
The threshold a=0 is allowed. No compactness hypothesis is needed. -/
theorem cap_bound_lower_coord (K : Set (ι → ℝ)) (hconv : Convex ℝ K) (i j : ι)
    (hbox : ∀ p ∈ K, ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    (pL pR pB : ι → ℝ) (hL : pL ∈ K) (hR : pR ∈ K) (hB : pB ∈ K)
    (hxL : pL i = 0) (hxR : pR i = 1) (hyB : pB j = 0)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (l h : ℝ) (hlh : l ≤ h)
    (hcover : ∀ p ∈ K, p j < a → l ≤ p i ∧ p i ≤ h) :
    a ≤ h - l := by
  exact cap_bound_lower_affine K hconv (AffineMap.proj i) (AffineMap.proj j)
    pL pR pB hL hR hB hxL hxR hyB (hbox pL hL j).2 (hbox pR hR j).2
    a ha0 ha1 l h hlh hcover

/-- A window containing the entire strict upper cap has width at least 1-b.
The threshold b=1 is allowed. The top anchor is an actual point of K. -/
theorem cap_bound_upper_coord (K : Set (ι → ℝ)) (hconv : Convex ℝ K) (i j : ι)
    (hbox : ∀ p ∈ K, ∀ k, 0 ≤ p k ∧ p k ≤ 1)
    (pL pR pT : ι → ℝ) (hL : pL ∈ K) (hR : pR ∈ K) (hT : pT ∈ K)
    (hxL : pL i = 0) (hxR : pR i = 1) (hyT : pT j = 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (l h : ℝ) (hlh : l ≤ h)
    (hcover : ∀ p ∈ K, b < p j → l ≤ p i ∧ p i ≤ h) :
    1 - b ≤ h - l := by
  exact cap_bound_upper_affine K hconv (AffineMap.proj i) (AffineMap.proj j)
    pL pR pT hL hR hT hxL hxR hyT (hbox pL hL j).1 (hbox pR hR j).1
    b hb0 hb1 l h hlh hcover

/-- The two-dimensional lower-cap interface. -/
theorem cap_bound_lower (K : Set Point2) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j : Fin 2, 0 ≤ p j ∧ p j ≤ 1)
    (pL pR pB : Point2) (hL : pL ∈ K) (hR : pR ∈ K) (hB : pB ∈ K)
    (hxL : pL 0 = 0) (hxR : pR 0 = 1) (hyB : pB 1 = 0)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (l h : ℝ) (hlh : l ≤ h)
    (hcover : ∀ p ∈ K, p 1 < a → l ≤ p 0 ∧ p 0 ≤ h) :
    a ≤ h - l :=
  cap_bound_lower_coord K hconv 0 1 hbox pL pR pB hL hR hB hxL hxR hyB a ha0 ha1 l h hlh hcover

/-- The two-dimensional upper-cap interface. -/
theorem cap_bound_upper (K : Set Point2) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j : Fin 2, 0 ≤ p j ∧ p j ≤ 1)
    (pL pR pT : Point2) (hL : pL ∈ K) (hR : pR ∈ K) (hT : pT ∈ K)
    (hxL : pL 0 = 0) (hxR : pR 0 = 1) (hyT : pT 1 = 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (l h : ℝ) (hlh : l ≤ h)
    (hcover : ∀ p ∈ K, b < p 1 → l ≤ p 0 ∧ p 0 ≤ h) :
    1 - b ≤ h - l :=
  cap_bound_upper_coord K hconv 0 1 hbox pL pR pT hL hR hT hxL hxR hyT b hb0 hb1 l h hlh hcover

end Plank.Convex.ConvexCapWidth

/-- info: 'Plank.Convex.ConvexCapWidth.cap_bound_lower_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.ConvexCapWidth.cap_bound_lower_affine


/-- info: 'Plank.Convex.ConvexCapWidth.cap_bound_upper_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.ConvexCapWidth.cap_bound_upper_affine

/-- info: 'Plank.Convex.ConvexCapWidth.cap_bound_lower_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCapWidth.cap_bound_lower_coord

/-- info: 'Plank.Convex.ConvexCapWidth.cap_bound_upper_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCapWidth.cap_bound_upper_coord

/-- info: 'Plank.Convex.ConvexCapWidth.cap_bound_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCapWidth.cap_bound_lower

/-- info: 'Plank.Convex.ConvexCapWidth.cap_bound_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.ConvexCapWidth.cap_bound_upper
