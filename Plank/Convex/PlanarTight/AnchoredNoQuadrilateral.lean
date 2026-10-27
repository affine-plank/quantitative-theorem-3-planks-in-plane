/- An anchored positive plank cannot coexist at equality with the
quadrilateral branch of the contracted two-plank cover on a positive plane. -/
module
public import Plank.Convex.PlanarTight.QuadrilateralShape
public import Plank.Convex.PlanarTight.AnchoredCorner
public import Plank.Convex.PlanarTight.AnchoredReduction
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredNoQuadrilateral

abbrev Point := Fin 3 → ℝ

/-- The two opposite mixed edges of a genuine quadrilateral cannot both
contain the contraction center on a plane with positive coefficients. -/
theorem not_cover (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (T : Point) (hT : T ∈ K) (hT0 : T 0 = 1)
    (q p g r : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hp : 0 < p) (hp₁ : p < 1)
    (hg : 0 < g) (hg₁ : g < 1) (hr : 0 < r) (hr₁ : r < 1)
    (hshape : ∀ z ∈ K, TwoPlankQuadrilateral.InQuadrilateral (z 1) (z 2) q p)
    (hcover : ∀ z ∈ K, z 0 ≤ r ∨
      (r * T 1 + (1 - r) * ((1 - g) * q) ≤ z 1 ∧
        z 1 ≤ r * T 1 + (1 - r) * ((1 - g) * q + g)) ∨
      (r * T 2 + (1 - r) * (g * p) ≤ z 2 ∧
        z 2 ≤ r * T 2 + (1 - r) * (g * p + (1 - g)))) : False := by
  have H : TwoPlankClassification.Ranges K (AffineMap.proj 1) (AffineMap.proj 2) :=
    ⟨fun z hz => ⟨hbox z hz 1, hbox z hz 2⟩, hL 1, hU 1, hL 2, hU 2⟩
  obtain ⟨⟨L, hL, hL1, hL2⟩, ⟨R, hR, hR1, hR2⟩,
    ⟨B, hB, hB1, hB2⟩, ⟨U, hU, hU1, hU2⟩⟩ :=
    QuadrilateralShape.contacts K _ _ H q p hq hq₁ hp hp₁ hshape
  change L 1 = 0 at hL1
  change L 2 = p at hL2
  change R 1 = 1 at hR1
  change R 2 = p at hR2
  change B 1 = q at hB1
  change B 2 = 0 at hB2
  change U 1 = q at hU1
  change U 2 = 1 at hU2
  have hplaneL := hplane L hL
  have hplaneR := hplane R hR
  have hplaneB := hplane B hB
  have hplaneU := hplane U hU
  rw [hL1, hL2] at hplaneL
  rw [hR1, hR2] at hplaneR
  rw [hB1, hB2] at hplaneB
  rw [hU1, hU2] at hplaneU
  have hB0 : 0 < B 0 := by
    have hpos₁ := mul_pos hb (sub_pos.mpr hq₁)
    have hpos₂ := mul_pos hc hp
    have hnonneg := mul_nonneg ha.le (hbox R hR 0).1
    have hprod : 0 < a * B 0 := by nlinarith only [hplaneB, hplaneR, hpos₁, hpos₂, hnonneg]
    by_contra hn
    have hbad := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
    linarith only [hprod, hbad]
  have hL0 : 0 < L 0 := by
    have hpos₁ := mul_pos hb hq
    have hpos₂ := mul_pos hc (sub_pos.mpr hp₁)
    have hnonneg := mul_nonneg ha.le (hbox U hU 0).1
    have hprod : 0 < a * L 0 := by nlinarith only [hplaneL, hplaneU, hpos₁, hpos₂, hnonneg]
    by_contra hn
    have hbad := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hn)
    linarith only [hprod, hbad]
  let Y' : Point →ᵃ[ℝ] ℝ := TwoPlankClassification.reflect (AffineMap.proj 1)
  let Z' : Point →ᵃ[ℝ] ℝ := TwoPlankClassification.reflect (AffineMap.proj 2)
  have hBR := AnchoredCorner.on_edge K hK (AffineMap.proj 0) Y' (AffineMap.proj 2)
    T R B hT hR hB hT0 p (1 - q) g r hp hg hg₁ hr hr₁
    (by change 1 - R 1 = 0; rw [hR1]; ring) hR2
    (by change 1 - B 1 = 1 - q; rw [hB1]) hB2
    (by
      change 0 < g * R 0 + (1 - g) * B 0
      exact add_pos_of_nonneg_of_pos (mul_nonneg hg.le (hbox R hR 0).1)
        (mul_pos (sub_pos.mpr hg₁) hB0)) (by
      rintro ⟨z, hz, hx, hy, hzz⟩
      change 1 - z 1 < r * (1 - T 1) + (1 - r) * ((1 - g) * (1 - q)) at hy
      change z 2 < r * T 2 + (1 - r) * (g * p) at hzz
      rcases hcover z hz with h | h | h
      · exact not_le_of_gt hx h
      · nlinarith only [hy, h.2]
      · exact not_lt_of_ge h.1 hzz)
  change p * (1 - T 1) + (1 - q) * T 2 = p * (1 - q) at hBR
  have hLU := AnchoredCorner.on_edge K hK (AffineMap.proj 0) (AffineMap.proj 1) Z'
    T L U hT hL hU hT0 (1 - p) q g r (sub_pos.mpr hp₁) hg hg₁ hr hr₁
    hL1 (by change 1 - L 2 = 1 - p; rw [hL2]) hU1
    (by change 1 - U 2 = 0; rw [hU2]; ring)
    (by
      change 0 < g * L 0 + (1 - g) * U 0
      exact add_pos_of_pos_of_nonneg (mul_pos hg hL0)
        (mul_nonneg (sub_pos.mpr hg₁).le (hbox U hU 0).1)) (by
      rintro ⟨z, hz, hx, hy, hzz⟩
      change z 1 < r * T 1 + (1 - r) * ((1 - g) * q) at hy
      change 1 - z 2 < r * (1 - T 2) + (1 - r) * (g * (1 - p)) at hzz
      rcases hcover z hz with h | h | h
      · exact not_le_of_gt hx h
      · exact not_lt_of_ge h.1 hy
      · nlinarith only [hzz, h.2])
  change (1 - p) * T 1 + q * (1 - T 2) = (1 - p) * q at hLU
  have hT1 : q ≤ T 1 := by
    have hnonneg := mul_nonneg (sub_pos.mpr hq₁).le (hbox T hT 2).1
    have hprod : 0 ≤ p * (T 1 - q) := by nlinarith only [hBR, hnonneg]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hprod hp)
  have hT2 : 0 ≤ T 2 - p := by
    have hnonneg := mul_nonneg (sub_pos.mpr hp₁).le (hbox T hT 1).1
    have hprod : 0 ≤ q * (T 2 - p) := by nlinarith only [hLU, hnonneg]
    exact nonneg_of_mul_nonneg_right hprod hq
  have hpos := mul_pos hb (lt_of_lt_of_le hq hT1)
  have hnonneg₁ := mul_nonneg hc.le hT2
  have hnonneg₂ := mul_nonneg ha.le (sub_nonneg.mpr (hbox L hL 0).2)
  have hplaneT := hplane T hT
  rw [hT0] at hplaneT
  nlinarith only [hplaneT, hplaneL, hpos, hnonneg₁, hnonneg₂]

/-- The internal quadrilateral alternative in the anchored contraction
is impossible for three distinct directions with a positive plane normal. -/
theorem not_interior (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (T : Point) (hT : T ∈ K) (hT0 : T 0 = 1) :
    ¬ TwoPlankInterior.Normal K (AffineMap.proj 1) (AffineMap.proj 2)
      ((lo 1 - hi 0 * T 1) / (1 - hi 0)) ((hi 1 - hi 0 * T 1) / (1 - hi 0))
      ((lo 2 - hi 0 * T 2) / (1 - hi 0)) ((hi 2 - hi 0 * T 2) / (1 - hi 0)) := by
  rintro ⟨g, q, p, hg, hg₁, hq, hq₁, hp, hp₁, hl, hu, hm, hv, hshape⟩
  have hs := hsum
  rw [Fin.sum_univ_three, hanchor, sub_zero] at hs
  have hr : 0 < hi 0 := by simpa only [hanchor] using hwidth 0
  have hwidth₁ := hwidth 1
  have hwidth₂ := hwidth 2
  have hr₁ : hi 0 < 1 := by linarith only [hs, hwidth₁, hwidth₂]
  have hd : 0 < 1 - hi 0 := sub_pos.mpr hr₁
  have endpoint (u t v : ℝ) (h : (u - hi 0 * t) / (1 - hi 0) = v) :
      u = hi 0 * t + (1 - hi 0) * v := by
    have heq := (div_eq_iff hd.ne').mp h
    nlinarith only [heq]
  have heL := endpoint _ _ _ hl
  have heU := endpoint _ _ _ hu
  have heM := endpoint _ _ _ hm
  have heV := endpoint _ _ _ hv
  apply not_cover K hK hbox hL hU a b c d ha hb hc hplane T hT hT0
    q p g (hi 0) hq hq₁ hp hp₁ hg hg₁ hr hr₁ hshape
  intro z hz
  obtain ⟨i, hil, hiu⟩ := hcover z hz
  fin_cases i
  · exact Or.inl hiu
  · change lo 1 ≤ z 1 at hil
    change z 1 ≤ hi 1 at hiu
    rw [heL] at hil
    rw [heU] at hiu
    exact Or.inr (Or.inl ⟨hil, hiu⟩)
  · change lo 2 ≤ z 2 at hil
    change z 2 ≤ hi 2 at hiu
    rw [heM] at hil
    rw [heV] at hiu
    exact Or.inr (Or.inr ⟨hil, hiu⟩)

/-- The four triangular enclosure alternatives, with either coordinate
and either orientation chosen as the anchored two-plank window. -/
def Triangular (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ) (l u m v : ℝ) : Prop :=
  TwoPlankClassification.Anchored K X Y l u m v ∨
  TwoPlankClassification.Anchored K (TwoPlankClassification.reflect X) Y (1 - u) (1 - l) m v ∨
  TwoPlankClassification.Anchored K Y X m v l u ∨
  TwoPlankClassification.Anchored K (TwoPlankClassification.reflect Y) X (1 - v) (1 - m) l u

/-- Every anchored positive three-plank equality cover on a positive plane
contracts to a triangular two-plank enclosure. This is a necessary shape
reduction; the original three windows still require classification. -/
theorem two_plank_triangular (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (T : Point) (hT : T ∈ K) (hT0 : T 0 = 1) :
    Triangular K (AffineMap.proj 1) (AffineMap.proj 2)
      ((lo 1 - hi 0 * T 1) / (1 - hi 0)) ((hi 1 - hi 0 * T 1) / (1 - hi 0))
      ((lo 2 - hi 0 * T 2) / (1 - hi 0)) ((hi 2 - hi 0 * T 2) / (1 - hi 0)) :=
  (AnchoredReduction.two_plank_normal K hK hbox hL hU lo hi hwidth hanchor hcover hsum T hT hT0).resolve_left
    (not_interior K hK hbox hL hU a b c d ha hb hc hplane lo hi hwidth hanchor hcover hsum T hT hT0)

end Plank.Convex.PlanarTight.AnchoredNoQuadrilateral

/-- info: 'Plank.Convex.PlanarTight.AnchoredNoQuadrilateral.not_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredNoQuadrilateral.not_cover

/-- info: 'Plank.Convex.PlanarTight.AnchoredNoQuadrilateral.not_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredNoQuadrilateral.not_interior

/-- info: 'Plank.Convex.PlanarTight.AnchoredNoQuadrilateral.two_plank_triangular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredNoQuadrilateral.two_plank_triangular
