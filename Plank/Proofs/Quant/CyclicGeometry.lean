module
/-
# Geometric consequences of a cyclic obstruction

An obstructed threshold point excludes two whole-plane exterior cells.
An obstructed deficit seed also constructs a point strictly inside the
triangle and all three planks. Consequently a null triple overlap closes
the actual area bound. Positive triple overlap still requires an estimate.
-/
public import Plank.Proofs.Quant.CyclicArea

@[expose] public section

noncomputable section

namespace Quant.CyclicGeometry

open Set MeasureTheory CommonVertex CyclicArea OrdinalArea

def w0 (a c : ℝ) : ℝ := a * (1 - c) + c
def w1 (b c : ℝ) : ℝ := 1 - c + b * c
def w2 (a b : ℝ) : ℝ := 1 - a * b

theorem weights_pos {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1) :
    0 < w0 a c ∧ 0 < w1 b c ∧ 0 < w2 a b := by
  have hc' := sub_pos.mpr hc.2
  have ha0 := ha.1
  have hb0 := hb.1
  have hc0 := hc.1
  have hab : a * b < 1 := lt_trans (mul_lt_of_lt_one_right ha.1 hb.2) ha.2
  dsimp [w0, w1, w2]
  exact ⟨by positivity, by positivity, sub_pos.mpr hab⟩

theorem dot_relation (C : Config) {b a c : ℝ}
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) (x : ℝ × ℝ) :
    w0 a c * dot (C.plank 0).u x =
      w1 b c * dot (C.plank 1).u x + w2 a b * dot (C.plank 2).u x := by
  rw [hu₀, hu₁, hu₂]
  dsimp [w0, w1, w2, dot]
  ring

/-- No assumption that the threshold point is in the deficit triangle is
needed for these strict inequalities between the six boundary levels. -/
theorem level_separation_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) {z : ℝ × ℝ}
    (hz : z ∈ badSeeds C b a c) :
    (w0 a c * (C.plank 0).lo <
      w1 b c * (C.plank 1).hi + w2 a b * (C.plank 2).hi) ∧
    (w1 b c * (C.plank 1).lo + w2 a b * (C.plank 2).lo <
      w0 a c * (C.plank 0).hi) := by
  have hr : ∀ i, 0 ≤ widths C i := fun i => sub_nonneg.mpr (C.plank i).lo_le_hi
  have hbounds := CyclicAssignment.Bad.bounds
    (mul_nonneg hb.1.le (hr 1)) (mul_nonneg (sub_nonneg.mpr hb.2.le) (hr 2))
    (mul_nonneg ha.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr ha.2.le) (hr 2))
    (mul_nonneg hc.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr hc.2.le) (hr 1)) hz
  rcases hbounds with ⟨hx0, hxpq, hys, hyr, hzu, hzt⟩
  rcases weights_pos hb ha hc with ⟨hw0, hw1, hw2⟩
  have htop : w0 a c * (b * widths C 1 + (1 - b) * widths C 2) -
      w1 b c * (-((1 - a) * widths C 2)) -
      w2 a b * (-((1 - c) * widths C 1)) =
        w1 b c * widths C 1 + w2 a b * widths C 2 := by
    dsimp [w0, w1, w2]
    ring
  have hbottom : w0 a c * widths C 0 =
      w1 b c * (a * widths C 0) + w2 a b * (c * widths C 0) := by
    dsimp [w0, w1, w2]
    ring
  have ht : w0 a c * threshold C z 0 - w1 b c * threshold C z 1 -
      w2 a b * threshold C z 2 < w1 b c * widths C 1 + w2 a b * widths C 2 := by
    have h0 := mul_lt_mul_of_pos_left hxpq hw0
    have h1 := mul_lt_mul_of_pos_left hys hw1
    have h2 := mul_lt_mul_of_pos_left hzu hw2
    linarith
  have hl : -(w0 a c * widths C 0) <
      w0 a c * threshold C z 0 - w1 b c * threshold C z 1 -
      w2 a b * threshold C z 2 := by
    have h0 := mul_lt_mul_of_pos_left hx0 hw0
    have h1 := mul_lt_mul_of_pos_left hyr hw1
    have h2 := mul_lt_mul_of_pos_left hzt hw2
    linarith
  have hid : w0 a c * threshold C z 0 - w1 b c * threshold C z 1 -
      w2 a b * threshold C z 2 =
      w0 a c * (C.plank 0).lo - w1 b c * (C.plank 1).lo -
      w2 a b * (C.plank 2).lo := by
    have hrel := dot_relation C hu₀ hu₁ hu₂ (z + base C)
    dsimp [threshold]
    nlinarith
  rw [hid] at ht hl
  dsimp [widths] at ht hl
  constructor <;> nlinarith

/-- The two all-equal cyclic signs (ABC labels 100 and 011) are impossible
even outside the original triangle, including their equality boundaries. -/
theorem two_cells_empty_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) {z : ℝ × ℝ}
    (hz : z ∈ badSeeds C b a c) (x : ℝ × ℝ) :
    ¬ ((C.plank 0).hi ≤ dot (C.plank 0).u x ∧
        dot (C.plank 1).u x ≤ (C.plank 1).lo ∧
        dot (C.plank 2).u x ≤ (C.plank 2).lo) ∧
    ¬ (dot (C.plank 0).u x ≤ (C.plank 0).lo ∧
        (C.plank 1).hi ≤ dot (C.plank 1).u x ∧
        (C.plank 2).hi ≤ dot (C.plank 2).u x) := by
  have hsep := level_separation_of_bad C hb ha hc hu₀ hu₁ hu₂ hz
  have hrel := dot_relation C hu₀ hu₁ hu₂ x
  rcases weights_pos hb ha hc with ⟨hw0, hw1, hw2⟩
  constructor
  · rintro ⟨h0, h1, h2⟩
    have h0' := mul_le_mul_of_nonneg_left h0 hw0.le
    have h1' := mul_le_mul_of_nonneg_left h1 hw1.le
    have h2' := mul_le_mul_of_nonneg_left h2 hw2.le
    linarith [hsep.2]
  · rintro ⟨h0, h1, h2⟩
    have h0' := mul_le_mul_of_nonneg_left h0 hw0.le
    have h1' := mul_le_mul_of_nonneg_left h1 hw1.le
    have h2' := mul_le_mul_of_nonneg_left h2 hw2.le
    linarith [hsep.1]

private theorem numerator_bounds {p q r s t u X Y Z : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : 0 < s) (_ht : 0 < t) (hu : 0 < u)
    (hX : q < X ∧ X < p) (hY : r < Y ∧ Y < s) (hZ : u < Z ∧ Z < t) :
    0 < p * s * Z + q * u * Y - s * u * X ∧
      p * s * Z + q * u * Y - s * u * X < p * s * t + q * r * u := by
  have hY0 : 0 < Y := hr.trans hY.1
  have h1 := mul_lt_mul_of_pos_left hZ.1 (mul_pos hp hs)
  have h2 := mul_lt_mul_of_pos_left hX.2 (mul_pos hs hu)
  have h3 := mul_pos (mul_pos hq hu) hY0
  have h4 := mul_lt_mul_of_pos_left hX.1 hs
  have h5 := mul_lt_mul_of_pos_left hY.2 hq
  have h6 : 0 < s * X - q * Y := by nlinarith only [h4, h5]
  have h7 := mul_pos (mul_pos hp hs) (sub_pos.mpr hZ.2)
  have h8 := mul_pos hu h6
  have h9 := mul_pos (mul_pos hq hr) hu
  constructor
  · nlinarith only [h1, h2, h3]
  · nlinarith only [h7, h8, h9]

/-- Three cyclic equations with a dominant coefficient in each row have
a strictly internal cube solution at every threshold between the two
coefficients. The proof is the explicit inverse, with signed cofactors. -/
theorem mixed_cycle_solution {p q r s t u X Y Z : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : 0 < s) (ht : 0 < t) (hu : 0 < u)
    (hX : q < X ∧ X < p) (hY : r < Y ∧ Y < s) (hZ : u < Z ∧ Z < t) :
    ∃ α β γ : ℝ, (0 < α ∧ α < 1) ∧ (0 < β ∧ β < 1) ∧ (0 < γ ∧ γ < 1) ∧
      p * β + q * γ = X ∧ r * α + s * γ = Y ∧ t * α + u * β = Z := by
  let D := p * s * t + q * r * u
  have hD : 0 < D := add_pos (mul_pos (mul_pos hp hs) ht) (mul_pos (mul_pos hq hr) hu)
  have h0 := numerator_bounds hp hq hr hs ht hu hX hY hZ
  have h1 := numerator_bounds hs hr hu ht hp hq hY hZ hX
  have h2 := numerator_bounds ht hu hq hp hs hr hZ hX hY
  let N0 := p * s * Z + q * u * Y - s * u * X
  let N1 := s * t * X + r * q * Z - t * q * Y
  let N2 := t * p * Y + u * r * X - p * r * Z
  have h0' : 0 < N0 ∧ N0 < D := h0
  have h1' : 0 < N1 ∧ N1 < D := by
    dsimp [N1, D]
    constructor
    · exact h1.1
    · nlinarith only [h1.2]
  have h2' : 0 < N2 ∧ N2 < D := by
    dsimp [N2, D]
    constructor
    · exact h2.1
    · nlinarith only [h2.2]
  refine ⟨N0 / D, N1 / D, N2 / D,
    ⟨div_pos h0'.1 hD, (div_lt_one hD).mpr h0'.2⟩,
    ⟨div_pos h1'.1 hD, (div_lt_one hD).mpr h1'.2⟩,
    ⟨div_pos h2'.1 hD, (div_lt_one hD).mpr h2'.2⟩, ?_, ?_, ?_⟩ <;>
    dsimp [N0, N1, N2] <;> field_simp [hD.ne'] <;> dsimp [D] <;> ring

/-- The two bad boxes give a fully mixed side assignment. This asserts
membership in the open cube, not a binary exterior assignment. -/
theorem mixed_side_of_bad {p q r s t u X Y Z : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : 0 < s) (ht : 0 < t) (hu : 0 < u)
    (h : CyclicAssignment.Bad p q r s t u X Y Z) :
    ∃ α β γ : ℝ, (0 < α ∧ α < 1) ∧ (0 < β ∧ β < 1) ∧ (0 < γ ∧ γ < 1) ∧
      p * β + q * γ = X ∧ r * α - s * γ = Y ∧ t * α - u * β = Z := by
  rcases h with ⟨hX, hY, hZ⟩ | ⟨hX, hY, hZ⟩
  · obtain ⟨α, β, γ, hα, hβ, hγ, h0, h1, h2⟩ :=
      mixed_cycle_solution hp hq hr hs ht hu hX
        (X := X) (Y := r - Y) (Z := t - Z)
        ⟨by linarith [hY.2], by linarith [hY.1]⟩
        ⟨by linarith [hZ.2], by linarith [hZ.1]⟩
    refine ⟨1 - α, β, γ, ⟨by linarith [hα.2], by linarith [hα.1]⟩,
      hβ, hγ, h0, ?_, ?_⟩ <;> nlinarith
  · obtain ⟨α, γ, β, hα, hγ, hβ, h0, h2, h1⟩ :=
      mixed_cycle_solution hq hp ht hu hr hs hX
        (X := X) (Y := t - Z) (Z := r - Y)
        ⟨by linarith [hZ.2], by linarith [hZ.1]⟩
        ⟨by linarith [hY.2], by linarith [hY.1]⟩
    refine ⟨1 - α, β, γ, ⟨by linarith [hα.2], by linarith [hα.1]⟩,
      hβ, hγ, ?_, ?_, ?_⟩ <;> nlinarith

theorem widths_pos_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    {z : ℝ × ℝ} (hz : z ∈ badSeeds C b a c) :
    ∀ i, 0 < widths C i := by
  have hr : ∀ i, 0 ≤ widths C i := fun i => sub_nonneg.mpr (C.plank i).lo_le_hi
  have hab := sub_pos.mpr ha.2
  have hbc := sub_pos.mpr hb.2
  have hcc := sub_pos.mpr hc.2
  rcases hz with ⟨hX, hY, hZ⟩ | ⟨hX, hY, hZ⟩
  · have h0 : 0 < c * widths C 0 := by
      nlinarith only [hZ.1, hZ.2, mul_nonneg hcc.le (hr 1)]
    have h1 : 0 < b * widths C 1 := by
      linarith [mul_nonneg hbc.le (hr 2)]
    have h2 : 0 < (1 - a) * widths C 2 := by
      nlinarith only [hY.1, hY.2, mul_nonneg ha.1.le (hr 0)]
    intro i
    fin_cases i
    · exact (mul_pos_iff.mp h0).resolve_right (fun h => (not_lt_of_ge hc.1.le) h.1) |>.2
    · exact (mul_pos_iff.mp h1).resolve_right (fun h => (not_lt_of_ge hb.1.le) h.1) |>.2
    · exact (mul_pos_iff.mp h2).resolve_right (fun h => (not_lt_of_ge hab.le) h.1) |>.2
  · have h0 : 0 < a * widths C 0 := by
      nlinarith only [hY.1, hY.2, mul_nonneg hab.le (hr 2)]
    have h1 : 0 < (1 - c) * widths C 1 := by
      nlinarith only [hZ.1, hZ.2, mul_nonneg hc.1.le (hr 0)]
    have h2 : 0 < (1 - b) * widths C 2 := by
      linarith [mul_nonneg hb.1.le (hr 1)]
    intro i
    fin_cases i
    · exact (mul_pos_iff.mp h0).resolve_right (fun h => (not_lt_of_ge ha.1.le) h.1) |>.2
    · exact (mul_pos_iff.mp h1).resolve_right (fun h => (not_lt_of_ge hcc.le) h.1) |>.2
    · exact (mul_pos_iff.mp h2).resolve_right (fun h => (not_lt_of_ge hbc.le) h.1) |>.2

/-- Recover the deficit seed from its mixed common point. The linear part
depends only on the three normal directions. -/
def seedOf (C : Config) (b a c : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ((C.plank 0).lo + (C.plank 2).lo - c * x.1 + (1 - b - c) * x.2,
    (C.plank 1).lo - (C.plank 2).hi + (c - a) * x.1 + (c - 1) * x.2)

/-- An obstructed deficit seed constructs a strict common point whose affine
seed image is the original seed. This retains the relation needed for area
comparison, rather than only asserting existence of a common point. -/
theorem exists_strict_common_point_with_seed_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) {z : ℝ × ℝ}
    (hzT : z ∈ RowDeletion.triangle C.deficit) (hz : z ∈ badSeeds C b a c) :
    ∃ x : ℝ × ℝ, (0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1) ∧
      (∀ i, (C.plank i).lo < dot (C.plank i).u x ∧
        dot (C.plank i).u x < (C.plank i).hi) ∧ seedOf C b a c x = z := by
  have hr := widths_pos_of_bad C hb ha hc hz
  obtain ⟨α, β, γ, hα, hβ, hγ, h0, h1, h2⟩ := mixed_side_of_bad
    (mul_pos hb.1 (hr 1)) (mul_pos (sub_pos.mpr hb.2) (hr 2))
    (mul_pos ha.1 (hr 0)) (mul_pos (sub_pos.mpr ha.2) (hr 2))
    (mul_pos hc.1 (hr 0)) (mul_pos (sub_pos.mpr hc.2) (hr 1)) hz
  let x : ℝ × ℝ := (z.1 + widths C 0 * α + widths C 2 * γ,
    z.2 + widths C 1 * β + widths C 2 * (1 - γ))
  have hdot : ∀ i, dot (C.plank i).u x = (C.plank i).lo +
      widths C i * ![α, β, γ] i := by
    intro i
    fin_cases i
    · change dot (C.plank 0).u x = (C.plank 0).lo + widths C 0 * α
      rw [hu₀]
      dsimp [x, dot]
      simp only [threshold, base, hu₀, dot, Prod.fst_add, Prod.snd_add] at h0
      nlinarith only [h0]
    · change dot (C.plank 1).u x = (C.plank 1).lo + widths C 1 * β
      rw [hu₁]
      dsimp [x, dot]
      simp only [threshold, base, hu₁, dot, Prod.fst_add, Prod.snd_add] at h1
      nlinarith only [h1]
    · change dot (C.plank 2).u x = (C.plank 2).lo + widths C 2 * γ
      rw [hu₂]
      dsimp [x, dot]
      simp only [threshold, base, hu₂, dot, Prod.fst_add, Prod.snd_add] at h2
      nlinarith only [h2]
  refine ⟨x, ?_, ?_, ?_⟩
  · change 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ C.deficit at hzT
    have hdef := deficit_eq C hb ha hc hu₀ hu₁ hu₂
    dsimp [x]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith only [hzT.1, mul_pos (hr 0) hα.1, mul_pos (hr 2) hγ.1]
    · nlinarith only [hzT.2.1, mul_pos (hr 1) hβ.1,
        mul_pos (hr 2) (sub_pos.mpr hγ.2)]
    · nlinarith only [hzT.2.2, hdef, mul_pos (hr 0) (sub_pos.mpr hα.2),
        mul_pos (hr 1) (sub_pos.mpr hβ.2)]
  · intro i
    rw [hdot]
    have hσ : 0 < ![α, β, γ] i ∧ ![α, β, γ] i < 1 := by
      fin_cases i
      · exact hα
      · exact hβ
      · exact hγ
    have hwidth : (C.plank i).hi = (C.plank i).lo + widths C i := by
      dsimp [widths]
      ring
    rw [hwidth]
    constructor
    · linarith [mul_pos (hr i) hσ.1]
    · nlinarith only [mul_pos (hr i) (sub_pos.mpr hσ.2)]
  · have hd0 := hdot 0
    have hd1 := hdot 1
    have hd2 := hdot 2
    simp only [hu₀, hu₁, hu₂, dot, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Fin.isValue] at hd0 hd1 hd2
    have hhi : (C.plank 2).hi = (C.plank 2).lo + widths C 2 := by
      dsimp [widths]
      ring
    apply Prod.ext
    · change (C.plank 0).lo + (C.plank 2).lo - c * x.1 +
        (1 - b - c) * x.2 = z.1
      dsimp [x] at hd0 hd2 ⊢
      linear_combination -hd0 - hd2
    · change (C.plank 1).lo - (C.plank 2).hi + (c - a) * x.1 +
        (c - 1) * x.2 = z.2
      rw [hhi]
      dsimp [x] at hd1 hd2 ⊢
      linear_combination -hd1 + hd2

/-- An obstructed deficit seed constructs a point strictly inside the
triangle and strictly between the boundaries of every actual plank. -/
theorem exists_strict_common_point_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) {z : ℝ × ℝ}
    (hzT : z ∈ RowDeletion.triangle C.deficit) (hz : z ∈ badSeeds C b a c) :
    ∃ x : ℝ × ℝ, (0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1) ∧
      ∀ i, (C.plank i).lo < dot (C.plank i).u x ∧ dot (C.plank i).u x < (C.plank i).hi := by
  obtain ⟨x, hxT, hxP, _⟩ :=
    exists_strict_common_point_with_seed_of_bad C hb ha hc hu₀ hu₁ hu₂ hzT hz
  exact ⟨x, hxT, hxP⟩

/-- The actual quantitative bound holds whenever the three planks have
no common point strictly inside the triangle and all six boundaries. -/
theorem sqPos_of_no_strict_common_point (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hn : ¬ ∃ x : ℝ × ℝ, (0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1) ∧
      ∀ i, (C.plank i).lo < dot (C.plank i).u x ∧ dot (C.plank i).u x < (C.plank i).hi) :
    Quant.SqPos C := by
  apply sqPos_of_no_bad_seed C hb ha hc hu₀ hu₁ hu₂
  intro z hzT hz
  exact hn (exists_strict_common_point_of_bad C hb ha hc hu₀ hu₁ hu₂ hzT hz)

def commonInterior (C : Config) : Set (ℝ × ℝ) :=
  {x | (0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1) ∧
    ∀ i, (C.plank i).lo < dot (C.plank i).u x ∧ dot (C.plank i).u x < (C.plank i).hi}

def tripleOverlapSet (C : Config) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ ⋂ i, (C.plank i).set

theorem isOpen_commonInterior (C : Config) : IsOpen (commonInterior C) := by
  have hT : IsOpen {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2 ∧ x.1 + x.2 < 1} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hP : IsOpen {x : ℝ × ℝ | ∀ i,
      (C.plank i).lo < dot (C.plank i).u x ∧ dot (C.plank i).u x < (C.plank i).hi} := by
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    exact (Proofs.GapCells.isOpen_lt_dot _ _).inter (Proofs.GapCells.isOpen_dot_lt _ _)
  exact hT.inter hP

theorem commonInterior_subset_tripleOverlap (C : Config) :
    commonInterior C ⊆ tripleOverlapSet C := by
  intro x hx
  refine ⟨?_, ?_⟩
  · rw [Proofs.Quant.stdTriangle_set_eq]
    exact ⟨hx.1.1.le, hx.1.2.1.le, hx.1.2.2.le⟩
  · apply mem_iInter.mpr
    intro i
    exact ⟨(hx.2 i).1.le, (hx.2 i).2.le⟩

theorem tripleOverlap_pos_of_bad (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) {z : ℝ × ℝ}
    (hzT : z ∈ RowDeletion.triangle C.deficit) (hz : z ∈ badSeeds C b a c) :
    0 < volume (tripleOverlapSet C) := by
  have hne : (commonInterior C).Nonempty :=
    exists_strict_common_point_of_bad C hb ha hc hu₀ hu₁ hu₂ hzT hz
  exact ((isOpen_commonInterior C).measure_pos volume hne).trans_le
    (measure_mono (commonInterior_subset_tripleOverlap C))

/-- This applies to the actual closed-plank overlap, including boundary
contacts and zero widths. A positive-area triple overlap is necessary
for any configuration left by the cyclic localization. -/
theorem sqPos_of_tripleOverlap_zero (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hzero : volume (tripleOverlapSet C) = 0) : Quant.SqPos C := by
  apply sqPos_of_no_bad_seed C hb ha hc hu₀ hu₁ hu₂
  intro z hzT hz
  have hpos := tripleOverlap_pos_of_bad C hb ha hc hu₀ hu₁ hu₂ hzT hz
  rw [hzero] at hpos
  exact (lt_irrefl _ hpos)

theorem positive_part_of_tripleOverlap_zero (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hzero : volume (tripleOverlapSet C) = 0) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  have h := sqPos_of_tripleOverlap_zero C hb ha hc hu₀ hu₁ hu₂ hzero
  change (max 0 C.deficit) ^ 2 * (1 / 2) ≤ C.gapArea at h
  linarith

def TripleNullOrbit (C : Config) : Prop :=
  ∃ (b a c : ℝ) (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1)
    (hc : 0 < c ∧ c < 1) (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i),
    volume (tripleOverlapSet (abcConfig b a c hb ha hc lo hi hle)) = 0 ∧
    C.Equiv (abcConfig b a c hb ha hc lo hi hle)

theorem moveOrbit_sqPos (C : Config) (h : TripleNullOrbit C) : Quant.SqPos C := by
  obtain ⟨b, a, c, hb, ha, hc, lo, hi, hle, hzero, he⟩ := h
  have hD := sqPos_of_tripleOverlap_zero
    (abcConfig b a c hb ha hc lo hi hle) hb ha hc rfl rfl rfl hzero
  simp only [Quant.SqPos, Config.deficit] at hD ⊢
  rw [he.sumRelW_eq, he.gapArea_eq]
  exact hD

end Quant.CyclicGeometry
