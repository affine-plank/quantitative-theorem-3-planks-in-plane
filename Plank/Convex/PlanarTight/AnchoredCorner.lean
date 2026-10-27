/- A band corner surviving contraction beyond an anchored plank must lie
on a support line of the entire body, together with the contraction center. -/
module
public import Plank.Convex.ConvexCellSeparation
public import Mathlib.Tactic.LinearCombination
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredCorner

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem map_contract (f : E →ᵃ[ℝ] ℝ) (T C : E) (r : ℝ) :
    f (r • T + (1 - r) • C) = r * f T + (1 - r) * f C := by
  rw [AffineMap.decomp]
  simp only [Pi.add_apply, map_add, map_smul, smul_eq_mul]
  ring

/-- If the contracted intersection of two band boundaries is beyond the
anchored plank, separation gives a supporting combination of those boundaries
which vanishes at both the original corner and the contraction center. -/
theorem support (K : Set E) (hK : Convex ℝ K) (X g h : E →ᵃ[ℝ] ℝ)
    (T C : E) (hT : T ∈ K) (hC : C ∈ K) (hXT : X T = 1)
    (hXC : 0 < X C) (hgC : g C = 0) (hhC : h C = 0)
    (r : ℝ) (hr : 0 < r) (hr₁ : r < 1)
    (hempty : ¬ ∃ z ∈ K, r < X z ∧ r * g T < g z ∧ r * h T < h z) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧
      a * g T + b * h T = 0 ∧ ∀ z ∈ K, a * g z + b * h z ≤ 0 := by
  let cuts : Fin 3 → E →ᵃ[ℝ] ℝ := ![
    X - AffineMap.const ℝ E r,
    g - AffineMap.const ℝ E (r * g T),
    h - AffineMap.const ℝ E (r * h T)]
  obtain ⟨m, hm, hsum, hrows⟩ := ConvexCellSeparation.exists_weights K hK cuts (by
    rintro ⟨z, hz, hc⟩
    exact hempty ⟨z, hz, sub_pos.mp (hc 0), sub_pos.mp (hc 1), sub_pos.mp (hc 2)⟩)
  have hrow (z : E) (hz : z ∈ K) :
      m 0 * (X z - r) + m 1 * (g z - r * g T) + m 2 * (h z - r * h T) ≤ 0 := by
    simpa [Fin.sum_univ_three, cuts, AffineMap.coe_sub] using hrows z hz
  let Q := r • T + (1 - r) • C
  have hs : 0 < 1 - r := sub_pos.mpr hr₁
  have hQ : Q ∈ K := hK hT hC hr.le hs.le (by ring)
  have hqrow := hrow Q hQ
  have hqX : X Q = r + (1 - r) * X C := by
    rw [map_contract, hXT, mul_one]
  have hqg : g Q = r * g T := by rw [map_contract, hgC, mul_zero, add_zero]
  have hqh : h Q = r * h T := by rw [map_contract, hhC, mul_zero, add_zero]
  rw [hqX, hqg, hqh] at hqrow
  have hprod : m 0 * ((1 - r) * X C) ≤ 0 := by nlinarith only [hqrow]
  have hm0 : m 0 = 0 :=
    (mul_eq_zero.mp (le_antisymm hprod (mul_nonneg (hm 0) (mul_pos hs hXC).le))).resolve_right
      (mul_pos hs hXC).ne'
  have hrow' (z : E) (hz : z ∈ K) :
      m 1 * (g z - r * g T) + m 2 * (h z - r * h T) ≤ 0 := by
    simpa only [hm0, zero_mul, zero_add] using hrow z hz
  have ht := hrow' T hT
  have hc := hrow' C hC
  rw [hgC, hhC] at hc
  have hvlo : 0 ≤ r * (m 1 * g T + m 2 * h T) := by nlinarith only [hc]
  have hvhi : (1 - r) * (m 1 * g T + m 2 * h T) ≤ 0 := by nlinarith only [ht]
  have hv : m 1 * g T + m 2 * h T = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right hvhi hs) (nonneg_of_mul_nonneg_right hvlo hr)
  refine ⟨m 1, m 2, hm 1, hm 2, ?_, hv, ?_⟩
  · simpa only [Fin.sum_univ_three, hm0, zero_add] using hsum
  · intro z hz
    have hzrow := hrow' z hz
    have hrv : r * (m 1 * g T + m 2 * h T) = 0 := by rw [hv, mul_zero]
    nlinarith only [hzrow, hrv]

/-- A contracted corner on the open edge between `(0,p)` and `(q,0)`
forces the contraction center onto the same edge line, provided that the
corner is outside the zero support face of the anchored coordinate. -/
theorem on_edge (K : Set E) (hK : Convex ℝ K) (X Y Z : E →ᵃ[ℝ] ℝ)
    (T A B : E) (hT : T ∈ K) (hA : A ∈ K) (hB : B ∈ K) (hXT : X T = 1)
    (p q t r : ℝ) (hp : 0 < p)
    (ht : 0 < t) (ht₁ : t < 1) (hr : 0 < r) (hr₁ : r < 1)
    (hYA : Y A = 0) (hZA : Z A = p) (hYB : Y B = q) (hZB : Z B = 0)
    (hXC : 0 < X (t • A + (1 - t) • B))
    (hempty : ¬ ∃ z ∈ K, r < X z ∧
      Y z < r * Y T + (1 - r) * ((1 - t) * q) ∧
      Z z < r * Z T + (1 - r) * (t * p)) :
    p * Y T + q * Z T = p * q := by
  let C := t • A + (1 - t) • B
  let g : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E ((1 - t) * q) - Y
  let h : E →ᵃ[ℝ] ℝ := AffineMap.const ℝ E (t * p) - Z
  have hg (z : E) : g z = (1 - t) * q - Y z := by simp [g, AffineMap.coe_sub]
  have hh (z : E) : h z = t * p - Z z := by simp [h, AffineMap.coe_sub]
  have hC : C ∈ K := hK hA hB ht.le (sub_pos.mpr ht₁).le (by ring)
  have hgC : g C = 0 := by rw [hg, map_contract, hYA, hYB]; ring
  have hhC : h C = 0 := by rw [hh, map_contract, hZA, hZB]; ring
  obtain ⟨a, b, ha, hb, hab, hzero, hrow⟩ :=
    support K hK X g h T C hT hC hXT hXC hgC hhC r hr hr₁ (by
      rintro ⟨z, hz, hx, hy, hz'⟩
      rw [hg, hg] at hy
      rw [hh, hh] at hz'
      exact hempty ⟨z, hz, hx, by nlinarith only [hy], by nlinarith only [hz']⟩)
  have hrowA := hrow A hA
  have hrowB := hrow B hB
  rw [hg, hh, hYA, hZA] at hrowA
  rw [hg, hh, hYB, hZB] at hrowB
  have he₀ : (1 - t) * (a * q - b * p) ≤ 0 := by nlinarith only [hrowA]
  have he₁ : t * (b * p - a * q) ≤ 0 := by nlinarith only [hrowB]
  have he₀' := nonpos_of_mul_nonpos_right he₀ (sub_pos.mpr ht₁)
  have he₁' := nonpos_of_mul_nonpos_right he₁ ht
  have heq : a * q = b * p := by linarith only [he₀', he₁']
  have ha' : 0 < a := by
    by_contra hn
    have haz : a = 0 := le_antisymm (le_of_not_gt hn) ha
    have hbz : b = 0 := (mul_eq_zero.mp (by simpa only [haz, zero_mul] using heq.symm)).resolve_right hp.ne'
    linarith only [hab, haz, hbz]
  rw [hg, hh] at hzero
  have hprod : a * (p * q - (p * Y T + q * Z T)) = 0 := by
    linear_combination p * hzero + (t * p - Z T) * heq
  have hz := (mul_eq_zero.mp hprod).resolve_left ha'.ne'
  linarith only [hz]

end Plank.Convex.PlanarTight.AnchoredCorner

/-- info: 'Plank.Convex.PlanarTight.AnchoredCorner.support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredCorner.support

/-- info: 'Plank.Convex.PlanarTight.AnchoredCorner.on_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredCorner.on_edge
