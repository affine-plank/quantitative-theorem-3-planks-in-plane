/- A missing cell along a contracted edge forces the corresponding
perspective inequality; two such inequalities identify the whole triangle. -/
module
public import Plank.Convex.PlanarTight.AnchoredCorner
public import Plank.Convex.PlanarTight.AnchoredShape
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.PerspectiveTriangle

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A strict third cut at an interior point of AB removes its separator
weight and forces the supporting line through A and B. -/
theorem lower_support (K : Set E) (hK : Convex ℝ K) (X Y Z : E →ᵃ[ℝ] ℝ)
    (A B : E) (hA : A ∈ K) (hB : B ∈ K) (u r s : ℝ)
    (hXA : X A = 1) (hXB : X B = 0) (hYA : Y A = u) (hYB : Y B = 0)
    (hr : 0 < r) (hr₁ : r < 1)
    (hgap : s < r * Z A + (1 - r) * Z B)
    (hempty : ¬ ∃ z ∈ K, r < X z ∧ Y z < r * u ∧ s < Z z) :
    ∀ z ∈ K, u * X z ≤ Y z := by
  let cuts : Fin 3 → E →ᵃ[ℝ] ℝ := ![
    X - AffineMap.const ℝ E r,
    AffineMap.const ℝ E (r * u) - Y,
    Z - AffineMap.const ℝ E s]
  obtain ⟨m, hm, hsum, hrows⟩ := ConvexCellSeparation.exists_weights K hK cuts (by
    rintro ⟨z, hz, hc⟩
    exact hempty ⟨z, hz, sub_pos.mp (hc 0), sub_pos.mp (hc 1), sub_pos.mp (hc 2)⟩)
  have hrow (z : E) (hz : z ∈ K) :
      m 0 * (X z - r) + m 1 * (r * u - Y z) + m 2 * (Z z - s) ≤ 0 := by
    simpa [Fin.sum_univ_three, cuts, AffineMap.coe_sub] using hrows z hz
  let Q := r • A + (1 - r) • B
  have hQ : Q ∈ K := hK hA hB hr.le (sub_pos.mpr hr₁).le (by ring)
  have hXQ : X Q = r := by rw [AnchoredCorner.map_contract, hXA, hXB]; ring
  have hYQ : Y Q = r * u := by rw [AnchoredCorner.map_contract, hYA, hYB]; ring
  have hZQ : s < Z Q := by
    change s < Z (r • A + (1 - r) • B)
    rw [AnchoredCorner.map_contract]
    exact hgap
  have hq := hrow Q hQ
  rw [hXQ, hYQ] at hq
  have hp : m 2 * (Z Q - s) ≤ 0 := by simpa only [sub_self, mul_zero, zero_add] using hq
  have hm₂ : m 2 = 0 := le_antisymm
    (nonpos_of_mul_nonpos_left hp (sub_pos.mpr hZQ)) (hm 2)
  have hrow' (z : E) (hz : z ∈ K) : m 0 * (X z - r) + m 1 * (r * u - Y z) ≤ 0 := by
    simpa only [hm₂, zero_mul, add_zero] using hrow z hz
  have h₀ := hrow' A hA
  have h₁ := hrow' B hB
  rw [hXA, hYA] at h₀
  rw [hXB, hYB] at h₁
  have heq : m 0 = m 1 * u := by
    have hle : (1 - r) * (m 0 - m 1 * u) ≤ 0 := by nlinarith only [h₀]
    have hge : r * (m 1 * u - m 0) ≤ 0 := by nlinarith only [h₁]
    have hle' := nonpos_of_mul_nonpos_right hle (sub_pos.mpr hr₁)
    have hge' := nonpos_of_mul_nonpos_right hge hr
    linarith only [hle', hge']
  have hm₁ : 0 < m 1 := by
    apply lt_of_le_of_ne (hm 1)
    intro he
    rw [Fin.sum_univ_three, hm₂, heq, ← he, zero_mul] at hsum
    norm_num at hsum
  intro z hz
  have hzrow := hrow' z hz
  rw [heq] at hzrow
  have hp' : m 1 * (u * X z - Y z) ≤ 0 := by nlinarith only [hzrow]
  exact sub_nonpos.mp (nonpos_of_mul_nonpos_right hp' hm₁)

abbrev Point := Fin 3 → ℝ

/-- An apex and the two opposite unit-coordinate contacts, together with
the two perspective bounds, identify the body as their triangle. -/
theorem eq_triangle (K : Set Point) (hK : Convex ℝ K)
    (hbox₀ : ∀ z ∈ K, 0 ≤ z 0)
    (a b c d : ℝ) (hb : 0 < b)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (T R U : Point) (hT : T ∈ K) (hR : R ∈ K) (hU : U ∈ K)
    (hT₀ : T 0 = 1) (hR₀ : R 0 = 0) (hR₁ : R 1 = 1) (hR₂ : R 2 = 0)
    (hU₀ : U 0 = 0) (hU₁ : U 1 = 0) (hU₂ : U 2 = 1)
    (hY : ∀ z ∈ K, T 1 * z 0 ≤ z 1) (hZ : ∀ z ∈ K, T 2 * z 0 ≤ z 2) :
    AnchoredShape.IsTriangle K := by
  have hpR := hplane R hR
  have hpU := hplane U hU
  rw [hR₀, hR₁, hR₂] at hpR
  rw [hU₀, hU₁, hU₂] at hpU
  have hd : d = b := by linarith only [hpR]
  have hc : c = b := by linarith only [hpR, hpU]
  have hpT := hplane T hT
  rw [hT₀, hc, hd] at hpT
  let v : Fin 3 → Point := ![T, R, U]
  have hv : ∀ i, v i ∈ K := by intro i; fin_cases i <;> assumption
  let f : Fin 3 → Point →ᵃ[ℝ] ℝ := ![
    AffineMap.proj 0,
    AffineMap.proj 1 - T 1 • AffineMap.proj 0,
    AffineMap.proj 2 - T 2 • AffineMap.proj 0]
  have hdiag : ∀ i, f i (v i) = 1 := by
    intro i
    fin_cases i <;> simp [f, v, AffineMap.coe_sub, AffineMap.coe_smul,
      hT₀, hR₀, hR₁, hU₀, hU₂]
  have hoff : ∀ i j, j ≠ i → f i (v j) < 1 := by
    intro i j hji
    fin_cases i <;> fin_cases j <;> simp_all [f, v, AffineMap.coe_sub, AffineMap.coe_smul]
  have hind := TriangleSupportShape.independent_of_strict_maxima v f hdiag hoff
  have hsub : convexHull ℝ (Set.range v) ⊆ K :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hv i) hK
  refine ⟨v, hind, Set.Subset.antisymm ?_ hsub⟩
  intro z hz
  let w : Fin 3 → ℝ := ![z 0, z 1 - T 1 * z 0, z 2 - T 2 * z 0]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    fin_cases i
    · exact hbox₀ z hz
    · exact sub_nonneg.mpr (hY z hz)
    · exact sub_nonneg.mpr (hZ z hz)
  have hs : ∑ i, w i = 1 := by
    have hpz := hplane z hz
    rw [hc, hd] at hpz
    have he : b * (z 0 + (z 1 - T 1 * z 0) + (z 2 - T 2 * z 0) - 1) = 0 := by
      linear_combination hpz - z 0 * hpT
    have he' := (mul_eq_zero.mp he).resolve_left hb.ne'
    rw [Fin.sum_univ_three]
    change z 0 + (z 1 - T 1 * z 0) + (z 2 - T 2 * z 0) = 1
    linarith only [he']
  apply mem_convexHull_of_exists_fintype w v
  · exact hw
  · exact hs
  · exact fun i => ⟨i, rfl⟩
  · ext i
    fin_cases i <;> simp [Fin.sum_univ_three, w, v, hT₀, hR₀, hR₁, hR₂, hU₀, hU₁, hU₂] <;> ring

end Plank.Convex.PlanarTight.PerspectiveTriangle

/-- info: 'Plank.Convex.PlanarTight.PerspectiveTriangle.lower_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.PerspectiveTriangle.lower_support

/-- info: 'Plank.Convex.PlanarTight.PerspectiveTriangle.eq_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.PerspectiveTriangle.eq_triangle
