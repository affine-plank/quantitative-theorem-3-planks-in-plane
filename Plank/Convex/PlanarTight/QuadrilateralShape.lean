/- The quadrilateral enclosure in the internal two-plank classification is
exact whenever its two coordinates identify the planar body. -/
module
public import Plank.Convex.PlanarTight.TwoPlankClassification
public import Mathlib.Analysis.Convex.Combination
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.QuadrilateralShape

open TwoPlankQuadrilateral

theorem at_left (y q p : ℝ) (hq : 0 < q)
    (h : InQuadrilateral 0 y q p) : y = p := by
  obtain ⟨h₀, _, h₂, _⟩ := h
  have hlow : 0 ≤ q * (y - p) := by nlinarith only [h₀]
  have hupp : 0 ≤ q * (p - y) := by nlinarith only [h₂]
  have := nonneg_of_mul_nonneg_right hlow hq
  have := nonneg_of_mul_nonneg_right hupp hq
  linarith

theorem at_right (y q p : ℝ) (hq₁ : q < 1)
    (h : InQuadrilateral 1 y q p) : y = p := by
  obtain ⟨_, h₁, _, h₃⟩ := h
  have hlow : 0 ≤ (1 - q) * (y - p) := by nlinarith only [h₁]
  have hupp : 0 ≤ (1 - q) * (p - y) := by nlinarith only [h₃]
  have := nonneg_of_mul_nonneg_right hlow (sub_pos.mpr hq₁)
  have := nonneg_of_mul_nonneg_right hupp (sub_pos.mpr hq₁)
  linarith

theorem at_bottom (x q p : ℝ) (hp : 0 < p)
    (h : InQuadrilateral x 0 q p) : x = q := by
  obtain ⟨h₀, h₁, _, _⟩ := h
  have hlow : 0 ≤ p * (x - q) := by nlinarith only [h₀]
  have hupp : 0 ≤ p * (q - x) := by nlinarith only [h₁]
  have := nonneg_of_mul_nonneg_right hlow hp
  have := nonneg_of_mul_nonneg_right hupp hp
  linarith

theorem at_top (x q p : ℝ) (hp₁ : p < 1)
    (h : InQuadrilateral x 1 q p) : x = q := by
  obtain ⟨_, _, h₂, h₃⟩ := h
  have hlow : 0 ≤ (1 - p) * (x - q) := by nlinarith only [h₂]
  have hupp : 0 ≤ (1 - p) * (q - x) := by nlinarith only [h₃]
  have := nonneg_of_mul_nonneg_right hlow (sub_pos.mpr hp₁)
  have := nonneg_of_mul_nonneg_right hupp (sub_pos.mpr hp₁)
  linarith

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Attained coordinate extrema in the enclosure are its four vertices. -/
theorem contacts (K : Set E) (X Y : E →ᵃ[ℝ] ℝ)
    (H : TwoPlankClassification.Ranges K X Y) (q p : ℝ)
    (hq : 0 < q) (hq₁ : q < 1) (hp : 0 < p) (hp₁ : p < 1)
    (hshape : ∀ z ∈ K, InQuadrilateral (X z) (Y z) q p) :
    (∃ L ∈ K, X L = 0 ∧ Y L = p) ∧
    (∃ R ∈ K, X R = 1 ∧ Y R = p) ∧
    (∃ B ∈ K, X B = q ∧ Y B = 0) ∧
    (∃ T ∈ K, X T = q ∧ Y T = 1) := by
  obtain ⟨L, hL, hXL⟩ := H.minX
  obtain ⟨R, hR, hXR⟩ := H.maxX
  obtain ⟨B, hB, hYB⟩ := H.minY
  obtain ⟨T, hT, hYT⟩ := H.maxY
  refine ⟨⟨L, hL, hXL, ?_⟩, ⟨R, hR, hXR, ?_⟩,
    ⟨B, hB, ?_, hYB⟩, ⟨T, hT, ?_, hYT⟩⟩
  · exact at_left _ q p hq (by simpa only [hXL] using hshape L hL)
  · exact at_right _ q p hq₁ (by simpa only [hXR] using hshape R hR)
  · exact at_bottom _ q p hp (by simpa only [hYB] using hshape B hB)
  · exact at_top _ q p hp₁ (by simpa only [hYT] using hshape T hT)

abbrev Point := Fin 2 → ℝ

/-- The four vertices, in left, bottom, right, top order. -/
def vertices (q p : ℝ) : Fin 4 → Point := ![![0, p], ![q, 0], ![1, p], ![q, 1]]

/-- Explicit barycentric coordinates in one of the two triangles obtained
by dividing the quadrilateral along its horizontal diagonal. -/
theorem mem_convexHull (z : Point) (q p : ℝ) (hp : 0 < p) (hp₁ : p < 1)
    (h : InQuadrilateral (z 0) (z 1) q p) :
    z ∈ convexHull ℝ (Set.range (vertices q p)) := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  by_cases hy : z 1 ≤ p
  · let w : Fin 4 → ℝ := ![
      ((1 - q) * z 1 - p * z 0 + p * q) / p,
      (p - z 1) / p,
      (p * z 0 + q * z 1 - p * q) / p, 0]
    apply mem_convexHull_of_exists_fintype w (vertices q p)
    · intro i
      fin_cases i
      · exact div_nonneg (by nlinarith only [h₁]) hp.le
      · exact div_nonneg (sub_nonneg.mpr hy) hp.le
      · exact div_nonneg (by nlinarith only [h₀]) hp.le
      · exact le_rfl
    · dsimp [w]
      rw [Fin.sum_univ_four]
      dsimp
      field_simp
      ring
    · exact fun i => ⟨i, rfl⟩
    · ext i
      fin_cases i <;> simp [Fin.sum_univ_four, w, vertices]
      all_goals field_simp
      all_goals ring
  · have hd : 0 < 1 - p := sub_pos.mpr hp₁
    let w : Fin 4 → ℝ := ![
      ((1 - q) * (1 - z 1) - (1 - p) * z 0 + (1 - p) * q) / (1 - p), 0,
      ((1 - p) * z 0 + q * (1 - z 1) - (1 - p) * q) / (1 - p),
      (z 1 - p) / (1 - p)]
    apply mem_convexHull_of_exists_fintype w (vertices q p)
    · intro i
      fin_cases i
      · exact div_nonneg (by nlinarith only [h₃]) hd.le
      · exact le_rfl
      · exact div_nonneg (by nlinarith only [h₂]) hd.le
      · exact div_nonneg (by linarith only [hy]) hd.le
    · dsimp [w]
      rw [Fin.sum_univ_four]
      dsimp
      field_simp
      ring
    · exact fun i => ⟨i, rfl⟩
    · ext i
      fin_cases i <;> simp [Fin.sum_univ_four, w, vertices]
      all_goals field_simp
      all_goals ring

/-- A planar convex body with attained unit coordinate ranges and this
quadrilateral enclosure is exactly the convex hull of the four vertices. -/
theorem eq_convexHull (K : Set Point) (hK : Convex ℝ K)
    (H : TwoPlankClassification.Ranges K (AffineMap.proj 0) (AffineMap.proj 1))
    (q p : ℝ) (hq : 0 < q) (hq₁ : q < 1) (hp : 0 < p) (hp₁ : p < 1)
    (hshape : ∀ z ∈ K, InQuadrilateral (z 0) (z 1) q p) :
    K = convexHull ℝ (Set.range (vertices q p)) := by
  apply Set.Subset.antisymm
  · exact fun z hz => mem_convexHull z q p hp hp₁ (hshape z hz)
  · apply convexHull_min _ hK
    obtain ⟨⟨L, hL, hXL, hYL⟩, ⟨R, hR, hXR, hYR⟩,
      ⟨B, hB, hXB, hYB⟩, ⟨T, hT, hXT, hYT⟩⟩ :=
      contacts K _ _ H q p hq hq₁ hp hp₁ hshape
    have hLeq : L = vertices q p 0 := by ext i; fin_cases i <;> assumption
    have hBeq : B = vertices q p 1 := by ext i; fin_cases i <;> assumption
    have hReq : R = vertices q p 2 := by ext i; fin_cases i <;> assumption
    have hTeq : T = vertices q p 3 := by ext i; fin_cases i <;> assumption
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact hLeq ▸ hL
    · exact hBeq ▸ hB
    · exact hReq ▸ hR
    · exact hTeq ▸ hT

end Plank.Convex.PlanarTight.QuadrilateralShape

/-- info: 'Plank.Convex.PlanarTight.QuadrilateralShape.contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.QuadrilateralShape.contacts

/-- info: 'Plank.Convex.PlanarTight.QuadrilateralShape.eq_convexHull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.QuadrilateralShape.eq_convexHull
