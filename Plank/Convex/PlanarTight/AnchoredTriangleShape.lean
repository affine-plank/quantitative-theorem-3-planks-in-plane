/- A triangular two-coordinate enclosure with an interior apex
parameter is the whole triangle once all coordinate extrema are attained. -/
module
public import Plank.Convex.PlanarTight.TwoPlankClassification
public import Plank.Convex.PlanarTight.TriangleSupportShape
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredTriangleShape

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The three vertices of a triangular enclosure are actual body points
when its apex parameter is strictly between zero and one. -/
theorem contacts (K : Set E) (X Y : E →ᵃ[ℝ] ℝ)
    (H : TwoPlankClassification.Ranges K X Y)
    (c : ℝ) (hc : 0 < c) (hc₁ : c < 1)
    (hshape : ∀ z ∈ K, c * X z ≤ Y z ∧ Y z ≤ 1 - (1 - c) * X z) :
    (∃ A ∈ K, X A = 0 ∧ Y A = 0) ∧
    (∃ B ∈ K, X B = 0 ∧ Y B = 1) ∧
    (∃ C ∈ K, X C = 1 ∧ Y C = c) := by
  obtain ⟨A, hA, hYA⟩ := H.minY
  obtain ⟨B, hB, hYB⟩ := H.maxY
  obtain ⟨C, hC, hXC⟩ := H.maxX
  have hXA : X A = 0 := by
    have hs := (hshape A hA).1
    rw [hYA] at hs
    have hx := (H.box A hA).1.1
    nlinarith only [hs, hx, hc]
  have hXB : X B = 0 := by
    have hs := (hshape B hB).2
    rw [hYB] at hs
    have hx := (H.box B hB).1.1
    nlinarith only [hs, hx, hc₁]
  have hYC : Y C = c := by
    have hs := hshape C hC
    rw [hXC] at hs
    linarith only [hs.1, hs.2]
  exact ⟨⟨A, hA, hXA, hYA⟩, ⟨B, hB, hXB, hYB⟩, ⟨C, hC, hXC, hYC⟩⟩

/-- The enclosure equals its triangle. Injectivity is needed only on K,
so the result also applies to a body in a plane inside a larger space. -/
theorem eq_triangle (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (H : TwoPlankClassification.Ranges K X Y)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, X x = X y → Y x = Y y → x = y)
    (c : ℝ) (hc : 0 < c) (hc₁ : c < 1)
    (hshape : ∀ z ∈ K, c * X z ≤ Y z ∧ Y z ≤ 1 - (1 - c) * X z) :
    ∃ v : Fin 3 → E, (∀ i, v i ∈ K) ∧
      X (v 0) = 0 ∧ Y (v 0) = 0 ∧ X (v 1) = 0 ∧ Y (v 1) = 1 ∧
      X (v 2) = 1 ∧ Y (v 2) = c ∧
      AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v) := by
  obtain ⟨⟨A, hA, hXA, hYA⟩, ⟨B, hB, hXB, hYB⟩, ⟨C, hC, hXC, hYC⟩⟩ :=
    contacts K X Y H c hc hc₁ hshape
  let v : Fin 3 → E := ![A, B, C]
  have hv : ∀ i, v i ∈ K := by intro i; fin_cases i <;> assumption
  let f : Fin 3 → E →ᵃ[ℝ] ℝ := ![TwoPlankClassification.reflect Y, Y, X]
  have hdiag : ∀ i, f i (v i) = 1 := by
    intro i
    fin_cases i <;> simp [f, v, hYA, hYB, hXC]
  have hoff : ∀ i j, j ≠ i → f i (v j) < 1 := by
    intro i j hji
    fin_cases i <;> fin_cases j <;>
      simp_all [f, v]
  have hind := TriangleSupportShape.independent_of_strict_maxima v f hdiag hoff
  have hsub : convexHull ℝ (Set.range v) ⊆ K :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hv i) hK
  refine ⟨v, hv, hXA, hYA, hXB, hYB, hXC, hYC, hind, ?_⟩
  apply Set.Subset.antisymm _ hsub
  intro x hx
  let w : Fin 3 → ℝ := ![1 - Y x - (1 - c) * X x, Y x - c * X x, X x]
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    have hs := hshape x hx
    fin_cases i
    · dsimp [w]
      linarith only [hs.2]
    · exact sub_nonneg.mpr hs.1
    · exact (H.box x hx).1.1
  have hsum : ∑ i, w i = 1 := by simp [Fin.sum_univ_three, w]; ring
  let y : E := ∑ i, w i • v i
  have hy : y ∈ convexHull ℝ (Set.range v) :=
    mem_convexHull_of_exists_fintype w v hw hsum (fun i => ⟨i, rfl⟩) rfl
  have hXy : X y = X x := by
    rw [Plank.Body.map_comb X w v hsum]
    simp [Fin.sum_univ_three, w, v, hXA, hXB, hXC]
  have hYy : Y y = Y x := by
    rw [Plank.Body.map_comb Y w v hsum]
    simp [Fin.sum_univ_three, w, v, hYA, hYB, hYC]
    ring
  have heq := hinj x hx y (hsub hy) hXy.symm hYy.symm
  exact heq.symm ▸ hy

end Plank.Convex.PlanarTight.AnchoredTriangleShape

/-- info: 'Plank.Convex.PlanarTight.AnchoredTriangleShape.contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredTriangleShape.contacts

/-- info: 'Plank.Convex.PlanarTight.AnchoredTriangleShape.eq_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredTriangleShape.eq_triangle
