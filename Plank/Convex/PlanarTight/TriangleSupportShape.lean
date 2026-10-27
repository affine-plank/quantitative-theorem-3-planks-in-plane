/- Three strict directional maximizers and their opposite support lines
identify the whole planar convex body as their triangle. -/
module
public import Plank.Proofs.AffineEvaluation
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.TriangleSupportShape

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Three points which are distinct strict maximizers of three affine
coordinates cannot be collinear. -/
theorem independent_of_strict_maxima (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hdiag : ∀ i, f i (v i) = 1) (hoff : ∀ i j, j ≠ i → f i (v j) < 1) :
    AffineIndependent ℝ v := by
  have hnot (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) :
      ¬ Wbtw ℝ (v j) (v i) (v k) := by
    intro h
    have hmem := (convex_Iio (𝕜 := ℝ) (1 : ℝ)).mem_of_wbtw (h.map (f i))
      (hoff i j hji) (hoff i k hki)
    simp only [Set.mem_Iio, hdiag i, lt_self_iff_false] at hmem
  apply affineIndependent_iff_not_collinear.mpr
  intro hcol
  have hset : Set.range v = ({v 0, v 1, v 2} : Set E) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Set.mem_range_self 0
      · exact Set.mem_range_self 1
      · exact Set.mem_range_self 2
  have hcol' : Collinear ℝ ({v 0, v 1, v 2} : Set E) := hset ▸ hcol
  rcases hcol'.wbtw_or_wbtw_or_wbtw with h | h | h
  · exact hnot 1 0 2 (by decide) (by decide) h
  · exact hnot 2 1 0 (by decide) (by decide) h
  · exact hnot 0 2 1 (by decide) (by decide) h

variable [FiniteDimensional ℝ E]

/-- Three nonzero supporting affine forms, each vanishing on the opposite
two vertices, describe exactly the triangle spanned by an affine basis. -/
theorem eq_convexHull_of_supports (hdim : Module.finrank ℝ E = 2)
    (K : Set E) (hK : Convex ℝ K) (v : Fin 3 → E) (hv : ∀ i, v i ∈ K)
    (hind : AffineIndependent ℝ v) (g : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hside : ∀ x ∈ K, ∀ i, 0 ≤ g i x)
    (hoff : ∀ i j, j ≠ i → g i (v j) = 0)
    (hnonzero : ∀ i, ∃ x, g i x ≠ 0) : K = convexHull ℝ (Set.range v) := by
  let B : AffineBasis (Fin 3) ℝ E := ⟨v, hind,
    hind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [hdim])⟩
  have hrepr (i : Fin 3) (x : E) : g i x = B.coord i x * g i (v i) := by
    calc
      g i x = g i (∑ j, B.coord j x • v j) :=
        congrArg (g i) (B.linear_combination_coord_eq_self x).symm
      _ = ∑ j, B.coord j x * g i (v j) :=
        Plank.Body.map_comb (g i) (fun j => B.coord j x) v (B.sum_coord_apply_eq_one x)
      _ = B.coord i x * g i (v i) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [hoff i j hji, mul_zero]
        · simp
  have hpos (i : Fin 3) : 0 < g i (v i) := by
    have hnonneg := hside (v i) (hv i) i
    apply lt_of_le_of_ne hnonneg
    intro heq
    obtain ⟨x, hx⟩ := hnonzero i
    apply hx
    rw [hrepr, ← heq, mul_zero]
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ convexHull ℝ (Set.range B)
    rw [B.convexHull_eq_nonneg_coord]
    intro i
    have h := hside x hx i
    rw [hrepr] at h
    exact nonneg_of_mul_nonneg_left h (hpos i)
  · exact convexHull_min (by rintro _ ⟨i, rfl⟩; exact hv i) hK

end Plank.Convex.PlanarTight.TriangleSupportShape

/-- info: 'Plank.Convex.PlanarTight.TriangleSupportShape.independent_of_strict_maxima' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TriangleSupportShape.independent_of_strict_maxima

/-- info: 'Plank.Convex.PlanarTight.TriangleSupportShape.eq_convexHull_of_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TriangleSupportShape.eq_convexHull_of_supports
