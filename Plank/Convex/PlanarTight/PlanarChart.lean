/- An affine chart for a coordinate plane with nonzero third coefficient. -/
module
public import Plank.Convex.PlanarTight.StrictCapSetting
public import Mathlib.LinearAlgebra.AffineSpace.Independent
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.PlanarChart

abbrev Point2 := Fin 2 → ℝ
abbrev Point3 := Fin 3 → ℝ

def projection : Point3 →ᵃ[ℝ] Point2 :=
  AffineMap.pi ![AffineMap.proj 0, AffineMap.proj 1]

def forms (a : Point3) (d : ℝ) : Fin 3 → Point2 →ᵃ[ℝ] ℝ :=
  ![AffineMap.proj 0, AffineMap.proj 1,
    (a 2)⁻¹ • (AffineMap.const ℝ Point2 d - a 0 • AffineMap.proj 0 -
      a 1 • AffineMap.proj 1)]

def graph (a : Point3) (d : ℝ) : Point2 →ᵃ[ℝ] Point3 := AffineMap.pi (forms a d)

theorem graph_plane (a : Point3) (d : ℝ) (ha : a 2 ≠ 0) (x : Point2) :
    ∑ i, a i * forms a d i x = d := by
  rw [Fin.sum_univ_three]
  change a 0 * x 0 + a 1 * x 1 +
    a 2 * ((a 2)⁻¹ * (d - a 0 * x 0 - a 1 * x 1)) = d
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  ring

theorem graph_injective (a : Point3) (d : ℝ) : Function.Injective (graph a d) := by
  intro x y h
  funext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

theorem graph_projection (a : Point3) (d : ℝ) (ha : a 2 ≠ 0)
    (x : Point3) (hx : ∑ i, a i * x i = d) : graph a d (projection x) = x := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · change (a 2)⁻¹ * (d - a 0 * x 0 - a 1 * x 1) = x 2
    simp only [Fin.sum_univ_three] at hx
    have he : d - a 0 * x 0 - a 1 * x 1 = a 2 * x 2 := by linarith only [hx]
    rw [he, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]

theorem graph_image_projection (K : Set Point3) (a : Point3) (d : ℝ) (ha : a 2 ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i * x i = d) : graph a d '' (projection '' K) = K := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simpa only [graph_projection a d ha x (hplane x hx)] using hx
  · intro x hx
    exact ⟨projection x, ⟨x, hx, rfl⟩, graph_projection a d ha x (hplane x hx)⟩

/-- An exact nondegenerate triangle in the chart is an exact nondegenerate
triangle in the original coordinate plane. -/
theorem triangle_of_projection (K : Set Point3) (a : Point3) (d : ℝ) (ha : a 2 ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i * x i = d) (v : Fin 3 → Point2)
    (hv : AffineIndependent ℝ v) (hbody : projection '' K = convexHull ℝ (Set.range v)) :
    ∃ w : Fin 3 → Point3, AffineIndependent ℝ w ∧ K = convexHull ℝ (Set.range w) := by
  refine ⟨graph a d ∘ v, hv.map' (graph a d) (graph_injective a d), ?_⟩
  calc
    K = graph a d '' (projection '' K) := (graph_image_projection K a d ha hplane).symm
    _ = graph a d '' convexHull ℝ (Set.range v) := by rw [hbody]
    _ = convexHull ℝ (Set.range (graph a d ∘ v)) := by
      rw [AffineMap.image_convexHull, ← Set.range_comp]

end Plank.Convex.PlanarTight.PlanarChart

/-- info: 'Plank.Convex.PlanarTight.PlanarChart.graph_image_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.PlanarChart.graph_image_projection

/-- info: 'Plank.Convex.PlanarTight.PlanarChart.triangle_of_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.PlanarChart.triangle_of_projection
