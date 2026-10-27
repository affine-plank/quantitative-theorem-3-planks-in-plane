/- Perspective support inequalities identify the specified apex and
base contacts as the exact triangle, retaining their zero-face geometry. -/
module
public import Plank.Convex.PlanarTight.AnchoredCapBody
public import Plank.Convex.PlanarTight.PerspectiveTriangle
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.PerspectiveCap

abbrev Point := Fin 3 → ℝ

theorem of_supports (K : Set Point) (hK : Convex ℝ K)
    (hbox₀ : ∀ z ∈ K, 0 ≤ z 0)
    (a b c d : ℝ) (hb : 0 < b)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (T R U : Point) (hT : T ∈ K) (hR : R ∈ K) (hU : U ∈ K)
    (hT₀ : T 0 = 1) (hR₀ : R 0 = 0) (hR₁ : R 1 = 1) (hR₂ : R 2 = 0)
    (hU₀ : U 0 = 0) (hU₁ : U 1 = 0) (hU₂ : U 2 = 1)
    (hY : ∀ z ∈ K, T 1 * z 0 ≤ z 1) (hZ : ∀ z ∈ K, T 2 * z 0 ≤ z 2) :
    AnchoredCapBody.Has K (AffineMap.proj 0) T := by
  have hpR := hplane R hR
  have hpU := hplane U hU
  rw [hR₀, hR₁, hR₂] at hpR
  rw [hU₀, hU₁, hU₂] at hpU
  have hd : d = b := by linarith only [hpR]
  have hc : c = b := by linarith only [hpR, hpU]
  have hpT := hplane T hT
  rw [hT₀, hc, hd] at hpT
  have hsub : convexHull ℝ {T, R, U} ⊆ K := by
    apply convexHull_min _ hK
    intro z hz
    rcases hz with rfl | rfl | rfl <;> assumption
  refine ⟨hT₀, R, U, hR₀, hU₀, Set.Subset.antisymm ?_ hsub⟩
  intro z hz
  let v : Fin 3 → Point := ![T, R, U]
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
  · intro i
    fin_cases i <;> simp [v]
  · ext i
    fin_cases i <;> simp [Fin.sum_univ_three, w, v, hT₀, hR₀, hR₁, hR₂, hU₀, hU₁, hU₂] <;> ring

end Plank.Convex.PlanarTight.PerspectiveCap

/-- info: 'Plank.Convex.PlanarTight.PerspectiveCap.of_supports' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.PerspectiveCap.of_supports
