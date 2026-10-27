/- Normalize affine windows once, recording only their three vertex values. -/
module
public import Plank.Proofs.TriangleCoverData
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.AffineTriangle
open Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The directional range on a three-generator convex hull. -/
def vertexSpread (v : Fin 3 → E) (f : E →ᵃ[ℝ] ℝ) : ℝ :=
  max (f (v 0)) (max (f (v 1)) (f (v 2))) -
    min (f (v 0)) (min (f (v 1)) (f (v 2)))

/-- Total interval width relative to the three vertex ranges. -/
def relativeWidthSum (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) : ℝ := ∑ k, (hi k-lo k)/vertexSpread v (f k)

private theorem max3_eq {s : Fin 3 → ℝ} {a : Fin 3} (h : ∀ i, s i ≤ s a) :
    max (s 0) (max (s 1) (s 2)) = s a := by
  refine le_antisymm (max_le (h 0) (max_le (h 1) (h 2))) ?_
  fin_cases a
  · exact le_max_left _ _
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_right _ _)

private theorem min3_eq {s : Fin 3 → ℝ} {a : Fin 3} (h : ∀ i, s a ≤ s i) :
    min (s 0) (min (s 1) (s 2)) = s a := by
  refine le_antisymm ?_ (le_min (h 0) (le_min (h 1) (h 2)))
  fin_cases a
  · exact min_le_left _ _
  · exact min_le_of_right_le (min_le_left _ _)
  · exact min_le_of_right_le (min_le_right _ _)

/-- Affine windows on a three-generator hull give a normalized scalar cover
with exactly the same total relative width. -/
theorem exists_normalized_cover
    (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (hpos : ∀ k, 0 < vertexSpread v (f k)) (hle : ∀ k, lo k ≤ hi k)
    (hcover : ∀ X ∈ convexHull ℝ (Set.range v), ∃ k, lo k ≤ f k X ∧ f k X ≤ hi k) :
    ∃ C : TriangleNormalization.Cover 3, C.width = relativeWidthSum v f lo hi := by
  let σ (k : Fin 3) := Tuple.sort (fun i => f k (v i))
  have hmono (k : Fin 3) : Monotone ((fun i => f k (v i)) ∘ σ k) :=
    Tuple.monotone_sort (fun i => f k (v i))
  have hlb (k i : Fin 3) : f k (v (σ k 0)) ≤ f k (v i) := by
    simpa using hmono k (Fin.zero_le ((σ k).symm i))
  have hub (k i : Fin 3) : f k (v i) ≤ f k (v (σ k 2)) := by
    simpa using hmono k (Fin.le_last ((σ k).symm i))
  let m (k : Fin 3) := f k (v (σ k 0))
  let W (k : Fin 3) := vertexSpread v (f k)
  have hW (k : Fin 3) : W k = f k (v (σ k 2))-m k := by
    exact congrArg₂ (· - ·)
      (max3_eq (s := fun i => f k (v i)) (hub k))
      (min3_eq (s := fun i => f k (v i)) (a := σ k 0) (hlb k))
  let g (k i : Fin 3) := (f k (v i)-m k)/W k
  have hf0 (k : Fin 3) : g k (σ k 0) = 0 := by simp only [g, m, sub_self, zero_div]
  have hf1 (k : Fin 3) : g k (σ k 2) = 1 := by
    dsimp [g]
    rw [← hW]
    exact div_self (hpos k).ne'
  have hvertex (k i : Fin 3) : 0 ≤ g k i ∧ g k i ≤ 1 := by
    dsimp [g]
    exact ⟨div_nonneg (sub_nonneg.mpr (hlb k i)) (hpos k).le,
      (div_le_one (show 0 < W k from hpos k)).mpr
        (by rw [hW]; exact sub_le_sub_right (hub k i) _)⟩
  let a (k : Fin 3) := (lo k-m k)/W k
  let b (k : Fin 3) := (hi k-m k)/W k
  have hab (k : Fin 3) : a k ≤ b k :=
    (div_le_div_iff_of_pos_right (hpos k)).mpr (sub_le_sub_right (hle k) _)
  have hcost : (∑ k, (b k-a k)) = relativeWidthSum v f lo hi := by
    apply sum_congr rfl
    intro k _
    dsimp [a,b,W]
    ring
  refine ⟨{
    g := g
    σ := σ
    lo := a
    hi := b
    bounds := hvertex
    zero := hf0
    one := hf1
    ordered := hab
    covered := ?_ }, hcost⟩
  intro l hl0 hl1
  let X := univ.affineCombination ℝ v l
  have hX : X ∈ convexHull ℝ (Set.range v) :=
    affineCombination_mem_convexHull (fun j _ => hl0 j) hl1
  obtain ⟨k, hk⟩ := hcover X hX
  have heval := (univ : Finset (Fin 3)).map_affineCombination v l hl1 (f k)
  rw [affineCombination_eq_linear_combination univ (f k ∘ v) l hl1] at heval
  simp only [Function.comp_apply, smul_eq_mul] at heval
  have hlevel : (∑ j, l j * g k j) = (f k X-m k)/W k := by
    simp only [X, g, ← mul_div_assoc, mul_sub, ← sum_div, sum_sub_distrib,
      ← sum_mul, hl1, one_mul, ← heval]
  refine ⟨k, ?_, ?_⟩ <;> rw [hlevel]
  · exact (div_le_div_iff_of_pos_right (hpos k)).mpr (sub_le_sub_right hk.1 _)
  · exact (div_le_div_iff_of_pos_right (hpos k)).mpr (sub_le_sub_right hk.2 _)

end Plank.AffineTriangle
