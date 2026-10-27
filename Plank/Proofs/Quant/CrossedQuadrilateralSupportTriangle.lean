/- Two positive planks with a supporting side can be tight only on a triangle. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSupportOriginal
public import Plank.Proofs.Quant.PlanarSupportPairTransport
public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSupportTriangle
open Plank
open Set MeasureTheory PlanarQuantitative
open Plank.Convex.DeficientHeightTilt

/-- The finite four-point body reduction has exactly two geometric shape
alternatives. Redundant or repeated generators are absorbed into the triangle. -/
theorem triangle_or_genuine {K : Set Point} (a b c d : Point)
    (hK : K = convexHull ℝ {a,b,c,d}) :
    (∃ u v w : Point, K = convexHull ℝ {u,v,w}) ∨ CrossedQuadrilateralGenuine.Genuine K := by
  classical
  let E := K.extremePoints ℝ
  have hfin : ({a,b,c,d} : Set Point).Finite := by simp
  have hsub : E ⊆ {a,b,c,d} := by
    dsimp [E]
    rw [hK]
    exact extremePoints_convexHull_subset
  have hEfin : E.Finite := hfin.subset hsub
  have hcompact : IsCompact K := by rw [hK]; exact hfin.isCompact_convexHull ℝ
  have hconv : Convex ℝ K := by rw [hK]; exact convex_convexHull ℝ _
  have hEHull : K = convexHull ℝ E := by
    have hh := closure_convexHull_extremePoints hcompact hconv
    change closure (convexHull ℝ E) = K at hh
    rw [(hEfin.isClosed_convexHull ℝ).closure_eq] at hh
    exact hh.symm
  have hcard : E.ncard ≤ 4 := by
    have hn := Set.ncard_le_ncard hsub hfin
    have h₁ := Set.ncard_insert_le a ({b,c,d} : Set Point)
    have h₂ := Set.ncard_insert_le b ({c,d} : Set Point)
    have h₃ := Set.ncard_insert_le c ({d} : Set Point)
    simp only [Set.ncard_singleton] at h₃
    omega
  by_cases hfour : E.ncard = 4
  · right
    obtain ⟨u,v,w,z,huv,huw,huz,hvw,hvz,hwz,hE⟩ := Set.ncard_eq_four.mp hfour
    let p : Fin 4 → Point := ![u,v,w,z]
    have hp : Function.Injective p := by
      intro i j he
      fin_cases i <;> fin_cases j <;> norm_num [p] at he ⊢ <;> tauto
    have hrange : Set.range p = {u,v,w,z} := by
      ext x
      simp [p,eq_comm,or_comm,or_left_comm]
    refine ⟨p,hp,?_,?_⟩
    · rw [hrange,← hE]
      exact hEHull
    · intro i
      change p i ∈ E
      rw [hE,← hrange]
      exact mem_range_self i
  · left
    have hn : E.ncard ≤ 3 := by omega
    have hz : E.ncard ≠ 0 := by
      intro hz
      have hE : E = ∅ := (Set.ncard_eq_zero hEfin).mp hz
      have ha : a ∈ K := by rw [hK]; exact subset_convexHull ℝ _ (by simp)
      rw [hEHull,hE,convexHull_empty] at ha
      exact ha
    have hc : E.ncard = 1 ∨ E.ncard = 2 ∨ E.ncard = 3 := by omega
    rcases hc with h | h | h
    · obtain ⟨u,hE⟩ := Set.ncard_eq_one.mp h
      refine ⟨u,u,u,?_⟩
      simpa only [hE,insert_eq_of_mem (mem_singleton u)] using hEHull
    · obtain ⟨u,v,_,hE⟩ := Set.ncard_eq_two.mp h
      refine ⟨u,v,v,?_⟩
      simpa only [hE,insert_eq_of_mem (mem_singleton v)] using hEHull
    · obtain ⟨u,v,w,_,_,_,hE⟩ := Set.ncard_eq_three.mp h
      exact ⟨u,v,w,hEHull.trans (congrArg (convexHull ℝ) hE)⟩

/-- Actual equality with two positive planks and a supporting boundary
forces a triangle, without a prior polygon or quadrilateral hypothesis. -/
theorem support_equality_triangle {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f g : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo₀ hi₀ lo hi : ℝ) (hface : f b = lo₀ ∨ f a = hi₀) (horder : lo₀ < hi₀) (ho : lo < hi)
    (hWf : 0 < rangeWidth K f) (hWg : 0 < rangeWidth K g)
    (hR : (hi₀-lo₀)/rangeWidth K f+(hi-lo)/rangeWidth K g < 1)
    (he : (volume (K \ ({x | lo₀ ≤ f x ∧ f x ≤ hi₀} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal =
      (max 0 (1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g))^2*(volume K).toReal) :
    ∃ u v w : Point, K = convexHull ℝ {u,v,w} := by
  obtain ⟨u,v,w,z,hshape⟩ := PlanarSupportPairClassification.equality_implies_four_vertices_of_support
    hK hc hV f g a b ha hb hmax hmin lo₀ hi₀ lo hi hface horder.le ho hWf hWg hR he
  rcases triangle_or_genuine u v w z hshape with ht | hG
  · exact ht
  · have hstrict := CrossedQuadrilateralSupportOriginal.support_strict hG hV f g a b
      ha hb hmax hmin lo₀ hi₀ lo hi hface horder ho hWf hWg hR
    rw [max_eq_right (by linarith only [hR] : 0 ≤ 1-(hi₀-lo₀)/rangeWidth K f-(hi-lo)/rangeWidth K g)] at he
    exact (not_lt_of_ge he.le hstrict).elim

end Quant.CrossedQuadrilateralSupportTriangle

/-- info: 'Quant.CrossedQuadrilateralSupportTriangle.support_equality_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSupportTriangle.support_equality_triangle
