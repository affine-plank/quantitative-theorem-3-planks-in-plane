/- Nondegenerate supporting-edge critical covers identify an exact triangle. -/
module

public import Plank.Proofs.Quant.PlanarCriticalQuadrilateral

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCriticalAnchoredShape

open Set PlanarQuantitative
open Plank.Convex.PlanarTight TwoPlankClassification
open scoped BigOperators

/-- The attained unit ranges turn a triangular enclosure with its apex
strictly between the two opposite levels into the exact original triangle.
The contact points prove coordinate injectivity; this is not an extra
assumption on the affine directions. -/
theorem triangle_of_enclosure {K : Set Point} (hK : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hshape : ∀ x ∈ K, c*X x ≤ Y x ∧ Y x ≤ 1-(1-c)*X x) :
    ∃ a b d : Point, K = convexHull ℝ {a,b,d} := by
  obtain ⟨B,hB,hYB⟩ := H.minY
  obtain ⟨T,hT,hYT⟩ := H.maxY
  obtain ⟨R,hR,hXR⟩ := H.maxX
  have hXB : X B = 0 := by
    have hh := (hshape B hB).1
    rw [hYB] at hh
    nlinarith only [hh,(H.box B hB).1.1,hc]
  have hXT : X T = 0 := by
    have hh := (hshape T hT).2
    rw [hYT] at hh
    nlinarith only [hh,(H.box T hT).1.1,hc1]
  have hYR : Y R = c := by
    have hh := hshape R hR
    rw [hXR] at hh
    nlinarith only [hh.1,hh.2]
  let F : Point →ᵃ[ℝ] Point := AffineMap.pi ![X,Y]
  have hTlin : F.linear (T-B) = ![0,1] := by
    have hh := F.linearMap_vsub T B
    change F.linear (T-B) = F T-F B at hh
    rw [hh]
    ext i
    fin_cases i <;> simp [F,hXB,hXT,hYB,hYT]
  have hRlin : F.linear (R-B) = ![1,c] := by
    have hh := F.linearMap_vsub R B
    change F.linear (R-B) = F R-F B at hh
    rw [hh]
    ext i
    fin_cases i <;> simp [F,hXB,hXR,hYB,hYR]
  have hsurj : Function.Surjective F.linear := by
    intro z
    refine ⟨z 0 • (R-B)+(z 1-c*z 0) • (T-B),?_⟩
    rw [map_add,map_smul,map_smul,hRlin,hTlin]
    ext i
    fin_cases i <;> simp <;> ring
  have hinj : Function.Injective F :=
    F.linear_injective_iff.mp (LinearMap.injective_iff_surjective.mpr hsurj)
  let v : Fin 3 → Point := ![B,T,R]
  refine ⟨B,T,R,Subset.antisymm ?_ ?_⟩
  · intro x hx
    let w : Fin 3 → ℝ := ![1-(1-c)*X x-Y x,Y x-c*X x,X x]
    have hsum : ∑ i, w i = 1 := by simp [w,Fin.sum_univ_three]; ring
    apply mem_convexHull_of_exists_fintype w v
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr (hshape x hx).2
      · exact sub_nonneg.mpr (hshape x hx).1
      · exact (H.box x hx).1.1
    · exact hsum
    · intro i
      fin_cases i <;> simp [v]
    · apply hinj
      ext i
      fin_cases i
      · change X (∑ j, w j • v j) = X x
        rw [Body.map_comb X w v hsum]
        simp [Fin.sum_univ_three,v,hXB,hXT,hXR,w]
      · change Y (∑ j, w j • v j) = Y x
        rw [Body.map_comb Y w v hsum]
        simp [Fin.sum_univ_three,v,hYB,hYT,hYR,w]
        ring
  · apply convexHull_min _ hK
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

/-- If neither endpoint of the second window is a support endpoint, an
anchored full-cover normal form has an exact triangle body. -/
theorem triangle_of_anchored {K : Set Point} (hK : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y) (l u m v : ℝ)
    (ha : Anchored K X Y l u m v) (hm : 0 < m) (hv : v < 1) :
    ∃ a b d : Point, K = convexHull ℝ {a,b,d} := by
  obtain ⟨_,hu,_,c,hc,hc1,hmdef,hvdef,hshape⟩ := ha
  have hcp : 0 < c := by
    by_contra h
    have hz : c = 0 := le_antisymm (le_of_not_gt h) hc
    rw [hmdef,hz,mul_zero] at hm
    exact lt_irrefl 0 hm
  have hcl : c < 1 := by
    by_contra h
    have hz : c = 1 := le_antisymm hc1 (le_of_not_gt h)
    rw [hvdef,hz,mul_one] at hv
    linarith only [hv]
  exact triangle_of_enclosure hK X Y H c hcp hcl hshape

/-- The two endpoint-apex enclosures are explicit corner cuts of a right
triangle in the attained affine coordinates. They contain no area or
covering predicate. -/
def DegenerateAnchored (K : Set Point) (X Y : Point →ᵃ[ℝ] ℝ)
    (l u m v : ℝ) : Prop :=
  l = 0 ∧ 0 < u ∧ u < 1 ∧
    ((m = 0 ∧ v = 1-u ∧ ∀ x ∈ K, X x+Y x ≤ 1) ∨
     (m = u ∧ v = 1 ∧ ∀ x ∈ K, X x ≤ Y x))

/-- Every anchored critical family is either an exact triangle, or one
of the two explicit endpoint-apex corner-cut enclosures. -/
theorem anchored_alternatives {K : Set Point} (hK : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y) (l u m v : ℝ)
    (ha : Anchored K X Y l u m v) :
    (∃ a b d : Point, K = convexHull ℝ {a,b,d}) ∨
      DegenerateAnchored K X Y l u m v := by
  obtain ⟨hl,hu,hu1,c,hc,hc1,hm,hv,hshape⟩ := ha
  by_cases h0 : c = 0
  · right
    refine ⟨hl,hu,hu1,Or.inl ⟨?_,?_,?_⟩⟩
    · simpa only [h0,mul_zero] using hm
    · simpa only [h0,mul_zero,zero_add] using hv
    · intro x hx
      have hh := (hshape x hx).2
      rw [h0] at hh
      linarith only [hh]
  · by_cases h1 : c = 1
    · right
      refine ⟨hl,hu,hu1,Or.inr ⟨?_,?_,?_⟩⟩
      · simpa only [h1,mul_one] using hm
      · rw [hv,h1,mul_one]
        ring
      · intro x hx
        simpa only [h1,one_mul] using (hshape x hx).1
    · exact Or.inl (triangle_of_enclosure hK X Y H c
        (lt_of_le_of_ne hc (fun he => h0 he.symm)) (lt_of_le_of_ne hc1 h1) hshape)

end Plank.PlanarCriticalAnchoredShape

/-- info: 'Plank.PlanarCriticalAnchoredShape.triangle_of_enclosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCriticalAnchoredShape.triangle_of_enclosure
/-- info: 'Plank.PlanarCriticalAnchoredShape.anchored_alternatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCriticalAnchoredShape.anchored_alternatives
