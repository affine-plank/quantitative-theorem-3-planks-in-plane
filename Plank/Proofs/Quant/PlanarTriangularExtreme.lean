/- Extreme points in an attained triangular affine enclosure. -/
module

public import Plank.Proofs.Quant.PlanarCriticalAnchoredShape
public import Plank.Proofs.Quant.PlanarFiniteExtremeHull
public import Plank.Proofs.Quant.PlanarSingletonCorners

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTriangularExtreme

open Set MeasureTheory PlanarQuantitative PlanarOnePlankShape PlanarOnePlankVertices
open Plank.Convex.PlanarTight TwoPlankClassification PlanarSingletonCorners
open scoped BigOperators

/-- The two top contacts in the triangular enclosure are actual body points. -/
theorem contacts {K : Set Point} (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (hshape : ∀ x ∈ K, X x+Y x ≤ 1) :
    ∃ R ∈ K, ∃ T ∈ K, X R = 1 ∧ Y R = 0 ∧ X T = 0 ∧ Y T = 1 := by
  obtain ⟨R,hR,hXR⟩ := H.maxX
  obtain ⟨T,hT,hYT⟩ := H.maxY
  refine ⟨R,hR,T,hT,hXR,?_,?_,hYT⟩
  · have hh := hshape R hR
    rw [hXR] at hh
    linarith only [hh,(H.box R hR).2.1]
  · have hh := hshape T hT
    rw [hYT] at hh
    linarith only [hh,(H.box T hT).1.1]

/-- Either the two coordinates distinguish every planar point, or they
are complementary on the whole body. This includes dependent directions. -/
theorem injective_or_complementary {K : Set Point} (X Y : Point →ᵃ[ℝ] ℝ)
    (H : Ranges K X Y) (hshape : ∀ x ∈ K, X x+Y x ≤ 1) :
    (∀ x y : Point, X x = X y → Y x = Y y → x = y) ∨
      (∀ x ∈ K, Y x = 1-X x) := by
  by_cases hB : ∃ B ∈ K, X B+Y B < 1
  · obtain ⟨B,_,hB⟩ := hB
    obtain ⟨R,_,T,_,hXR,hYR,hXT,hYT⟩ := contacts X Y H hshape
    let F : Point →ᵃ[ℝ] Point := AffineMap.pi ![X,Y]
    have hRlin : F.linear (R-T) = ![1,-1] := by
      have hh := F.linearMap_vsub R T
      change F.linear (R-T) = F R-F T at hh
      rw [hh]
      ext i
      fin_cases i <;> simp [F,hXR,hYR,hXT,hYT]
    have hBlin : F.linear (B-T) = ![X B,Y B-1] := by
      have hh := F.linearMap_vsub B T
      change F.linear (B-T) = F B-F T at hh
      rw [hh]
      ext i
      fin_cases i <;> simp [F,hXT,hYT]
    have hn : X B+Y B-1 ≠ 0 := by linarith only [hB]
    have hsurj : Function.Surjective F.linear := by
      intro z
      let b := (z 0+z 1)/(X B+Y B-1)
      refine ⟨(z 0-b*X B) • (R-T)+b • (B-T),?_⟩
      rw [map_add,map_smul,map_smul,hRlin,hBlin]
      ext i
      fin_cases i <;> simp [b]
      field_simp
      ring
    have hinj : Function.Injective F :=
      F.linear_injective_iff.mp (LinearMap.injective_iff_surjective.mpr hsurj)
    exact Or.inl (fun x y hx hy => hinj (by ext i; fin_cases i <;> assumption))
  · right
    intro x hx
    have hh := hshape x hx
    have hn : ¬ X x+Y x < 1 := fun h => hB ⟨x,hx,h⟩
    linarith only [hh,le_of_not_gt hn]

/-- If the origin contact is present too, the triangular enclosure is
the exact triangle, including its boundary. -/
theorem triangle_of_origin {K : Set Point} (hconv : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (hshape : ∀ x ∈ K, X x+Y x ≤ 1)
    (B : Point) (hB : B ∈ K) (hXB : X B = 0) (hYB : Y B = 0) :
    ∃ a b d : Point, K = convexHull ℝ {a,b,d} := by
  obtain ⟨R,hR,T,hT,hXR,hYR,hXT,hYT⟩ := contacts X Y H hshape
  have hinj : ∀ x y : Point, X x = X y → Y x = Y y → x = y := by
    rcases injective_or_complementary X Y H hshape with hi | hc
    · exact hi
    · have hh := hc B hB
      rw [hXB,hYB] at hh
      norm_num at hh
  let v : Fin 3 → Point := ![B,T,R]
  refine ⟨B,T,R,Subset.antisymm ?_ ?_⟩
  · intro x hx
    let w : Fin 3 → ℝ := ![1-X x-Y x,Y x,X x]
    have hsum : ∑ i, w i = 1 := by simp [w,Fin.sum_univ_three]
    apply mem_convexHull_of_exists_fintype w v
    · intro i
      fin_cases i
      · dsimp [w]
        linarith only [hshape x hx]
      · exact (H.box x hx).2.1
      · exact (H.box x hx).1.1
    · exact hsum
    · intro i
      fin_cases i <;> simp [v]
    · apply hinj
      · rw [Body.map_comb X w v hsum]
        simp [Fin.sum_univ_three,v,w,hXB,hXT,hXR]
      · rw [Body.map_comb Y w v hsum]
        simp [Fin.sum_univ_three,v,w,hYB,hYT,hYR]
  · apply convexHull_min _ hconv
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

/-- An extreme singleton of a critical corner is a top contact, unless
the whole body is already the exact triangle. -/
theorem singleton_extreme {K : Set Point} (hconv : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (hshape : ∀ x ∈ K, X x+Y x ≤ 1)
    (R T : Point) (hR : R ∈ K) (hT : T ∈ K)
    (hXR : X R = 1) (hYR : Y R = 0) (hXT : X T = 0) (hYT : Y T = 1)
    (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (x : Point) (hx : x ∈ K.extremePoints ℝ) (sx sy : Bool)
    (hs : corner K X Y 0 u 0 (1-u) sx sy = {x}) :
    x = R ∨ x = T ∨ ∃ a b d : Point, K = convexHull ℝ {a,b,d} := by
  cases sx <;> cases sy
  · have hh : x ∈ corner K X Y 0 u 0 (1-u) false false := by rw [hs]; simp
    change x ∈ K ∧ X x ≤ 0 ∧ Y x ≤ 0 at hh
    exact Or.inr (Or.inr (triangle_of_origin hconv X Y H hshape x hx.1
      (le_antisymm hh.2.1 (H.box x hx.1).1.1)
      (le_antisymm hh.2.2 (H.box x hx.1).2.1)))
  · have hh : T ∈ corner K X Y 0 u 0 (1-u) false true := by
      change T ∈ K ∧ X T ≤ 0 ∧ 1-u ≤ Y T
      exact ⟨hT,by rw [hXT],by rw [hYT]; linarith only [hu]⟩
    rw [hs] at hh
    exact Or.inr (Or.inl (mem_singleton_iff.mp hh).symm)
  · have hh : R ∈ corner K X Y 0 u 0 (1-u) true false := by
      change R ∈ K ∧ u ≤ X R ∧ Y R ≤ 0
      exact ⟨hR,by rw [hXR]; exact hu1.le,by rw [hYR]⟩
    rw [hs] at hh
    exact Or.inl (mem_singleton_iff.mp hh).symm
  · let P := T+u • (R-T)
    have hP : P ∈ K := hconv.add_smul_sub_mem hT hR ⟨hu.le,hu1.le⟩
    have hXP : X P = u := by simp [P,Body.map_add_smul_sub,hXT,hXR]
    have hYP : Y P = 1-u := by
      simp only [P,Body.map_add_smul_sub,hYT,hYR]
      ring
    have hh : P ∈ corner K X Y 0 u 0 (1-u) true true := by
      change P ∈ K ∧ u ≤ X P ∧ 1-u ≤ Y P
      exact ⟨hP,hXP.ge,hYP.ge⟩
    rw [hs] at hh
    have he : P = x := mem_singleton_iff.mp hh
    have hop : P ∈ openSegment ℝ T R := by
      rw [openSegment_eq_image']
      exact ⟨u,⟨hu,hu1⟩,rfl⟩
    have hTx : T = x := hx.2 hT hR (he ▸ hop)
    exact Or.inr (Or.inl hTx.symm)

end Plank.PlanarTriangularExtreme

/-- info: 'Plank.PlanarTriangularExtreme.singleton_extreme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarTriangularExtreme.singleton_extreme
