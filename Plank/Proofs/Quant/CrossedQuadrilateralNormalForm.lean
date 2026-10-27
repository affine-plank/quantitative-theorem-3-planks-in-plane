/- Every genuine quadrilateral has two diagonals crossing in their interiors. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralImageStrata
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralNormalForm
open Set MeasureTheory
open Plank.PlanarQuantitative

/-- An extreme generator cannot be recovered from a hull omitting its index. -/
theorem extreme_index (v : Fin 4 → Point) (hv : Function.Injective v)
    (he : ∀ i, v i ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ)
    (I : Set (Fin 4)) (i : Fin 4) (hi : v i ∈ convexHull ℝ (v '' I)) : i ∈ I := by
  have hs : convexHull ℝ (v '' I) ⊆ convexHull ℝ (Set.range v) :=
    convexHull_mono (Set.image_subset_range v I)
  have hxe := inter_extremePoints_subset_extremePoints_of_subset hs ⟨hi,he i⟩
  obtain ⟨j,hj,hji⟩ := extremePoints_convexHull_subset hxe
  exact hv hji ▸ hj

/-- With four distinct extreme vertices, Radon's partition must have two
vertices on each side, and its intersection is internal to both diagonals. -/
theorem crossing_diagonals (v : Fin 4 → Point) (hv : Function.Injective v)
    (he : ∀ i, v i ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ) :
    ∃ a b c d z : Point, Set.range v = {a,b,c,d} ∧
      a ≠ c ∧ b ≠ d ∧ z ∈ openSegment ℝ a c ∧ z ∈ openSegment ℝ b d := by
  classical
  have hn : ¬AffineIndependent ℝ v := by
    intro h
    have hc := h.card_le_finrank_succ
    have hd : Module.finrank ℝ (vectorSpan ℝ (Set.range v)) ≤ 2 := by
      simpa [Point] using (Submodule.finrank_le (vectorSpan ℝ (Set.range v)))
    norm_num only [Fintype.card_fin] at hc
    omega
  obtain ⟨I,z,hzI,hzIc⟩ := Convex.radon_partition hn
  let inds (J : Set (Fin 4)) : Finset (Fin 4) := Finset.univ.filter (fun i => i ∈ J)
  have htwo (J : Set (Fin 4)) (hzJ : z ∈ convexHull ℝ (v '' J))
      (hzJc : z ∈ convexHull ℝ (v '' Jᶜ)) : 2 ≤ (inds J).card := by
    by_contra hh
    have hle : (inds J).card ≤ 1 := by omega
    by_cases hz : (inds J) = ∅
    · have hJ : J = ∅ := by
        simpa [inds] using congrArg (fun A : Finset (Fin 4) => (A : Set (Fin 4))) hz
      simp [hJ] at hzJ
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    have hiJ : i ∈ J := by simpa [inds] using hi
    have hJ : J = {i} := by
      ext j
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hj
        exact (Finset.card_le_one.mp hle) j (by simpa [inds] using hj) i hi
      · rintro rfl
        exact hiJ
    have hzi : z = v i := by simpa [hJ] using hzJ
    have hiJc := extreme_index v hv he Jᶜ i (by rwa [← hzi])
    exact hiJc hiJ
  have hI := htwo I hzI hzIc
  have hIc := htwo Iᶜ hzIc (by simpa using hzI)
  have hsum : (inds I).card+(inds Iᶜ).card = 4 := by
    have hh : (inds I)ᶜ = inds Iᶜ := by ext i; simp [inds]
    simpa only [hh,Fintype.card_fin] using Finset.card_add_card_compl (inds I)
  obtain ⟨i,k,hik,hIk⟩ := Finset.card_eq_two.mp (show (inds I).card = 2 by omega)
  obtain ⟨j,l,hjl,hJl⟩ := Finset.card_eq_two.mp (show (inds Iᶜ).card = 2 by omega)
  have hIs : I = {i,k} := by
    simpa [inds] using congrArg (fun A : Finset (Fin 4) => (A : Set (Fin 4))) hIk
  have hIcs : Iᶜ = {j,l} := by
    ext m
    change m ∉ I ↔ m = j ∨ m = l
    simpa [inds] using Iff.of_eq (congrArg (fun A : Finset (Fin 4) => m ∈ A) hJl)
  have hzne (a : Fin 4) : v a ≠ z := by
    intro h
    by_cases ha : a ∈ I
    · exact (extreme_index v hv he Iᶜ a (by rwa [h])) ha
    · exact ha (extreme_index v hv he I a (by rwa [h]))
  refine ⟨v i,v j,v k,v l,z,?_,hv.ne hik,hv.ne hjl,?_,?_⟩
  · calc
      Set.range v = v '' (I ∪ Iᶜ) := by rw [Set.union_compl_self,Set.image_univ]
      _ = {v i,v k} ∪ {v j,v l} := by rw [Set.image_union,hIcs,hIs]; simp [Set.image_insert_eq,Set.image_singleton]
      _ = {v i,v j,v k,v l} := by
        ext x
        simp only [mem_union,mem_insert_iff,mem_singleton_iff]
        tauto
  · apply mem_openSegment_of_ne_left_right (hzne i) (hzne k)
    simpa [hIs,Set.image_insert_eq,Set.image_singleton,convexHull_pair] using hzI
  · apply mem_openSegment_of_ne_left_right (hzne j) (hzne l)
    simpa [hIcs,Set.image_insert_eq,Set.image_singleton,convexHull_pair] using hzIc

theorem body_eq_hull (S : CrossedQuadrilateralAttainment.Shape) :
    CrossedQuadrilateralFormDirections.body S =
      convexHull ℝ {![S.a,0],![0,S.b],![-S.c,0],![0,-S.d]} := by
  let C : Point ≃ᵃ[ℝ] (ℝ × ℝ) := ParallelProductPlane.coordinates.toLinearEquiv.toAffineEquiv
  have hi : CrossedQuadrilateralFormDirections.body S = C.symm '' S.body := by
    ext x
    constructor
    · intro hx
      exact ⟨C x,hx,C.symm_apply_apply x⟩
    · rintro ⟨y,hy,rfl⟩
      change C (C.symm y) ∈ S.body
      simpa only [C.apply_symm_apply] using hy
  rw [hi]
  change C.symm.toAffineMap '' convexHull ℝ S.vertices = _
  rw [AffineMap.image_convexHull]
  simp only [CrossedQuadrilateralAttainment.Shape.vertices,Set.image_insert_eq,Set.image_singleton]
  rfl

/-- Two interior-crossing diagonals give the positive diagonal model. Positive
area proves the constructed affine map invertible; no nonsingularity premise
or chosen ordering of the original four points is left over. -/
theorem model_of_crossing (a b c d z : Point)
    (hzx : z ∈ openSegment ℝ a c) (hzy : z ∈ openSegment ℝ b d)
    (hV : 0 < (volume (convexHull ℝ ({a,b,c,d} : Set Point))).toReal) :
    ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point),
      convexHull ℝ ({a,b,c,d} : Set Point) = T '' CrossedQuadrilateralFormDirections.body S := by
  obtain ⟨u,v,hu,hv,huv,hzx⟩ := hzx
  obtain ⟨s,t,hs,ht,hst,hzy⟩ := hzy
  let S : CrossedQuadrilateralAttainment.Shape :=
    ⟨1,1,u/v,s/t,zero_lt_one,zero_lt_one,div_pos hu hv,div_pos hs ht⟩
  let L : Point →ₗ[ℝ] Point :=
    (LinearMap.proj (0 : Fin 2)).smulRight (a-z)+(LinearMap.proj (1 : Fin 2)).smulRight (b-z)
  let A : Point →ᵃ[ℝ] Point := AffineMap.const ℝ Point z+L.toAffineMap
  have hA (x : Point) : A x = z+(x 0 • (a-z)+x 1 • (b-z)) := rfl
  have ha : A ![S.a,0] = a := by simp [hA,S]
  have hb : A ![0,S.b] = b := by simp [hA,S]
  have hc : A ![-S.c,0] = c := by
    ext i
    have hz : u*a i+v*c i = z i := congrFun hzx i
    have hsum : (u+v)*z i = z i := by rw [huv,one_mul]
    change z i+(-(u/v)*(a i-z i)+0*(b i-z i)) = c i
    rw [zero_mul,add_zero]
    field_simp
    nlinarith only [hz,hsum]
  have hd : A ![0,-S.d] = d := by
    ext i
    have hz : s*b i+t*d i = z i := congrFun hzy i
    have hsum : (s+t)*z i = z i := by rw [hst,one_mul]
    change z i+(0*(a i-z i)+(-(s/t))*(b i-z i)) = d i
    rw [zero_mul,zero_add]
    field_simp
    nlinarith only [hz,hsum]
  have himage : A '' CrossedQuadrilateralFormDirections.body S =
      convexHull ℝ ({a,b,c,d} : Set Point) := by
    rw [body_eq_hull,AffineMap.image_convexHull]
    simp only [Set.image_insert_eq,Set.image_singleton,ha,hb,hc,hd]
  have hvol : volume (A '' CrossedQuadrilateralFormDirections.body S) =
      ENNReal.ofReal |LinearMap.det L| * volume (CrossedQuadrilateralFormDirections.body S) := by
    have he : A '' CrossedQuadrilateralFormDirections.body S =
        (fun x : Point => z+x) '' (L '' CrossedQuadrilateralFormDirections.body S) := by
      rw [Set.image_image]
      rfl
    rw [he,Set.image_add_left,measure_preimage_add]
    exact Measure.addHaar_image_linearMap volume L _
  have hdet : LinearMap.det L ≠ 0 := by
    intro hz
    rw [himage,hz,abs_zero,ENNReal.ofReal_zero,zero_mul] at hvol
    simp only [hvol,ENNReal.toReal_zero,lt_self_iff_false] at hV
  have hbij : Function.Bijective A := by
    constructor
    · intro x y hxy
      change z+L x = z+L y at hxy
      exact (L.equivOfDetNeZero hdet).injective (add_left_cancel hxy)
    · intro y
      obtain ⟨x,hx⟩ := (L.equivOfDetNeZero hdet).surjective (y-z)
      refine ⟨x,?_⟩
      change L x = y-z at hx
      change z+L x = y
      rw [hx]
      abel
  exact ⟨S,AffineEquiv.ofBijective hbij,himage.symm⟩

/-- Every positive-area convex hull of four distinct extreme vertices is an
invertible affine image of the positive diagonal quadrilateral model. -/
theorem exists_model (v : Fin 4 → Point) (hv : Function.Injective v)
    (he : ∀ i, v i ∈ (convexHull ℝ (Set.range v)).extremePoints ℝ)
    (hV : 0 < (volume (convexHull ℝ (Set.range v))).toReal) :
    ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point),
      convexHull ℝ (Set.range v) = T '' CrossedQuadrilateralFormDirections.body S := by
  obtain ⟨a,b,c,d,z,hr,_,_,hzx,hzy⟩ := crossing_diagonals v hv he
  rw [hr] at hV ⊢
  exact model_of_crossing a b c d z hzx hzy hV

end Quant.CrossedQuadrilateralNormalForm

/-- info: 'Quant.CrossedQuadrilateralNormalForm.crossing_diagonals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralNormalForm.crossing_diagonals
