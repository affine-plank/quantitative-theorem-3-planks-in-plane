/- Split a genuine quadrilateral into the two triangles on a diagonal. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralOneDiagonal
public import Plank.Proofs.TriangleGeometry

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralDiagonalSplit
open Set MeasureTheory Proofs.Basic Proofs.Transport
open CrossedQuadrilateralAttainment
open scoped BigOperators

def half (S : Shape) (j : Bool) : Triangle where
  A := (-S.c,0)
  B := (S.a,0)
  C := (0,S.Y j)
  not_collinear := not_collinear_of_det3_ne_zero (by
    change (S.a-(-S.c))*(S.Y j-0)-(0-0)*(0-(-S.c)) ≠ 0
    simpa only [sub_neg_eq_add,sub_zero,sub_self,zero_mul] using
      mul_ne_zero (add_pos S.ha S.hc).ne' (S.Y_ne j))

theorem compact_half (S : Shape) (j : Bool) : IsCompact (half S j).set := by
  rw [set_eq_convexHull]
  apply Set.Finite.isCompact_convexHull
  simp

theorem half_subset_body (S : Shape) (j : Bool) : (half S j).set ⊆ S.body := by
  rw [set_eq_convexHull]
  apply convexHull_min _ (convex_body S)
  rintro z (rfl | rfl | rfl)
  · exact vertexX_mem S false
  · exact vertexX_mem S true
  · exact vertexY_mem S j

theorem zero_mem_half (S : Shape) (j : Bool) : (0 : Point) ∈ (half S j).set := by
  refine ⟨S.a/(S.a+S.c),S.c/(S.a+S.c),0,
    div_nonneg S.ha.le (add_pos S.ha S.hc).le,
    div_nonneg S.hc.le (add_pos S.ha S.hc).le,le_rfl,?_,?_⟩
  · rw [add_zero,← add_div,div_self (add_pos S.ha S.hc).ne']
  · ext <;> simp [half] <;> ring

theorem core_subset_half (S : Shape) (i j : Bool) : core S i j ⊆ (half S j).set := by
  intro z hz
  let w : Fin 3 → ℝ := ![1-z.1/S.X i-z.2/S.Y j,z.1/S.X i,z.2/S.Y j]
  let v : Fin 3 → Point := ![0,(S.X i,0),(0,S.Y j)]
  have hw : ∀ k ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w k := by
    intro k _; fin_cases k <;> dsimp [w] <;> linarith [hz.1,hz.2.1,hz.2.2]
  have hv : ∀ k ∈ (Finset.univ : Finset (Fin 3)), v k ∈ (half S j).set := by
    intro k _; fin_cases k
    · exact zero_mem_half S j
    · cases i
      · exact mem_A (half S j)
      · exact mem_B (half S j)
    · exact mem_C (half S j)
  have h := (convex_triangle (half S j)).sum_mem hw
    (show ∑ k ∈ (Finset.univ : Finset (Fin 3)), w k = 1 by
      simp [w,Fin.sum_univ_three]; ring) hv
  convert h using 1
  ext <;> simp [v,w,Fin.sum_univ_three,div_mul_cancel₀ _ (S.X_ne i),div_mul_cancel₀ _ (S.Y_ne j)]

theorem body_eq_union (S : Shape) : S.body = (half S false).set ∪ (half S true).set := by
  apply Set.Subset.antisymm
  · intro z hz
    rw [body_eq_cores] at hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    obtain ⟨j,hj⟩ := mem_iUnion.mp hi
    cases j
    · exact Or.inl (core_subset_half S i false hj)
    · exact Or.inr (core_subset_half S i true hj)
  · exact Set.union_subset (half_subset_body S false) (half_subset_body S true)

theorem half_sign (S : Shape) (j : Bool) {z : Point} (hz : z ∈ (half S j).set) :
    0 ≤ z.2/S.Y j := by
  obtain ⟨α,β,γ,_,_,hγ,_,rfl⟩ := hz
  simpa [half,S.Y_ne j] using hγ

theorem halves_null_inter (S : Shape) :
    volume ((half S false).set ∩ (half S true).set) = 0 := by
  apply measure_mono_null (t := {z : Point | dot (0,1) z = 0})
  · intro z hz
    have hm := half_sign S false hz.1
    have hp := half_sign S true hz.2
    change 0 ≤ z.2/(-S.d) at hm
    change 0 ≤ z.2/S.b at hp
    have hm' := (le_div_iff_of_neg (neg_neg_of_pos S.hd)).mp hm
    have hp' := (le_div_iff₀ S.hb).mp hp
    simp only [zero_mul] at hm' hp'
    simpa only [Set.mem_ofPred_eq,dot,zero_mul,one_mul,zero_add] using le_antisymm hm' hp'
  · exact volume_line (by norm_num : ((0,1) : Point) ≠ 0) 0

theorem area_split (S : Shape) :
    (volume S.body).toReal = (volume (half S false).set).toReal +
      (volume (half S true).set).toReal := by
  have h := measureReal_union_add_inter (μ := volume)
    (s := (half S false).set) (compact_half S true).measurableSet
    (compact_half S false).measure_ne_top (compact_half S true).measure_ne_top
  simp only [measureReal_def] at h
  rw [← body_eq_union,halves_null_inter] at h
  simpa only [measureReal_def,ENNReal.toReal_zero,add_zero] using h

theorem gap_split (S : Shape) (A : Set Point) (hA : MeasurableSet A) :
    (volume (S.body \ A)).toReal = (volume ((half S false).set \ A)).toReal +
      (volume ((half S true).set \ A)).toReal := by
  have hn : volume (((half S false).set \ A) ∩ ((half S true).set \ A)) = 0 :=
    measure_mono_null (inter_subset_inter sdiff_subset sdiff_subset) (halves_null_inter S)
  have h := measureReal_union_add_inter (μ := volume)
    (s := (half S false).set \ A) ((compact_half S true).measurableSet.diff hA)
    (measure_ne_top_of_subset sdiff_subset (compact_half S false).measure_ne_top)
    (measure_ne_top_of_subset sdiff_subset (compact_half S true).measure_ne_top)
  have hu : ((half S false).set \ A) ∪ ((half S true).set \ A) = S.body \ A := by
    rw [body_eq_union]
    ext z
    simp only [Set.mem_union,Set.mem_sdiff]
    tauto
  simp only [measureReal_def] at h
  rw [hu,hn] at h
  simpa only [measureReal_def,ENNReal.toReal_zero,add_zero] using h

end Quant.CrossedQuadrilateralDiagonalSplit

/-- info: 'Quant.CrossedQuadrilateralDiagonalSplit.gap_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralDiagonalSplit.gap_split
