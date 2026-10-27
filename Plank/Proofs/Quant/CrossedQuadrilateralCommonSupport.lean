/- Rigidity when three positive planks share a quadrilateral support diagonal. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralDiagonalSplit
public import Plank.Proofs.Quant.CommonMiddleStackUnique

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCommonSupport
open Set MeasureTheory Proofs.Transport
open CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CommonMiddleAffineTransport
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- The same opposite vertices minimize and maximize this oriented plank
form on both halves, hence on the entire quadrilateral. -/
def CommonSupports (S : Shape) (p : Plank) : Prop :=
  ∀ j, CommonExtremes (half S j) p

theorem triangle_bounds (T : Triangle) (p : Plank) (h : CommonExtremes T p)
    {z : Point} (hz : z ∈ T.set) : dot p.u T.A ≤ dot p.u z ∧ dot p.u z ≤ dot p.u T.B := by
  have hmin := min_le_dot T p.u hz
  have hmax := dot_le_max T p.u hz
  simp only [min_eq_right h.2,min_eq_left h.1] at hmin
  simp only [max_eq_left h.2,max_eq_right (h.1.trans h.2)] at hmax
  exact ⟨hmin,hmax⟩

theorem range_triangle (T : Triangle) (p : Plank) (h : CommonExtremes T p) :
    rangeWidth T.set (direction p.u) = T.width p.u := by
  rw [width_eq_span T p h]
  exact Plank.Body.width_eq_of_realisers (f := direction p.u) (mem_B T) (mem_A T)
    (fun z hz => (triangle_bounds T p h hz).2)
    (fun z hz => (triangle_bounds T p h hz).1)

theorem range_body (S : Shape) (p : Plank) (h : CommonSupports S p) :
    rangeWidth S.body (direction p.u) = span (half S true) p := by
  apply Plank.Body.width_eq_of_realisers (f := direction p.u)
    (vertexX_mem S true) (vertexX_mem S false)
  · intro z hz
    rw [body_eq_union] at hz
    rcases hz with hz | hz
    · exact (triangle_bounds (half S false) p (h false) hz).2
    · exact (triangle_bounds (half S true) p (h true) hz).2
  · intro z hz
    rw [body_eq_union] at hz
    rcases hz with hz | hz
    · exact (triangle_bounds (half S false) p (h false) hz).1
    · exact (triangle_bounds (half S true) p (h true) hz).1

/-- Splitting along the common support segment preserves every actual
relative width, not just their sum. -/
theorem relativeWidth_half (S : Shape) (p : Plank) (h : CommonSupports S p) (j : Bool) :
    p.relWidth (half S j) = relativeWidth S p := by
  simp only [Plank.relWidth,relativeWidth,width_eq_span (half S j) p (h j),range_body S p h]
  rfl

theorem product_lower_bound {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (p : Fin 3 → Plank)
    (hW : ∀ i, 0 < rangeWidth K (direction (p i).u)) :
    (max 0 (1-∑ i, ((p i).hi-(p i).lo)/rangeWidth K (direction (p i).u)))^2 *
      (volume K).toReal ≤ (volume (K \ ⋃ i, (p i).set)).toReal := by
  let C := ParallelProductPlane.coordinates
  let f (i) := ParallelProductPlane.pullForm (direction (p i).u)
  have hne' : (C ⁻¹' K).Nonempty := by
    obtain ⟨z,hz⟩ := hne
    exact ⟨C.symm z,by simpa only [Set.mem_preimage,C.apply_symm_apply] using hz⟩
  have hw (i) : rangeWidth (C ⁻¹' K) (f i) = rangeWidth K (direction (p i).u) :=
    CrossedQuadrilateralDirections.width_preimage K _
  have hg : volume ((C ⁻¹' K) \ ⋃ i, {x | (p i).lo ≤ f i x ∧ f i x ≤ (p i).hi}) =
      volume (K \ ⋃ i, (p i).set) := by
    rw [← ParallelProductPlane.volume_preimage]
    congr 1
    rw [Set.preimage_sdiff,Set.preimage_iUnion]
    rfl
  have harea : volume (C ⁻¹' K) = volume K := ParallelProductPlane.volume_preimage K
  have h := Plank.PlanarThreePlank.sharpPlanarBound_three (C ⁻¹' K)
    (ParallelProductPlane.compact_preimage hK) (hc.linear_preimage C.toLinearMap) hne'
    f (fun i => (p i).lo) (fun i => (p i).hi) (fun i => (p i).lo_le_hi)
    (fun i => by rw [hw]; exact hW i)
  simpa only [hw,hg,harea] using h

/-- Whole-body equality forces equality in each half because the actual
budgets agree and the triangle gaps add. -/
theorem half_equality (S : Shape) (p : Fin 3 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (hR : (∑ i, relativeWidth S (p i)) < 1)
    (he : (volume (S.body \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, relativeWidth S (p i))^2*(volume S.body).toReal) (j : Bool) :
    (volume ((half S j).set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth (half S j))^2*(volume (half S j).set).toReal := by
  have hb (j : Bool) :
      (1-∑ i, relativeWidth S (p i))^2*(volume (half S j).set).toReal ≤
        (volume ((half S j).set \ ⋃ i, (p i).set)).toReal := by
    have ht := product_lower_bound (compact_half S j) (convex_triangle (half S j))
      ⟨(half S j).A,mem_A (half S j)⟩ p
      (fun i => by rw [range_triangle _ _ (h i j)]; exact width_pos _ (p i).u_ne_zero)
    simp only [range_triangle _ _ (h _ j)] at ht
    change (max 0 (1-∑ i, (p i).relWidth (half S j)))^2*(volume (half S j).set).toReal ≤
      (volume ((half S j).set \ ⋃ i, (p i).set)).toReal at ht
    simp only [relativeWidth_half S _ (h _),max_eq_right (sub_pos.mpr hR).le] at ht
    exact ht
  have hm : MeasurableSet (⋃ i, (p i).set) :=
    MeasurableSet.iUnion (fun i => (Proofs.Quant.isClosed_plank_set (p i)).measurableSet)
  have hs := gap_split S (⋃ i, (p i).set) hm
  rw [he,area_split] at hs
  simp only [relativeWidth_half S _ (h _)]
  cases j <;> nlinarith only [hs,hb false,hb true]

/-- Three positive tight planks with a common support diagonal must all
be parallel to the other diagonal. Their placements and overlaps are arbitrary
in the hypotheses. -/
theorem parallel_of_equality (S : Shape) (p : Fin 3 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (hw : ∀ i, 0 < relativeWidth S (p i))
    (hR : (∑ i, relativeWidth S (p i)) < 1)
    (he : (volume (S.body \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, relativeWidth S (p i))^2*(volume S.body).toReal) :
    ∀ i, (p i).u.2 = 0 := by
  have hR0 : 0 < ∑ i, relativeWidth S (p i) :=
    Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have ht := CommonMiddleStackUnique.slope_eq_of_equalities
    (half S false) (half S true) p rfl rfl (fun i => h i false) (fun i => h i true)
    (fun i => by rw [relativeWidth_half S _ (h i)]; exact hw i)
    (by simpa only [relativeWidth_half S _ (h _)] using hR0)
    (by simpa only [relativeWidth_half S _ (h _)] using hR)
    (half_equality S p h hR he false) (half_equality S p h hR he true)
  intro i
  have hs : span (half S false) (p i) = span (half S true) (p i) := rfl
  have hp := span_pos (half S true) (p i) (h i true)
  have hh := ht i
  unfold CommonMiddleAffineTransport.slope at hh
  rw [hs] at hh
  have hh' := (div_left_inj' hp.ne').mp hh
  simp only [half,Shape.Y,Bool.false_eq_true,if_false,if_true,dot,mul_zero,zero_add,add_zero] at hh'
  have hm : (p i).u.2*(S.b+S.d) = 0 := by nlinarith only [hh']
  exact (mul_eq_zero.mp hm).resolve_right (add_pos S.hb S.hd).ne'

end Quant.CrossedQuadrilateralCommonSupport

/-- info: 'Quant.CrossedQuadrilateralCommonSupport.parallel_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCommonSupport.parallel_of_equality
