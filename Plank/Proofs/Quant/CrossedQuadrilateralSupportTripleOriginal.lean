/- Unrestricted three-positive-plank inward-support exclusion on quadrilaterals. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSupportTripleAxes

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSupportTripleOriginal
open Plank
open Set MeasureTheory PlanarQuantitative PlanarEqualityReductions PlanarParameterDomain
open CrossedQuadrilateralSupportOriginal
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem directions {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (F : Point →ᵃ[ℝ] ℝ) (g : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ K, 0 ≤ F x ∧ F x ≤ 1) (r : ℝ) (l u : Fin 2 → ℝ)
    (hr : 0 ≤ r) (ho : ∀ i, l i < u i) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hR : r+∑ i, (u i-l i)/rangeWidth K (g i) < 1)
    (he : (volume (K \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪
      ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal =
        (1-r-∑ i, (u i-l i)/rangeWidth K (g i))^2*(volume K).toReal) :
    ∃ (S : CrossedQuadrilateralAttainment.Shape) (T : Point ≃ᵃ[ℝ] Point),
      K = T '' CrossedQuadrilateralFormDirections.body S ∧
        ∀ i, (g i).linear (T.linear ![1,0]) = 0 ∨ (g i).linear (T.linear ![0,1]) = 0 := by
  obtain ⟨hp,_⟩ := (PlanarSupportReduction.equality_three_iff_reduced
    (genuine_compact hG) (genuine_convex hG) hV F g a b ha hb hFa hFb hF r l u
    hr (fun i => (ho i).le) hW hR).mp he
  let p : Endpoints 2 :=
    (fun i => PlanarSupportPairReduction.pulledEndpoint (g i) a r (l i),
      fun i => PlanarSupportPairReduction.pulledEndpoint (g i) a r (u i))
  have hs : 0 ≤ ∑ i, (u i-l i)/rangeWidth K (g i) :=
    Finset.sum_nonneg fun i _ => div_nonneg (sub_pos.mpr (ho i)).le (hW i).le
  have hq : 0 < 1-r := by linarith only [hR,hs]
  have hw : budget K g p = (∑ i, (u i-l i)/rangeWidth K (g i))/(1-r) := by
    simp only [budget,p,PlanarSupportPairReduction.pulled_relativeWidth]
    exact (Finset.sum_div _ _ _).symm
  have hsmall : budget K g p < 1 := by
    rw [hw]
    exact (div_lt_one hq).mpr (by linarith only [hR])
  have hord (i) : p.1 i < p.2 i := by
    apply sub_pos.mp
    change 0 < PlanarSupportPairReduction.pulledEndpoint (g i) a r (u i)-
      PlanarSupportPairReduction.pulledEndpoint (g i) a r (l i)
    rw [PlanarSupportPairReduction.pulled_width]
    exact div_pos (sub_pos.mpr (ho i)) hq
  have hpE : Equality K g p := by
    unfold Equality
    rw [max_eq_right (sub_pos.mpr hsmall).le]
    exact hp
  exact CrossedQuadrilateralTwoPlankDirections.original hG hV g p hW hord hsmall hpE

theorem model_not_equality (S : CrossedQuadrilateralAttainment.Shape)
    (F G H : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ CrossedQuadrilateralFormDirections.body S)
    (hb : b ∈ CrossedQuadrilateralFormDirections.body S) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ CrossedQuadrilateralFormDirections.body S, 0 ≤ F x ∧ F x ≤ 1)
    (hG : G.linear ![1,0] = 0 ∨ G.linear ![0,1] = 0)
    (hH : H.linear ![1,0] = 0 ∨ H.linear ![0,1] = 0)
    (r l u l' u' : ℝ) (hr : 0 < r) (ho : l < u) (ho' : l' < u')
    (hW : 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) G)
    (hW' : 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) H)
    (hR : r+(u-l)/rangeWidth (CrossedQuadrilateralFormDirections.body S) G+
      (u'-l')/rangeWidth (CrossedQuadrilateralFormDirections.body S) H < 1) :
    (volume (CrossedQuadrilateralFormDirections.body S \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪
      {x | l ≤ G x ∧ G x ≤ u} ∪ {x | l' ≤ H x ∧ H x ≤ u'}))).toReal ≠
      (1-r-(u-l)/rangeWidth (CrossedQuadrilateralFormDirections.body S) G-
        (u'-l')/rangeWidth (CrossedQuadrilateralFormDirections.body S) H)^2*
          (volume (CrossedQuadrilateralFormDirections.body S)).toReal := by
  let C := ParallelProductPlane.coordinates
  have hw (J : Point →ᵃ[ℝ] ℝ) : rangeWidth S.body (productForm J) =
      rangeWidth (CrossedQuadrilateralFormDirections.body S) J := by
    rw [← CrossedQuadrilateralDirections.width_preimage,product_pull]
  have hg : volume (CrossedQuadrilateralFormDirections.body S \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪
      {x | l ≤ G x ∧ G x ≤ u} ∪ {x | l' ≤ H x ∧ H x ≤ u'})) =
      volume (S.body \ ({x | 0 ≤ productForm F x ∧ productForm F x ≤ r} ∪
        {x | l ≤ productForm G x ∧ productForm G x ≤ u} ∪
        {x | l' ≤ productForm H x ∧ productForm H x ≤ u'})) := by
    rw [← ParallelProductPlane.volume_preimage]
    congr 1
    ext x
    change (C x ∈ S.body ∧ ¬((0 ≤ F x ∧ F x ≤ r ∨ l ≤ G x ∧ G x ≤ u) ∨ l' ≤ H x ∧ H x ≤ u')) ↔
      (C x ∈ S.body ∧ ¬((0 ≤ F (C.symm (C x)) ∧ F (C.symm (C x)) ≤ r ∨
        l ≤ G (C.symm (C x)) ∧ G (C.symm (C x)) ≤ u) ∨
        l' ≤ H (C.symm (C x)) ∧ H (C.symm (C x)) ≤ u'))
    rw [C.symm_apply_apply]
  intro he
  apply CrossedQuadrilateralSupportTripleAxes.diagonal_not_equality S
    (productForm F) (productForm G) (productForm H) (C a) (C b) ha hb
    (by simpa [productForm,C] using hFa) (by simpa [productForm,C] using hFb)
    (fun x hx => by simpa [productForm,C] using hF (C.symm x) (by simpa [C] using hx))
    hG hH r l u l' u' hr ho ho' (by rwa [hw]) (by rwa [hw]) (by rwa [hw,hw])
  rwa [← hg,hw,hw,← ParallelProductPlane.volume_preimage]

theorem two_union (g : Fin 2 → Point →ᵃ[ℝ] ℝ) (l u : Fin 2 → ℝ) :
    (⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}) =
      {x | l 0 ≤ g 0 x ∧ g 0 x ≤ u 0} ∪ {x | l 1 ≤ g 1 x ∧ g 1 x ≤ u 1} := by
  ext x
  simp only [mem_iUnion,mem_union,Fin.exists_fin_two]

/-- No direction or overlap hypothesis is supplied on the two other planks.
All three widths are positive, and the first plank starts at the minimum. -/
theorem normalized_not_equality {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (F : Point →ᵃ[ℝ] ℝ) (g : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ K, 0 ≤ F x ∧ F x ≤ 1) (r : ℝ) (l u : Fin 2 → ℝ)
    (hr : 0 < r) (ho : ∀ i, l i < u i) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hR : r+∑ i, (u i-l i)/rangeWidth K (g i) < 1) :
    (volume (K \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪
      ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal ≠
        (1-r-∑ i, (u i-l i)/rangeWidth K (g i))^2*(volume K).toReal := by
  intro he
  obtain ⟨S,T,rfl,hd⟩ := directions hG hV F g a b ha hb hFa hFb hF r l u hr.le ho hW hR he
  let A := CrossedQuadrilateralFormDirections.body S
  let f := CrossedQuadrilateralImageStrata.pre T F
  let gs (i) := CrossedQuadrilateralImageStrata.pre T (g i)
  have hw (i) : rangeWidth A (gs i) = rangeWidth (T '' A) (g i) :=
    CrossedQuadrilateralImageStrata.width_pre T A (g i)
  have hgap : T '' (A \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪
      ⋃ i, {x | l i ≤ gs i x ∧ gs i x ≤ u i})) =
    (T '' A) \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨mem_image_of_mem T hy.1,by
        simpa only [mem_union,mem_iUnion,mem_ofPred_eq,f,gs,CrossedQuadrilateralImageStrata.pre_apply] using hy.2⟩
    · rintro ⟨⟨y,hy,rfl⟩,hn⟩
      exact ⟨y,⟨hy,by
        simpa only [mem_union,mem_iUnion,mem_ofPred_eq,f,gs,CrossedQuadrilateralImageStrata.pre_apply] using hn⟩,rfl⟩
  have hpre {x : Point} (hx : x ∈ T '' A) : T.symm x ∈ A := by
    obtain ⟨y,hy,rfl⟩ := hx
    simpa using hy
  change (volume ((T '' A) \ _)).toReal = _ at he
  rw [← hgap,CrossedQuadrilateralImageStrata.area_image,CrossedQuadrilateralImageStrata.area_image] at he
  have heA : (volume (A \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪
      ⋃ i, {x | l i ≤ gs i x ∧ gs i x ≤ u i}))).toReal =
      (1-r-∑ i, (u i-l i)/rangeWidth (T '' A) (g i))^2*(volume A).toReal := by
    apply mul_left_cancel₀ (CrossedQuadrilateralImageStrata.factor_pos T).ne'
    nlinarith only [he]
  apply model_not_equality S f (gs 0) (gs 1) (T.symm a) (T.symm b) (hpre ha) (hpre hb)
    (by simpa [f] using hFa) (by simpa [f] using hFb)
    (fun x hx => hF (T x) (mem_image_of_mem T hx)) (hd 0) (hd 1) r (l 0) (u 0) (l 1) (u 1)
    hr (ho 0) (ho 1) (by rw [hw]; exact hW 0) (by rw [hw]; exact hW 1)
    (by rw [hw,hw]; simpa only [Fin.sum_univ_two,← add_assoc] using hR)
  simpa only [two_union,← Set.union_assoc,Fin.sum_univ_two,sub_add_eq_sub_sub,← hw] using heA

theorem lower_support_not_equality {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Point →ᵃ[ℝ] ℝ) (g : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo hi : ℝ) (l u : Fin 2 → ℝ) (hbase : f b = lo)
    (horder : lo < hi) (ho : ∀ i, l i < u i)
    (hWf : 0 < rangeWidth K f) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hR : (hi-lo)/rangeWidth K f+∑ i, (u i-l i)/rangeWidth K (g i) < 1) :
    (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪ ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal ≠
      (1-(hi-lo)/rangeWidth K f-∑ i, (u i-l i)/rangeWidth K (g i))^2*(volume K).toReal := by
  let F : Point →ᵃ[ℝ] ℝ := (rangeWidth K f)⁻¹ • (f-AffineMap.const ℝ Point lo)
  let r := (hi-lo)/rangeWidth K f
  have hFeval (x) : F x = (f x-lo)/rangeWidth K f := by simp [F,div_eq_mul_inv,mul_comm]
  have hw : rangeWidth K f = f a-lo := by
    have hh : rangeWidth K f = f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
    rwa [hbase] at hh
  have hFa : F a = 1 := by rw [hFeval,← hw,div_self hWf.ne']
  have hFb : F b = 0 := by rw [hFeval,hbase,sub_self,zero_div]
  have hF (x) (hx : x ∈ K) : 0 ≤ F x ∧ F x ≤ 1 := by
    rw [hFeval]
    refine ⟨div_nonneg (sub_nonneg.mpr (by rw [← hbase]; exact hmin x hx)) hWf.le,?_⟩
    rw [div_le_one hWf,hw]
    exact sub_le_sub_right (hmax x hx) _
  have hband : {x | 0 ≤ F x ∧ F x ≤ r} = {x | lo ≤ f x ∧ f x ≤ hi} := by
    ext x
    change (0 ≤ F x ∧ F x ≤ r) ↔ _
    rw [hFeval]
    dsimp only [r]
    rw [div_le_div_iff_of_pos_right hWf]
    simp only [le_div_iff₀ hWf,zero_mul,sub_nonneg,sub_le_sub_iff_right,mem_ofPred_eq]
  have hh := normalized_not_equality hG hV F g a b ha hb hFa hFb hF r l u
    (div_pos (sub_pos.mpr horder) hWf) ho hW hR
  rwa [hband] at hh

/-- Three positive physical planks cannot be sharp on a genuine quadrilateral
if one starts at its minimum or ends at its maximum. The other two directions,
placements, intersections and closed-cell degeneracies are unrestricted. -/
theorem support_strict {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Point →ᵃ[ℝ] ℝ) (g : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x)
    (lo hi : ℝ) (l u : Fin 2 → ℝ) (hface : f b = lo ∨ f a = hi)
    (horder : lo < hi) (ho : ∀ i, l i < u i)
    (hWf : 0 < rangeWidth K f) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hR : (hi-lo)/rangeWidth K f+∑ i, (u i-l i)/rangeWidth K (g i) < 1) :
    (1-(hi-lo)/rangeWidth K f-∑ i, (u i-l i)/rangeWidth K (g i))^2*(volume K).toReal <
      (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪ ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal := by
  have hneq : (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪
      ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal ≠
      (1-(hi-lo)/rangeWidth K f-∑ i, (u i-l i)/rangeWidth K (g i))^2*(volume K).toReal := by
    rcases hface with hf | hf
    · exact lower_support_not_equality hG hV f g a b ha hb hmax hmin lo hi l u hf horder ho hWf hW hR
    · have hw : rangeWidth K (-f) = rangeWidth K f :=
        Body.width_neg (genuine_compact hG) ⟨a,ha⟩ (PlanarGapCells.continuous_form f)
      have hband : {x | -hi ≤ (-f) x ∧ (-f) x ≤ -lo} = {x | lo ≤ f x ∧ f x ≤ hi} := by
        ext x
        change (-hi ≤ -f x ∧ -f x ≤ -lo) ↔ _
        constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]
      have hh := lower_support_not_equality hG hV (-f) g b a hb ha
        (fun x hx => by simpa using neg_le_neg (hmin x hx))
        (fun x hx => by simpa using neg_le_neg (hmax x hx)) (-hi) (-lo) l u
        (by simpa using congrArg Neg.neg hf) (neg_lt_neg horder) ho (by rwa [hw]) hW
        (by simpa only [hw,neg_sub_neg] using hR)
      simpa only [hband,hw,neg_sub_neg] using hh
  have hbound := PlanarThreePlank.sharpPlanarBound_three K (genuine_compact hG) (genuine_convex hG)
    ⟨a,ha⟩ (Fin.cons f g) (Fin.cons lo l) (Fin.cons hi u)
    (by intro i; refine Fin.cases ?_ (fun j => ?_) i; exact horder.le; exact (ho j).le)
    (by intro i; refine Fin.cases ?_ (fun j => ?_) i; exact hWf; exact hW j)
  have hu : (⋃ i : Fin 3, {x : Point | (Fin.cons lo l : Fin 3 → ℝ) i ≤
      ((Fin.cons f g : Fin 3 → Point →ᵃ[ℝ] ℝ) i) x ∧
      ((Fin.cons f g : Fin 3 → Point →ᵃ[ℝ] ℝ) i) x ≤ (Fin.cons hi u : Fin 3 → ℝ) i}) =
      {x | lo ≤ f x ∧ f x ≤ hi} ∪ ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i} := by
    ext x
    simp only [mem_iUnion,Fin.exists_fin_succ,Fin.cons_zero,Fin.cons_succ,mem_union]
  rw [Fin.sum_univ_succ] at hbound
  simp only [Fin.cons_zero,Fin.cons_succ,sub_add_eq_sub_sub] at hbound
  rw [hu,max_eq_right (by linarith only [hR] :
    0 ≤ 1-(hi-lo)/rangeWidth K f-∑ i, (u i-l i)/rangeWidth K (g i))] at hbound
  exact lt_of_le_of_ne hbound hneq.symm

end Quant.CrossedQuadrilateralSupportTripleOriginal

/-- info: 'Quant.CrossedQuadrilateralSupportTripleOriginal.support_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSupportTripleOriginal.support_strict
