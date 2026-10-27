/- Three-plank support exclusion when the other two forms are diagonal. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSupportTripleGeometry
public import Plank.Proofs.Quant.PlanarSupportReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSupportTripleAxes
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralPlacement CrossedQuadrilateralTwoPlankCatalogue
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem reduced {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (F : Point →ᵃ[ℝ] ℝ) (G : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ K, 0 ≤ F x ∧ F x ≤ 1) (r : ℝ) (l u : Fin 2 → ℝ)
    (hr : 0 ≤ r) (ho : ∀ i, l i < u i) (hW : ∀ i, 0 < rangeWidth K (G i))
    (hR : r+∑ i, (u i-l i)/rangeWidth K (G i) < 1)
    (he : (volume (K \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪
      ⋃ i, {x | l i ≤ G i x ∧ G i x ≤ u i}))).toReal =
        (1-r-∑ i, (u i-l i)/rangeWidth K (G i))^2*(volume K).toReal) :
    (volume (K \ ⋃ i, {x | (l i-r*G i a)/(1-r) ≤ G i x ∧
      G i x ≤ (u i-r*G i a)/(1-r)})).toReal =
        (1-∑ i, ((u i-r*G i a)/(1-r)-(l i-r*G i a)/(1-r))/rangeWidth K (G i))^2*
          (volume K).toReal ∧
    K ⊆ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ ⋃ i, {x | l i ≤ G i x ∧ G i x ≤ u i}) ∪
      AffineMap.homothety a (1-r) '' K := by
  let C := ParallelProductPlane.coordinates
  let A := C ⁻¹' K
  let f := ParallelProductPlane.pullForm F
  let g (i) := ParallelProductPlane.pullForm (G i)
  have hw (i) : rangeWidth (ParallelProductPlane.coordinates ⁻¹' K) (g i) = rangeWidth K (G i) :=
    CrossedQuadrilateralDirections.width_preimage K (G i)
  have hg : volume (A \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪
      ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i})) =
    volume (K \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ ⋃ i, {x | l i ≤ G i x ∧ G i x ≤ u i})) := by
    rw [← ParallelProductPlane.volume_preimage]
    simp only [preimage_sdiff,preimage_union,preimage_iUnion]
    rfl
  have hGa (i) : g i (C.symm a) = G i a := by simp [g,C]
  obtain ⟨hp,hcover⟩ := (Plank.PlanarSupportReduction.equality_three_iff_reduced
    (ParallelProductPlane.compact_preimage hK) (hc.linear_preimage C.toLinearMap)
    (by rw [ParallelProductPlane.volume_preimage]; exact hV) f g (C.symm a) (C.symm b)
    (by simpa [A,C] using ha) (by simpa [A,C] using hb) (by simpa [f,C] using hFa)
    (by simpa [f,C] using hFb) (fun x hx => hF (C x) hx) r l u hr (fun i => (ho i).le)
    (by intro i; rw [hw]; exact hW i) (by simpa only [hw] using hR)).mp
    (by rw [hg]; simpa only [hw,ParallelProductPlane.volume_preimage] using he)
  simp only [Plank.PlanarSupportPairReduction.pulledEndpoint,hGa,hw] at hp
  have hg' : volume (A \ ⋃ i, {x | (l i-r*G i a)/(1-r) ≤ g i x ∧
      g i x ≤ (u i-r*G i a)/(1-r)}) =
    volume (K \ ⋃ i, {x | (l i-r*G i a)/(1-r) ≤ G i x ∧ G i x ≤ (u i-r*G i a)/(1-r)}) := by
    rw [← ParallelProductPlane.volume_preimage]
    simp only [preimage_sdiff,preimage_iUnion]
    rfl
  rw [hg',ParallelProductPlane.volume_preimage] at hp
  refine ⟨hp,?_⟩
  intro x hx
  have hx' : C.symm x ∈ A := by simpa [A,C] using hx
  rcases hcover hx' with (hf | hg) | hh
  · exact Or.inl (Or.inl (by simpa [f,C] using hf))
  · apply Or.inl; apply Or.inr
    obtain ⟨i,hi⟩ := mem_iUnion.mp hg
    exact mem_iUnion.mpr ⟨i,by simpa [g,C] using hi⟩
  · obtain ⟨y,hy,he⟩ := hh
    refine Or.inr ⟨C y,hy,?_⟩
    have hh := congrArg C he
    simpa only [AffineMap.homothety_apply,vadd_eq_add,vsub_eq_sub,map_add,map_sub,map_smul,
      C.apply_symm_apply] using hh

def axisForm (i : Bool) : Point →ᵃ[ℝ] ℝ := direction (vector i 1)

theorem axis_apply (i : Bool) (x : Point) : axisForm i x = coord i x := by
  cases i <;> simp [axisForm,vector,coord,dot]

theorem axis_width (S : Shape) (i : Bool) : rangeWidth S.body (axisForm i) = span S i := by
  cases i
  · exact (coordinate_widths S).1
  · exact (coordinate_widths S).2

theorem span_pos (S : Shape) (i : Bool) : 0 < span S i := by
  cases i
  · exact add_pos S.ha S.hc
  · exact add_pos S.hb S.hd

theorem two_union (G : Fin 2 → Point →ᵃ[ℝ] ℝ) (l u : Fin 2 → ℝ) :
    (⋃ i, {x | l i ≤ G i x ∧ G i x ≤ u i}) =
      {x | l 0 ≤ G 0 x ∧ G 0 x ≤ u 0} ∪ {x | l 1 ≤ G 1 x ∧ G 1 x ≤ u 1} := by
  ext x
  simp only [mem_iUnion,mem_union,Fin.exists_fin_two]

theorem reduced_axes (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (i j : Bool) (r l u l' u' : ℝ) (hr : 0 ≤ r) (ho : l < u) (ho' : l' < u')
    (hR : r+(u-l)/span S i+(u'-l')/span S j < 1)
    (he : (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band i l u ∪ band j l' u'))).toReal =
      (1-r-(u-l)/span S i-(u'-l')/span S j)^2*(volume S.body).toReal) :
    Families S i j ((l-r*coord i a)/(1-r)) ((u-r*coord i a)/(1-r))
      ((l'-r*coord j a)/(1-r)) ((u'-r*coord j a)/(1-r)) ∧
    S.body ⊆ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band i l u ∪ band j l' u') ∪
      AffineMap.homothety a (1-r) '' S.body := by
  have hs := div_pos (sub_pos.mpr ho) (span_pos S i)
  have ht := div_pos (sub_pos.mpr ho') (span_pos S j)
  have hq : 0 < 1-r := by linarith only [hR,hs,ht]
  have hlo : (l-r*coord i a)/(1-r) < (u-r*coord i a)/(1-r) :=
    (div_lt_div_iff_of_pos_right hq).mpr (sub_lt_sub_right ho _)
  have hlo' : (l'-r*coord j a)/(1-r) < (u'-r*coord j a)/(1-r) :=
    (div_lt_div_iff_of_pos_right hq).mpr (sub_lt_sub_right ho' _)
  have hw (k : Bool) (c d : ℝ) :
      ((d-r*coord k a)/(1-r)-(c-r*coord k a)/(1-r))/span S k =
        ((d-c)/span S k)/(1-r) := by ring
  have hsmall : ((u-r*coord i a)/(1-r)-(l-r*coord i a)/(1-r))/span S i+
      ((u'-r*coord j a)/(1-r)-(l'-r*coord j a)/(1-r))/span S j < 1 := by
    rw [hw,hw,← add_div]
    exact (div_lt_one hq).mpr (by linarith only [hR])
  obtain ⟨hp,hcover⟩ := reduced (compact_body S) (convex_body S) (area_body_pos S)
    F ![axisForm i,axisForm j] a b ha hb hFa hFb hF r ![l,l'] ![u,u'] hr
    (by intro k; fin_cases k; exact ho; exact ho')
    (by
      intro k; fin_cases k
      · change 0 < rangeWidth S.body (axisForm i)
        rw [axis_width]; exact span_pos S i
      · change 0 < rangeWidth S.body (axisForm j)
        rw [axis_width]; exact span_pos S j)
    (by simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,axis_width,← add_assoc] using hR)
    (by
      rw [two_union]
      simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,axis_width,axis_apply,
        band,← Set.union_assoc,sub_add_eq_sub_sub] using he)
  rw [two_union] at hp hcover
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,axis_width,axis_apply,
    ← Set.union_assoc] at hp hcover
  exact ⟨(axis_equality_iff S i j _ _ _ _ hlo hlo' hsmall).mp hp,hcover⟩

theorem pulled_calibration (A C v r l u : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hq : 0 < 1-r)
    (hbal : ((u-r*v)/(1-r))/A = -((l-r*v)/(1-r))/C) :
    l = r*v-((u-l)/(A+C))*C ∧ u = r*v+((u-l)/(A+C))*A := by
  have hh := (div_eq_div_iff hA.ne' hC.ne').mp hbal
  have hh' := congrArg (fun z : ℝ => z*(1-r)) hh
  field_simp [hq.ne'] at hh'
  constructor <;> field_simp [(add_pos hA hC).ne'] <;> nlinarith only [hh']

theorem crossed_not_equality (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (r l u l' u' : ℝ) (hr : 0 < r) (ho : l < u) (ho' : l' < u')
    (hR : r+(u-l)/(S.a+S.c)+(u'-l')/(S.b+S.d) < 1) :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band false l u ∪ band true l' u'))).toReal ≠
      (1-r-(u-l)/(S.a+S.c)-(u'-l')/(S.b+S.d))^2*(volume S.body).toReal := by
  intro he
  obtain ⟨v,hv,hFv⟩ := CrossedQuadrilateralSupport.max_vertex S F a ha hFa (fun x hx => (hF x hx).2)
  have hvm := subset_convexHull ℝ S.vertices hv
  let s := (u-l)/(S.a+S.c)
  let t := (u'-l')/(S.b+S.d)
  have hs : 0 < s := div_pos (sub_pos.mpr ho) (add_pos S.ha S.hc)
  have ht : 0 < t := div_pos (sub_pos.mpr ho') (add_pos S.hb S.hd)
  have hq : 0 < 1-r := by change r+s+t < 1 at hR; linarith only [hR,hs,ht]
  obtain ⟨hf,hcover⟩ := reduced_axes S F v b hvm hb hFv hFb hF false true r l u l' u'
    hr.le ho ho' hR he
  simp only [Families,calibrated,coord,Bool.false_eq_true,if_false,if_true] at hf
  obtain ⟨hl,hu⟩ := pulled_calibration S.a S.c v.1 r l u S.ha S.hc hq hf.1
  obtain ⟨hl',hu'⟩ := pulled_calibration S.b S.d v.2 r l' u' S.hb S.hd hq hf.2
  change l = r*v.1-s*S.c at hl
  change u = r*v.1+s*S.a at hu
  change l' = r*v.2-t*S.d at hl'
  change u' = r*v.2+t*S.b at hu'
  apply CrossedQuadrilateralSupportTripleGeometry.no_cover S F v hv hFv
    (fun x hx => (hF x hx).1) r s t hr hs ht hR
  simpa only [band,coord,if_true,Bool.false_eq_true,if_false,hl,hu,hl',hu',
    CrossedQuadrilateralSupportGeometry.band,CrossedQuadrilateralSupportTripleGeometry.yBand] using hcover

theorem joined_not_equality (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (i : Bool) (r l u l' u' : ℝ) (hr : 0 < r) (ho : l < u) (ho' : l' < u')
    (hR : r+(u-l)/span S i+(u'-l')/span S i < 1) (hjoin : u = l') :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band i l u ∪ band i l' u'))).toReal ≠
      (1-r-(u-l)/span S i-(u'-l')/span S i)^2*(volume S.body).toReal := by
  subst l'
  have hu : band i l u ∪ band i u u' = band i l u' :=
    congrArg (fun A : Set ℝ => coord i ⁻¹' A) (Set.Icc_union_Icc_eq_Icc ho.le ho'.le)
  have hw : (u-l)/span S i+(u'-u)/span S i = (u'-l)/span S i := by ring
  have hsmall : r+(u'-l)/span S i < 1 := by rw [← hw]; linarith only [hR]
  intro he
  rw [Set.union_assoc,hu] at he
  apply CrossedQuadrilateralSupport.not_equality S F (axisForm i) a b ha hb hFa hFb hF
    r l u' hr (ho.trans ho') (by rw [axis_width]; exact span_pos S i)
    (by rwa [axis_width])
  simpa only [axis_width,axis_apply,band,← hw,sub_add_eq_sub_sub] using he

theorem same_not_equality (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (i : Bool) (r l u l' u' : ℝ) (hr : 0 < r) (ho : l < u) (ho' : l' < u')
    (hR : r+(u-l)/span S i+(u'-l')/span S i < 1) :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band i l u ∪ band i l' u'))).toReal ≠
      (1-r-(u-l)/span S i-(u'-l')/span S i)^2*(volume S.body).toReal := by
  intro he
  obtain ⟨hf,_⟩ := reduced_axes S F a b ha hb hFa hFb hF i i r l u l' u' hr.le ho ho' hR he
  have hs := div_pos (sub_pos.mpr ho) (span_pos S i)
  have ht := div_pos (sub_pos.mpr ho') (span_pos S i)
  have hq : 0 < 1-r := by linarith only [hR,hs,ht]
  simp only [Families,if_true] at hf
  rcases hf with ⟨hjoin,_⟩ | ⟨hjoin,_⟩
  · have hh := congrArg (fun z : ℝ => z*(1-r)) hjoin
    simp only [div_mul_cancel₀ _ hq.ne'] at hh
    exact joined_not_equality S F a b ha hb hFa hFb hF i r l u l' u' hr ho ho' hR
      (by linarith only [hh]) he
  · have hh := congrArg (fun z : ℝ => z*(1-r)) hjoin
    simp only [div_mul_cancel₀ _ hq.ne'] at hh
    apply joined_not_equality S F a b ha hb hFa hFb hF i r l' u' l u hr ho' ho
      (by linarith only [hR]) (by linarith only [hh])
    rw [Set.union_assoc,Set.union_comm (band i l' u'),← Set.union_assoc]
    convert he using 1; ring

/-- A positive support plank and two arbitrary positive diagonal bands are
strict: the two bands may have equal or different diagonal directions. -/
theorem not_equality (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (i j : Bool) (r l u l' u' : ℝ) (hr : 0 < r) (ho : l < u) (ho' : l' < u')
    (hR : r+(u-l)/span S i+(u'-l')/span S j < 1) :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band i l u ∪ band j l' u'))).toReal ≠
      (1-r-(u-l)/span S i-(u'-l')/span S j)^2*(volume S.body).toReal := by
  cases i <;> cases j
  · exact same_not_equality S F a b ha hb hFa hFb hF false r l u l' u' hr ho ho' hR
  · exact crossed_not_equality S F a b ha hb hFa hFb hF r l u l' u' hr ho ho' hR
  · intro he
    apply crossed_not_equality S F a b ha hb hFa hFb hF r l' u' l u hr ho' ho
      (by change r+(u-l)/(S.b+S.d)+(u'-l')/(S.a+S.c)<1 at hR; linarith only [hR])
    rw [Set.union_assoc,Set.union_comm (band false l' u'),← Set.union_assoc]
    convert he using 1
    simp only [span,if_true,Bool.false_eq_true,if_false]
    ring
  · exact same_not_equality S F a b ha hb hFa hFb hF true r l u l' u' hr ho ho' hR

theorem diagonal_not_equality (S : Shape) (F G H : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ S.body) (hb : b ∈ S.body) (hFa : F a = 1) (hFb : F b = 0)
    (hF : ∀ x ∈ S.body, 0 ≤ F x ∧ F x ≤ 1)
    (hG : G.linear (1,0) = 0 ∨ G.linear (0,1) = 0)
    (hH : H.linear (1,0) = 0 ∨ H.linear (0,1) = 0)
    (r l u l' u' : ℝ) (hr : 0 < r) (ho : l < u) (ho' : l' < u')
    (hW : 0 < rangeWidth S.body G) (hW' : 0 < rangeWidth S.body H)
    (hR : r+(u-l)/rangeWidth S.body G+(u'-l')/rangeWidth S.body H < 1) :
    (volume (S.body \ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ {x | l ≤ G x ∧ G x ≤ u} ∪
      {x | l' ≤ H x ∧ H x ≤ u'}))).toReal ≠
      (1-r-(u-l)/rangeWidth S.body G-(u'-l')/rangeWidth S.body H)^2*(volume S.body).toReal := by
  obtain ⟨i,L,U,hLU,hband,hw⟩ := CrossedQuadrilateralAxisPresentation.product_axis S G l u ho hW hG
  obtain ⟨j,L',U',hLU',hband',hw'⟩ := CrossedQuadrilateralAxisPresentation.product_axis S H l' u' ho' hW' hH
  have hh := not_equality S F a b ha hb hFa hFb hF i j r L U L' U' hr hLU hLU'
    (by rwa [← hw,← hw'])
  simpa only [← hband,← hband',← hw,← hw'] using hh

end Quant.CrossedQuadrilateralSupportTripleAxes

/-- info: 'Quant.CrossedQuadrilateralSupportTripleAxes.not_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSupportTripleAxes.not_equality
