/- Boundary segments crossing an open strip bound its extreme points before
any polyhedrality hypothesis. -/
module
public import Plank.Proofs.Quant.PlanarStripVertices
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarBoundaryStrip

open Set PlanarStripVertices
open scoped Topology

/-- Every boundary point in the open strip has a boundary segment reaching
outside that strip. Endpoints on its walls are allowed. -/
def ReachesBoundary (K : Set Plane) (a b : ℝ) : Prop :=
  ∀ p ∈ frontier K, p.1 ∈ Ioo a b →
    ∃ z ∈ frontier K, z.1 ∉ Ioo a b ∧ segment ℝ p z ⊆ frontier K

theorem linear_coordinates (f : Plane →ₗ[ℝ] ℝ) (x : Plane) :
    f x = x.1 * f (1,0) + x.2 * f (0,1) := by
  have hx : x = x.1 • ((1,0) : Plane) + x.2 • ((0,1) : Plane) := by
    ext <;> simp
  calc f x = f (x.1 • ((1,0) : Plane) + x.2 • ((0,1) : Plane)) := congrArg f hx
       _ = _ := by simp only [map_add,map_smul,smul_eq_mul]

/-- A nonconstant linear form constant on two horizontally separated points
has nonzero vertical coefficient. -/
theorem vertical_ne_zero (f : Plane →L[ℝ] ℝ) (hf : f ≠ 0)
    {u v : Plane} (huv : u.1 < v.1) (he : f u = f v) : f (0,1) ≠ 0 := by
  intro hz
  have h₁ := linear_coordinates f.toLinearMap u
  have h₂ := linear_coordinates f.toLinearMap v
  have he₁ : f (1,0) = 0 := by
    change f u = u.1 * f (1,0) + u.2 * f (0,1) at h₁
    change f v = v.1 * f (1,0) + v.2 * f (0,1) at h₂
    rw [hz, mul_zero, add_zero] at h₁ h₂
    have hmul : (v.1-u.1) * f (1,0) = 0 := by nlinarith [he]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_pos.mpr huv).ne'
  apply hf
  apply ContinuousLinearMap.ext
  intro x
  simpa [he₁,hz] using linear_coordinates f.toLinearMap x

/-- An extreme point on a nonvertical supporting line cannot lie between
two other points of the body on that line. -/
theorem not_straddle_face_extreme {K : Set Plane}
    (f : Plane →ᵃ[ℝ] ℝ) (hvert : f.linear (0,1) ≠ 0) {u p q : Plane}
    (hu : u ∈ K.extremePoints ℝ) (hp : p∈K) (hq : q∈K)
    (hfp : f p=f u) (hfq : f q=f u) (hpu : p.1<u.1) (huq : u.1<q.1) : False := by
  let t := (u.1-p.1)/(q.1-p.1)
  have hd : 0<q.1-p.1 := by linarith
  have ht0 : 0<t := div_pos (by linarith) hd
  have ht1 : t<1 := (div_lt_one hd).mpr (by linarith)
  have ht : t*(q.1-p.1)=u.1-p.1 := div_mul_cancel₀ _ hd.ne'
  let r := AffineMap.lineMap p q t
  have hrseg : r∈openSegment ℝ p q := lineMap_mem_openSegment ℝ p q ⟨ht0,ht1⟩
  have hrx : r.1=u.1 := by
    change (AffineMap.lineMap p q t).1=u.1
    rw [AffineMap.lineMap_apply_module']
    change t*(q.1-p.1)+p.1=u.1
    linarith only [ht]
  have hfr : f r=f u := by
    dsimp [r]
    rw [f.apply_lineMap,hfp,hfq,AffineMap.lineMap_same_apply]
  have hy : r.2=u.2 := by
    have h := vertical_difference f hrx
    rw [hfr,sub_self] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_right hvert)
  have hru : r=u := Prod.ext hrx hy
  have he := hu.2 hp hq (hru ▸ hrseg)
  have := congrArg Prod.fst he
  linarith

theorem upper_mem_frontier {K : Set Plane} (hK : IsClosed K)
    {p : Plane} (hp : p∈K) (hu : Upper K p) : p∈frontier K := by
  rw [hK.frontier_eq]
  refine ⟨hp,?_⟩
  intro hpi
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hpi)
  have hq : (p.1,p.2+r/2)∈K := interior_subset (hball (by
    rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    simp only [sub_self,abs_zero,add_sub_cancel_left,abs_of_pos (half_pos hr)]
    rw [max_eq_right (half_pos hr).le]
    linarith))
  have := hu _ hq rfl
  change p.2+r/2≤p.2 at this
  linarith

/-- Separate a boundary segment from the body's interior. -/
theorem supporting_segment {K : Set Plane} (hK : IsClosed K) (hc : Convex ℝ K)
    (hint : (interior K).Nonempty) {p z : Plane}
    (hs : segment ℝ p z⊆frontier K) :
    ∃ f : Plane →L[ℝ] ℝ, f≠0 ∧ (∀ x∈K,f x≤f p) ∧ f z=f p := by
  have hd : Disjoint (interior K) (segment ℝ p z) := by
    refine disjoint_left.mpr fun x hx hxs => ?_
    exact (hs hxs).2 hx
  obtain ⟨f,b,hf,hside,hseg⟩ := geometric_hahn_banach_of_nonempty_interior
    hc (convex_segment p z) hd hint ⟨p,left_mem_segment _ _ _⟩
  have hp := hs (left_mem_segment ℝ p z)
  have hz := hs (right_mem_segment ℝ p z)
  have hfp : f p=b := le_antisymm (hside p (hK.closure_eq ▸ hp.1))
    (hseg p (left_mem_segment _ _ _))
  have hfz : f z=b := le_antisymm (hside z (hK.closure_eq ▸ hz.1))
    (hseg z (right_mem_segment _ _ _))
  exact ⟨f,hf,fun x hx => (hside x hx).trans hfp.ge,hfz.trans hfp.symm⟩

/-- The open strip has at most one upper extreme point, without assuming
the body is a polygon. -/
theorem upper_extremes_subsingleton {K : Set Plane} (hK : IsCompact K)
    (hc : Convex ℝ K) (hint : (interior K).Nonempty) (a b : ℝ)
    (hrule : ReachesBoundary K a b) :
    {u | u∈K.extremePoints ℝ ∧ u.1∈Ioo a b ∧ Upper K u}.Subsingleton := by
  have hnot {u v : Plane} (hu : u∈K.extremePoints ℝ) (hv : v∈K.extremePoints ℝ)
      (huab : u.1∈Ioo a b) (hvab : v.1∈Ioo a b)
      (hupp : Upper K u) (hvpp : Upper K v) (huv : u.1<v.1) : False := by
    let c := (u.1+v.1)/2
    let M := K∩{x : Plane | x.1=c}
    let r := AffineMap.lineMap u v (1/2 : ℝ)
    have hrK : r∈K := hc.openSegment_subset hu.1 hv.1
      (lineMap_mem_openSegment ℝ u v (by norm_num))
    have hrx : r.1=c := by
      dsimp [r,c]
      rw [AffineMap.lineMap_apply_module']
      change (1/2 : ℝ)*(v.1-u.1)+u.1=(u.1+v.1)/2
      ring
    have hM : IsCompact M := hK.inter_right (isClosed_eq continuous_fst continuous_const)
    obtain ⟨p,hp,hmax⟩ := hM.exists_isMaxOn ⟨r,hrK,hrx⟩ continuous_snd.continuousOn
    have hupper : Upper K p := fun x hx hxp => hmax ⟨hx,hxp.trans hp.2⟩
    have hup : u.1<p.1 := by have := hp.2; dsimp [c] at this; linarith
    have hpv : p.1<v.1 := by have := hp.2; dsimp [c] at this; linarith
    have hpab : p.1∈Ioo a b := ⟨huab.1.trans hup,hpv.trans hvab.2⟩
    obtain ⟨z,hz,hzab,hseg⟩ := hrule p (upper_mem_frontier hK.isClosed hp.1 hupper) hpab
    have hzK : z∈K := hK.isClosed.closure_eq ▸ hz.1
    obtain ⟨f,hf,hside,hfz⟩ := supporting_segment hK.isClosed hc hint hseg
    let F := f.toLinearMap.toAffineMap
    have hfpx : F p=f p := rfl
    have hfzx : F z=f p := hfz
    have hlowhigh : z.1≤a ∨ b≤z.1 := by
      by_cases hza : z.1≤a
      · exact Or.inl hza
      · exact Or.inr (le_of_not_gt fun hzb => hzab ⟨lt_of_not_ge hza,hzb⟩)
    by_cases hpos : 0<f (0,1)
    · rcases hlowhigh with hza | hzb
      · exact not_straddle_upper_extreme hc F (f p) hside hpos hu hupp
          hzK hp.1 hfzx hfpx (hza.trans_lt huab.1) hup
      · exact not_straddle_upper_extreme hc F (f p) hside hpos hv hvpp
          hp.1 hzK hfpx hfzx hpv (hvab.2.trans_le hzb)
    · have hry : r.2≤p.2 := hupper r hrK (hrx.trans hp.2.symm)
      have hmul := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hry) (le_of_not_gt hpos)
      have hdiff := vertical_difference F (hrx.trans hp.2.symm)
      have hfr : f r=f p := le_antisymm (hside r hrK) (by
        change F r-F p=(r.2-p.2)*f (0,1) at hdiff
        change 0≤(r.2-p.2)*f (0,1) at hmul
        change F p≤F r
        linarith)
      have hmid : f r=(f u+f v)/2 := by
        dsimp [r]
        rw [AffineMap.lineMap_apply_module']
        simp only [map_add,map_smul,map_sub,smul_eq_mul]
        ring
      have hfu : f u=f p := by linarith [hside u hu.1,hside v hv.1]
      have hfv : f v=f p := by linarith [hside u hu.1,hside v hv.1]
      have hvert : F.linear (0,1)≠0 := vertical_ne_zero f hf huv (hfu.trans hfv.symm)
      rcases hlowhigh with hza | hzb
      · exact not_straddle_face_extreme F hvert hu hzK hp.1
          (hfz.trans hfu.symm) hfu.symm (hza.trans_lt huab.1) hup
      · exact not_straddle_face_extreme F hvert hv hp.1 hzK
          hfv.symm (hfz.trans hfv.symm) hpv (hvab.2.trans_le hzb)
  intro u hu v hv
  rcases lt_trichotomy u.1 v.1 with hlt | heq | hgt
  · exact (hnot hu.1 hv.1 hu.2.1 hv.2.1 hu.2.2 hv.2.2 hlt).elim
  · exact Prod.ext heq (le_antisymm (hv.2.2 u hu.1.1 heq) (hu.2.2 v hv.1.1 heq.symm))
  · exact (hnot hv.1 hu.1 hv.2.1 hu.2.1 hv.2.2 hu.2.2 hgt).elim

/-- Reflection supplies the lower-boundary half of the strip count. -/
theorem lower_extremes_subsingleton {K : Set Plane} (hK : IsCompact K)
    (hc : Convex ℝ K) (hint : (interior K).Nonempty) (a b : ℝ)
    (hrule : ReachesBoundary K a b) :
    {u | u∈K.extremePoints ℝ ∧ u.1∈Ioo a b ∧ Lower K u}.Subsingleton := by
  let N : Plane ≃ₗ[ℝ] Plane := LinearEquiv.neg ℝ
  let M := N '' K
  have hmem (x : Plane) : x∈M ↔ -x∈K := by
    constructor
    · rintro ⟨y,hy,rfl⟩; simpa [N] using hy
    · intro hx; exact ⟨-x,hx,by simp [N]⟩
  have hfront : N '' frontier K=frontier M :=
    N.toContinuousLinearEquiv.toHomeomorph.image_frontier K
  have hfrontmem (x : Plane) : x∈frontier M ↔ -x∈frontier K := by
    rw [←hfront]
    constructor
    · rintro ⟨y,hy,rfl⟩; simpa [N] using hy
    · intro hx; exact ⟨-x,hx,by simp [N]⟩
  have hM : IsCompact M := hK.image N.continuous_of_finiteDimensional
  have hcM : Convex ℝ M := hc.linear_image N.toLinearMap
  have hintM : (interior M).Nonempty := by
    have he : N '' interior K=interior M :=
      N.toContinuousLinearEquiv.toHomeomorph.image_interior K
    exact he ▸ hint.image N
  have hruleM : ReachesBoundary M (-b) (-a) := by
    intro p hp hpab
    have hp' : (-p).1∈Ioo a b := by
      change a < -p.1 ∧ -p.1 < b
      constructor <;> linarith [hpab.1,hpab.2]
    obtain ⟨z,hz,hzab,hseg⟩ := hrule (-p) ((hfrontmem p).mp hp) hp'
    refine ⟨-z,(hfrontmem (-z)).mpr (by simpa using hz),?_,?_⟩
    · intro hab
      apply hzab
      change -b < -z.1 ∧ -z.1 < -a at hab
      constructor <;> linarith [hab.1,hab.2]
    · have he : segment ℝ p (-z)=N '' segment ℝ (-p) z := by
        simpa [N] using (image_segment ℝ N.toAffineEquiv.toAffineMap (-p) z).symm
      rw [he,←hfront]
      exact image_mono hseg
  have hsub := upper_extremes_subsingleton hM hcM hintM (-b) (-a) hruleM
  have ht (u : Plane) (hu : u∈K.extremePoints ℝ ∧ u.1∈Ioo a b ∧ Lower K u) :
      -u∈M.extremePoints ℝ ∧ (-u).1∈Ioo (-b) (-a) ∧ Upper M (-u) := by
    refine ⟨?_,?_,?_⟩
    · rw [←image_extremePoints N K]
      exact ⟨u,hu.1,rfl⟩
    · change -b < -u.1 ∧ -u.1 < -a
      constructor <;> linarith [hu.2.1.1,hu.2.1.2]
    · intro x hx hxu
      have hfirst : (-x).1=u.1 := by
        change -x.1=u.1
        change x.1 = -u.1 at hxu
        linarith
      have hh := hu.2.2 (-x) ((hmem x).mp hx) hfirst
      change u.2 ≤ -x.2 at hh
      change x.2 ≤ -u.2
      linarith
  intro u hu v hv
  exact neg_injective (hsub (ht u hu) (ht v hv))

theorem finite_ncard_le_two_of_halves {K A : Set Plane}
    (hA : A⊆K.extremePoints ℝ)
    (hU : {u | u∈A ∧ Upper K u}.Subsingleton)
    (hL : {u | u∈A ∧ Lower K u}.Subsingleton) : A.Finite ∧ A.ncard≤2 := by
  let U := {u | u∈A ∧ Upper K u}
  let L := {u | u∈A ∧ Lower K u}
  have hsub : A⊆U∪L := by
    intro x hx
    rcases extreme_upper_or_lower (hA hx) with hu | hl
    · exact Or.inl ⟨hx,hu⟩
    · exact Or.inr ⟨hx,hl⟩
  have hfin := hU.finite.union hL.finite
  refine ⟨hfin.subset hsub,(ncard_le_ncard hsub hfin).trans ?_⟩
  exact (ncard_union_le U L).trans (Nat.add_le_add
    ((ncard_le_one hU.finite).mpr hU) ((ncard_le_one hL.finite).mpr hL))

/-- At most two extreme points lie in an open strip crossed by boundary
segments. No finite-face description is an input. -/
theorem open_strip_extremes {K : Set Plane} (hK : IsCompact K)
    (hc : Convex ℝ K) (hint : (interior K).Nonempty) (a b : ℝ)
    (hrule : ReachesBoundary K a b) :
    (K.extremePoints ℝ∩{x | x.1∈Ioo a b}).Finite ∧
      (K.extremePoints ℝ∩{x | x.1∈Ioo a b}).ncard≤2 := by
  apply finite_ncard_le_two_of_halves inter_subset_left
  · simpa only [mem_inter_iff,mem_ofPred_eq,and_assoc] using
      upper_extremes_subsingleton hK hc hint a b hrule
  · simpa only [mem_inter_iff,mem_ofPred_eq,and_assoc] using
      lower_extremes_subsingleton hK hc hint a b hrule

/-- A vertical line contains at most two extreme points of any planar set. -/
theorem line_extremes (K : Set Plane) (a : ℝ) :
    (K.extremePoints ℝ∩{x | x.1=a}).Finite ∧
      (K.extremePoints ℝ∩{x | x.1=a}).ncard≤2 := by
  apply finite_ncard_le_two_of_halves inter_subset_left
  · intro u hu v hv
    have hx : u.1=v.1 := hu.1.2.trans hv.1.2.symm
    exact Prod.ext hx (le_antisymm (hv.2 u hu.1.1.1 hx) (hu.2 v hv.1.1.1 hx.symm))
  · intro u hu v hv
    have hx : u.1=v.1 := hu.1.2.trans hv.1.2.symm
    exact Prod.ext hx (le_antisymm (hu.2 v hv.1.1.1 hx.symm) (hv.2 u hu.1.1.1 hx))

/-- Adding the two walls gives a coarse six-point closed-strip bound. This
is used to deduce polygonality before applying a sharper facet variation. -/
theorem closed_strip_extremes {K : Set Plane} (hK : IsCompact K)
    (hc : Convex ℝ K) (hint : (interior K).Nonempty) (a b : ℝ)
    (hrule : ReachesBoundary K a b) :
    (K.extremePoints ℝ∩{x | x.1∈Icc a b}).Finite ∧
      (K.extremePoints ℝ∩{x | x.1∈Icc a b}).ncard≤6 := by
  let A := K.extremePoints ℝ∩{x | x.1∈Ioo a b}
  let L := K.extremePoints ℝ∩{x | x.1=a}
  let R := K.extremePoints ℝ∩{x | x.1=b}
  have hA := open_strip_extremes hK hc hint a b hrule
  have hL := line_extremes K a
  have hR := line_extremes K b
  have hsub : K.extremePoints ℝ∩{x | x.1∈Icc a b}⊆A∪(L∪R) := by
    intro x hx
    by_cases hl : x.1=a
    · exact Or.inr (Or.inl ⟨hx.1,hl⟩)
    by_cases hr : x.1=b
    · exact Or.inr (Or.inr ⟨hx.1,hr⟩)
    exact Or.inl ⟨hx.1,lt_of_le_of_ne hx.2.1 (Ne.symm hl),lt_of_le_of_ne hx.2.2 hr⟩
  have hfin : (A∪(L∪R)).Finite := hA.1.union (hL.1.union hR.1)
  refine ⟨hfin.subset hsub,(ncard_le_ncard hsub hfin).trans ?_⟩
  have h₁ := ncard_union_le A (L∪R)
  have h₂ := ncard_union_le L R
  dsimp [A,L,R] at *
  omega

end Plank.PlanarBoundaryStrip
