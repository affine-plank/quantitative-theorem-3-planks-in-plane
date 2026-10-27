/- The calibrated single-band family, with two arbitrary null planks. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralTripleCatalogue
public import Plank.Proofs.Quant.PlanarSingleActivePlank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSingleCatalogue
open Plank Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarEqualityReductions
open CrossedQuadrilateralImageStrata CrossedQuadrilateralAxisPresentation
open CrossedQuadrilateralTwoPlankCatalogue CrossedQuadrilateralSupportOriginal
open Plank.Convex.DeficientHeightTilt

/-- A complete original-coordinate description of one calibrated diagonal band. -/
structure Presentation (K : Set Native) (f : Native →ᵃ[ℝ] ℝ) (lo hi : ℝ) where
  shape : CrossedQuadrilateralAttainment.Shape
  chart : Native ≃ᵃ[ℝ] Native
  axis : Bool
  lower : ℝ
  upper : ℝ
  body : K = chart '' CrossedQuadrilateralFormDirections.body shape
  ordered : lower < upper
  band : {x | lo ≤ f x ∧ f x ≤ hi} = chart '' nativeBand axis lower upper
  width : (hi-lo)/rangeWidth K f = (upper-lower)/span shape axis

def Presentation.calibrated {K : Set Native} {f : Native →ᵃ[ℝ] ℝ} {lo hi : ℝ}
    (D : Presentation K f lo hi) : Prop :=
  CrossedQuadrilateralTwoPlankCatalogue.calibrated D.shape D.axis D.lower D.upper

theorem axis_single_iff (S : CrossedQuadrilateralAttainment.Shape) (i : Bool) (l u : ℝ)
    (ho : l < u) (hR : (u-l)/span S i < 1) :
    (volume (S.body \ CrossedQuadrilateralPlacement.band i l u)).toReal =
      (1-(u-l)/span S i)^2*(volume S.body).toReal ↔
      CrossedQuadrilateralTwoPlankCatalogue.calibrated S i l u := by
  cases i
  · have he := CrossedQuadrilateralPlacement.arbitrary_placement_equality_iff S l u 0 0
      ho.le le_rfl (by simpa [span] using hR)
    rw [← Set.sdiff_sdiff,measure_sdiff_null (CrossedQuadrilateralPlacement.volume_band_null true 0)] at he
    simpa [span,CrossedQuadrilateralTwoPlankCatalogue.calibrated,ne_of_gt ho] using he
  · have he := CrossedQuadrilateralPlacement.arbitrary_placement_equality_iff S 0 0 l u
      le_rfl ho.le (by simpa [span] using hR)
    rw [Set.union_comm,← Set.sdiff_sdiff,
      measure_sdiff_null (CrossedQuadrilateralPlacement.volume_band_null false 0)] at he
    simpa [span,CrossedQuadrilateralTwoPlankCatalogue.calibrated,ne_of_gt ho] using he

theorem Presentation.equality_iff {K : Set Native} {f : Native →ᵃ[ℝ] ℝ} {lo hi : ℝ}
    (D : Presentation K f lo hi) (hR : (hi-lo)/rangeWidth K f < 1) :
    (volume (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
      (1-(hi-lo)/rangeWidth K f)^2*(volume K).toReal ↔ D.calibrated := by
  let A := CrossedQuadrilateralPlacement.band D.axis D.lower D.upper
  let N := ParallelProductPlane.coordinates ⁻¹' (D.shape.body \ A)
  have himage : D.chart '' N = K \ {x | lo ≤ f x ∧ f x ≤ hi} := by
    dsimp only [N,A]
    rw [Set.preimage_sdiff,Set.image_sdiff D.chart.injective]
    change D.chart '' CrossedQuadrilateralFormDirections.body D.shape \
      D.chart '' nativeBand D.axis D.lower D.upper = _
    rw [← D.body,← D.band]
  have hgap : (volume (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
      factor D.chart*(volume (D.shape.body \ A)).toReal := by
    rw [← himage,area_image]
    rw [show volume N = volume (D.shape.body \ A) from ParallelProductPlane.volume_preimage _]
  have harea : (volume K).toReal = factor D.chart*(volume D.shape.body).toReal := by
    calc
      (volume K).toReal = (volume (D.chart '' CrossedQuadrilateralFormDirections.body D.shape)).toReal :=
        congrArg (fun B : Set Native => (volume B).toReal) D.body
      _ = _ := by rw [area_image,ParallelProductPlane.volume_preimage]
  rw [hgap,harea,D.width]
  rw [show (1-(D.upper-D.lower)/span D.shape D.axis)^2*
      (factor D.chart*(volume D.shape.body).toReal) =
      factor D.chart*((1-(D.upper-D.lower)/span D.shape D.axis)^2*(volume D.shape.body).toReal) by ring]
  have hh := axis_single_iff D.shape D.axis D.lower D.upper D.ordered (by rwa [← D.width])
  exact ⟨fun h => hh.mp (mul_left_cancel₀ (factor_pos D.chart).ne' h),
    fun h => congrArg (fun a => factor D.chart*a) (hh.mpr h)⟩

theorem single_reduction {K : Set Native} (hne : K.Nonempty)
    (f : Fin 3 → Native →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (h1 : p.1 1=p.2 1) (h2 : p.1 2=p.2 2)
    (hR : budget K f p < 1) :
    Equality K f p ↔ (volume (K \ {x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0})).toReal =
      (1-(p.2 0-p.1 0)/rangeWidth K (f 0))^2*(volume K).toReal := by
  have hb : budget K f p = (p.2 0-p.1 0)/rangeWidth K (f 0) := by
    simp [budget,Fin.sum_univ_three,← h1,← h2]
  unfold Equality gapArea
  rw [PlanarSingleActivePlank.gap_eq_single hne f p.1 p.2 hW h1 h2,hb,
    max_eq_right (sub_pos.mpr (by rwa [← hb])).le]

theorem equality_iff_family {K : Set Native} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Native →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (h0 : p.1 0 < p.2 0)
    (h1 : p.1 1=p.2 1) (h2 : p.1 2=p.2 2) (hR : budget K f p < 1) :
    Equality K f p ↔ ∃ D : Presentation K (f 0) (p.1 0) (p.2 0), D.calibrated := by
  have hne : K.Nonempty := by
    obtain ⟨S,T,hb⟩ := CrossedQuadrilateralGenuine.exists_model hG hV
    rw [hb]
    exact (CrossedQuadrilateralContainedOriginal.body_nonempty S).image T
  have hb : budget K f p = (p.2 0-p.1 0)/rangeWidth K (f 0) := by
    simp [budget,Fin.sum_univ_three,← h1,← h2]
  have hr : (p.2 0-p.1 0)/rangeWidth K (f 0) < 1 := by rwa [← hb]
  have hred := single_reduction hne f p hW h1 h2 hR
  constructor
  · intro he
    have ho (i) : p.1 i ≤ p.2 i := by
      fin_cases i; exact h0.le; exact h1.le; exact h2.le
    obtain ⟨S,T,hbody,i,hi,hd⟩ := CrossedQuadrilateralOneDiagonal.original hG hV f p hW ho
      (by rw [hb]; exact div_pos (sub_pos.mpr h0) (hW 0)) hR he
    have hi0 : i=0 := by
      fin_cases i
      · rfl
      · exact (ne_of_lt hi h1).elim
      · exact (ne_of_lt hi h2).elim
    subst i
    let g := pre T (f 0)
    have hw : rangeWidth (CrossedQuadrilateralFormDirections.body S) g = rangeWidth K (f 0) := by
      rw [width_pre,← hbody]
    obtain ⟨ax,l,u,hlu,hband,hwidth⟩ := native_axis S g (p.1 0) (p.2 0) h0
      (by rw [hw]; exact hW 0) hd
    let D : Presentation K (f 0) (p.1 0) (p.2 0) := {
      shape:=S,chart:=T,axis:=ax,lower:=l,upper:=u,body:=hbody,ordered:=hlu,
      width:=by simpa only [hw] using hwidth,
      band:=by
        rw [← hband]
        ext x
        constructor
        · intro hx
          exact ⟨T.symm x,by simpa only [mem_ofPred_eq,g,pre_apply,T.apply_symm_apply] using hx,T.apply_symm_apply x⟩
        · rintro ⟨y,hy,rfl⟩
          exact hy }
    exact ⟨D,(D.equality_iff hr).mp (hred.mp he)⟩
  · rintro ⟨D,hD⟩
    exact hred.mpr ((D.equality_iff hr).mpr hD)

end Quant.CrossedQuadrilateralSingleCatalogue

/-- info: 'Quant.CrossedQuadrilateralSingleCatalogue.equality_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSingleCatalogue.equality_iff_family
