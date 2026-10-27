/- Exhaustive geometric catalogue for two positive planks on any quadrilateral. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAxisPresentation

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralTwoPlankFamilies
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarEqualityReductions
open CrossedQuadrilateralImageStrata CrossedQuadrilateralAxisPresentation
open CrossedQuadrilateralTwoPlankCatalogue
open Plank.Convex.DeficientHeightTilt

/-- A genuine affine presentation of the original body and each physical
plank. The widths are the original relative widths, not chosen surrogates. -/
structure Presentation (K : Set Native) (f : Fin 2 → Native →ᵃ[ℝ] ℝ) (p : Endpoints 2) where
  shape : CrossedQuadrilateralAttainment.Shape
  chart : Native ≃ᵃ[ℝ] Native
  axis : Fin 2 → Bool
  lo : Fin 2 → ℝ
  hi : Fin 2 → ℝ
  body : K = chart '' CrossedQuadrilateralFormDirections.body shape
  ordered : ∀ i, lo i < hi i
  band : ∀ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = chart '' nativeBand (axis i) (lo i) (hi i)
  width : ∀ i, (p.2 i-p.1 i)/rangeWidth K (f i) = (hi i-lo i)/span shape (axis i)

def Presentation.inFamilies {K : Set Native} {f : Fin 2 → Native →ᵃ[ℝ] ℝ} {p : Endpoints 2}
    (D : Presentation K f p) : Prop :=
  Families D.shape (D.axis 0) (D.axis 1) (D.lo 0) (D.hi 0) (D.lo 1) (D.hi 1)

theorem exists_presentation {K : Set Native} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Native →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) (he : Equality K f p) :
    Nonempty (Presentation K f p) := by
  obtain ⟨S,T,hbody,hd⟩ := CrossedQuadrilateralTwoPlankDirections.original hG hV f p hW ho hR he
  let g (i) := pre T (f i)
  have hw (i) : rangeWidth (CrossedQuadrilateralFormDirections.body S) (g i) = rangeWidth K (f i) := by
    rw [width_pre,← hbody]
  choose ax l u hlu hband hwidth using fun i =>
    native_axis S (g i) (p.1 i) (p.2 i) (ho i) (by rw [hw]; exact hW i) (hd i)
  refine ⟨{
    shape := S
    chart := T
    axis := ax
    lo := l
    hi := u
    body := hbody
    ordered := hlu
    band := ?_
    width := fun i => by simpa only [hw] using hwidth i}⟩
  intro i
  rw [← hband i]
  ext x
  constructor
  · intro hx
    exact ⟨T.symm x,by simpa only [mem_ofPred_eq,g,pre_apply,T.apply_symm_apply] using hx,T.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    exact hy

theorem Presentation.equality_iff {K : Set Native} {f : Fin 2 → Native →ᵃ[ℝ] ℝ}
    {p : Endpoints 2} (D : Presentation K f p) (hR : budget K f p < 1) :
    Equality K f p ↔ D.inFamilies := by
  let A := CrossedQuadrilateralPlacement.band (D.axis 0) (D.lo 0) (D.hi 0) ∪
    CrossedQuadrilateralPlacement.band (D.axis 1) (D.lo 1) (D.hi 1)
  let N := ParallelProductPlane.coordinates ⁻¹' (D.shape.body \ A)
  have himage : D.chart '' N = K \
      ({x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪ {x | p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1}) := by
    dsimp only [N,A]
    rw [Set.preimage_sdiff,Set.preimage_union,Set.image_sdiff D.chart.injective,Set.image_union]
    change D.chart '' CrossedQuadrilateralFormDirections.body D.shape \
      (D.chart '' nativeBand (D.axis 0) (D.lo 0) (D.hi 0) ∪
        D.chart '' nativeBand (D.axis 1) (D.lo 1) (D.hi 1)) = _
    rw [← D.body,← D.band 0,← D.band 1]
  have hgap : gapArea K f p = factor D.chart*(volume (D.shape.body \ A)).toReal := by
    have hu : (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) =
        ({x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪ {x | p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1}) := by
      ext x
      simp only [mem_iUnion,Fin.exists_fin_two,mem_union]
    rw [gapArea,hu,← himage,area_image]
    rw [show volume N = volume (D.shape.body \ A) from ParallelProductPlane.volume_preimage _]
  have harea : (volume K).toReal = factor D.chart*(volume D.shape.body).toReal := by
    calc
      (volume K).toReal = (volume (D.chart '' CrossedQuadrilateralFormDirections.body D.shape)).toReal :=
        congrArg (fun A : Set Native => (volume A).toReal) D.body
      _ = _ := by rw [area_image,ParallelProductPlane.volume_preimage]
  have hb : budget K f p =
      (D.hi 0-D.lo 0)/span D.shape (D.axis 0)+(D.hi 1-D.lo 1)/span D.shape (D.axis 1) := by
    simp only [budget,Fin.sum_univ_two,D.width]
  have hE : Equality K f p ↔ (volume (D.shape.body \ A)).toReal =
      (1-budget K f p)^2*(volume D.shape.body).toReal := by
    unfold Equality
    rw [max_eq_right (sub_pos.mpr hR).le,hgap,harea]
    rw [show (1-budget K f p)^2*(factor D.chart*(volume D.shape.body).toReal) =
      factor D.chart*((1-budget K f p)^2*(volume D.shape.body).toReal) by ring]
    exact ⟨mul_left_cancel₀ (factor_pos D.chart).ne',fun h => congrArg (fun a => factor D.chart*a) h⟩
  rw [hE,hb]
  exact axis_equality_iff D.shape (D.axis 0) (D.axis 1) _ _ _ _
    (D.ordered 0) (D.ordered 1) (by rwa [← hb])

/-- Exhaustive necessary-and-sufficient geometric catalogue, in the original
coordinates. Every two-positive-plank equality on a genuine quadrilateral is
an affine image of exactly one of the two displayed types: two calibrated
crossed bands, or two adjacent parallel pieces of one calibrated band.
The converse proves actual equality for every such represented family. -/
theorem equality_iff_families {K : Set Native} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Native →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget K f p < 1) :
    Equality K f p ↔ ∃ D : Presentation K f p, D.inFamilies := by
  constructor
  · intro he
    obtain ⟨D⟩ := exists_presentation hG hV f p hW ho hR he
    exact ⟨D,(D.equality_iff hR).mp he⟩
  · rintro ⟨D,hD⟩
    exact (D.equality_iff hR).mpr hD

end Quant.CrossedQuadrilateralTwoPlankFamilies

/-- info: 'Quant.CrossedQuadrilateralTwoPlankFamilies.equality_iff_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralTwoPlankFamilies.equality_iff_families
