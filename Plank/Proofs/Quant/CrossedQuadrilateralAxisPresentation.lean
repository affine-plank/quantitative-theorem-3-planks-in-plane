/- Convert arbitrary diagonal affine planks to physical axis intervals. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralTwoPlankCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralAxisPresentation
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralPlacement CrossedQuadrilateralTwoPlankCatalogue
open Plank.Convex.DeficientHeightTilt

def positive (S : Shape) (i : Bool) : ℝ := if i then S.b else S.a
def negative (S : Shape) (i : Bool) : ℝ := if i then S.d else S.c

theorem span_eq (S : Shape) (i : Bool) : span S i = positive S i+negative S i := by
  cases i <;> rfl

theorem coord_vector (i : Bool) (t : ℝ) : coord i (vector i t) = t := by cases i <;> rfl

theorem endpoint_mem (S : Shape) (i : Bool) :
    vector i (positive S i) ∈ S.body ∧ vector i (-negative S i) ∈ S.body := by
  cases i
  · exact ⟨vertexX_mem S true,vertexX_mem S false⟩
  · exact ⟨vertexY_mem S true,vertexY_mem S false⟩

theorem coord_bounds (S : Shape) (i : Bool) {x : Point} (hx : x ∈ S.body) :
    -negative S i ≤ coord i x ∧ coord i x ≤ positive S i := by
  cases i
  · exact (coordinate_box S hx).1
  · exact (coordinate_box S hx).2

theorem positive_scale (S : Shape) (i : Bool) (G : Point →ᵃ[ℝ] ℝ)
    (k c : ℝ) (hk : 0 < k) (hG : ∀ x, G x = k*coord i x+c)
    (lo hi : ℝ) (ho : lo < hi) :
    ∃ l u : ℝ, l < u ∧ {x | lo ≤ G x ∧ G x ≤ hi} = band i l u ∧
      (hi-lo)/rangeWidth S.body G = (u-l)/span S i := by
  have hw : rangeWidth S.body G = k*span S i := by
    have hh := Plank.Body.width_eq_of_realisers (f := G) (endpoint_mem S i).1 (endpoint_mem S i).2
      (fun x hx => by
        rw [hG,hG,coord_vector]
        nlinarith only [mul_le_mul_of_nonneg_left (coord_bounds S i hx).2 hk.le])
      (fun x hx => by
        rw [hG,hG,coord_vector]
        nlinarith only [mul_le_mul_of_nonneg_left (coord_bounds S i hx).1 hk.le])
    change rangeWidth S.body G = G (vector i (positive S i))-G (vector i (-negative S i)) at hh
    rw [hh,hG,hG,coord_vector,coord_vector,span_eq]
    ring
  refine ⟨(lo-c)/k,(hi-c)/k,
    (div_lt_div_iff_of_pos_right hk).mpr (sub_lt_sub_right ho _),?_,?_⟩
  · ext x
    change (lo ≤ G x ∧ G x ≤ hi) ↔ ((lo-c)/k ≤ coord i x ∧ coord i x ≤ (hi-c)/k)
    rw [hG,div_le_iff₀ hk,le_div_iff₀ hk]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith only [h₁,h₂]
  · rw [hw]
    field_simp
    ring

theorem nonzero_scale (S : Shape) (i : Bool) (G : Point →ᵃ[ℝ] ℝ)
    (k c : ℝ) (hk : k ≠ 0) (hG : ∀ x, G x = k*coord i x+c)
    (lo hi : ℝ) (ho : lo < hi) :
    ∃ l u : ℝ, l < u ∧ {x | lo ≤ G x ∧ G x ≤ hi} = band i l u ∧
      (hi-lo)/rangeWidth S.body G = (u-l)/span S i := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · obtain ⟨l,u,hu,hband,hw⟩ := positive_scale S i (-G) (-k) (-c) (neg_pos.mpr hk)
      (fun x => by change -G x = _; rw [hG]; ring) (-hi) (-lo) (neg_lt_neg ho)
    have hneg : {x | -hi ≤ (-G) x ∧ (-G) x ≤ -lo} = {x | lo ≤ G x ∧ G x ≤ hi} := by
      ext x
      change (-hi ≤ -G x ∧ -G x ≤ -lo) ↔ _
      constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]
    have hwneg : rangeWidth S.body (-G) = rangeWidth S.body G :=
      Plank.Body.width_neg (compact_body S) ⟨0,zero_mem S⟩ G.continuous_of_finiteDimensional
    exact ⟨l,u,hu,by rwa [hneg] at hband,by simpa only [hwneg,neg_sub_neg] using hw⟩
  · exact positive_scale S i G k c hk hG lo hi ho

theorem product_axis (S : Shape) (G : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo < hi) (hW : 0 < rangeWidth S.body G)
    (hd : G.linear (1,0) = 0 ∨ G.linear (0,1) = 0) :
    ∃ (i : Bool) (l u : ℝ), l < u ∧ {x | lo ≤ G x ∧ G x ≤ hi} = band i l u ∧
      (hi-lo)/rangeWidth S.body G = (u-l)/span S i := by
  have hn := CrossedQuadrilateralSupport.nonzero_coefficient S G hW
  rcases hd with hx | hy
  · refine ⟨true,?_⟩
    apply nonzero_scale S true G (G.linear (0,1)) (G 0) (hn.resolve_left (not_not.mpr hx))
    · intro x
      rw [CrossedQuadrilateralSupport.eval_linear,hx]
      simp only [coord,if_true,zero_mul,zero_add]
    · exact ho
  · refine ⟨false,?_⟩
    apply nonzero_scale S false G (G.linear (1,0)) (G 0) (hn.resolve_right (not_not.mpr hy))
    · intro x
      rw [CrossedQuadrilateralSupport.eval_linear,hy]
      simp only [coord,Bool.false_eq_true,if_false,zero_mul,add_zero]
    · exact ho

abbrev Native := Fin 2 → ℝ
def nativeBand (i : Bool) (l u : ℝ) : Set Native :=
  ParallelProductPlane.coordinates ⁻¹' band i l u

theorem native_axis (S : Shape) (g : Native →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo < hi) (hW : 0 < rangeWidth (CrossedQuadrilateralFormDirections.body S) g)
    (hd : g.linear ![1,0] = 0 ∨ g.linear ![0,1] = 0) :
    ∃ (i : Bool) (l u : ℝ), l < u ∧ {x | lo ≤ g x ∧ g x ≤ hi} = nativeBand i l u ∧
      (hi-lo)/rangeWidth (CrossedQuadrilateralFormDirections.body S) g = (u-l)/span S i := by
  let G := CrossedQuadrilateralSupportOriginal.productForm g
  have hw : rangeWidth S.body G = rangeWidth (CrossedQuadrilateralFormDirections.body S) g := by
    rw [← CrossedQuadrilateralDirections.width_preimage,CrossedQuadrilateralSupportOriginal.product_pull]
  obtain ⟨i,l,u,hlu,hband,hr⟩ := product_axis S G lo hi ho (by rwa [hw]) hd
  refine ⟨i,l,u,hlu,?_,by rwa [hw] at hr⟩
  have hh := congrArg (fun A : Set Point => ParallelProductPlane.coordinates ⁻¹' A) hband
  have hval (x : Native) : G (ParallelProductPlane.coordinates x) = g x := by
    change g (ParallelProductPlane.coordinates.symm (ParallelProductPlane.coordinates x)) = g x
    rw [ParallelProductPlane.coordinates.symm_apply_apply]
  simpa only [nativeBand,Set.preimage_ofPred_eq,hval] using hh

end Quant.CrossedQuadrilateralAxisPresentation
