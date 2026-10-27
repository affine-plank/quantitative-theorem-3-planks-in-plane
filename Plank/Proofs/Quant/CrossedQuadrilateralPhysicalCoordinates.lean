/- Transport original affine families into the continuous physical realization. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCrossEncoding

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralPhysicalCoordinates
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open CrossedQuadrilateralImageStrata CrossedQuadrilateralSupportOriginal
open CrossedQuadrilateralCrossEncoding
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def productFamily (T : Point ≃ᵃ[ℝ] Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) :
    Fin 3 → CrossedQuadrilateralAttainment.Point →ᵃ[ℝ] ℝ :=
  fun i => productForm (pre T (f i))

theorem width {K : Set Point} (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (i : Fin 3) :
    rangeWidth S.body (productFamily T f i) = rangeWidth K (f i) := by
  unfold productFamily
  rw [← CrossedQuadrilateralDirections.width_preimage,product_pull,width_pre,← hbody]

theorem budget_eq {K : Set Point} (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) :
    physicalBudget S (productFamily T f) p = budget K f p := by
  simp only [physicalBudget,budget,width S T hbody f]

theorem area_eq {K : Set Point} (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) :
    gapArea K f p = factor T*physicalArea S (productFamily T f) p := by
  rw [hbody,gap_scale]
  congr 1
  unfold gapArea physicalArea
  have he : (CrossedQuadrilateralFormDirections.body S \
      ⋃ i, {z | p.1 i ≤ pre T (f i) z ∧ pre T (f i) z ≤ p.2 i}) =
      ParallelProductPlane.coordinates ⁻¹' (S.body \
      ⋃ i, {z | p.1 i ≤ productFamily T f i z ∧ productFamily T f i z ≤ p.2 i}) := by
    ext z
    simp [CrossedQuadrilateralFormDirections.body,productFamily,productForm]
  rw [he,ParallelProductPlane.volume_preimage]

theorem body_area {K : Set Point} (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S) :
    (volume K).toReal = factor T*(volume S.body).toReal := by
  rw [hbody,area_image,ParallelProductPlane.volume_preimage]

theorem physical_equality {K : Set Point} (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (he : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    physicalArea S (productFamily T f) p =
      (1-physicalBudget S (productFamily T f) p)^2*(volume S.body).toReal := by
  apply mul_left_cancel₀ (factor_pos T).ne'
  rw [← area_eq S T hbody f p,he,budget_eq S T hbody f p,body_area S T hbody]
  ring

theorem coefficients (T : Point ≃ᵃ[ℝ] Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (i : Fin 3) :
    (productFamily T f i).linear (1,0) = (f i).linear (T.linear ![1,0]) ∧
    (productFamily T f i).linear (0,1) = (f i).linear (T.linear ![0,1]) := by
  have hx : ParallelProductPlane.coordinates.symm (1,0) = ![1,0] := by
    ext j; fin_cases j <;> rfl
  have hy : ParallelProductPlane.coordinates.symm (0,1) = ![0,1] := by
    ext j; fin_cases j <;> rfl
  constructor
  · change (f i).linear (T.linear (ParallelProductPlane.coordinates.symm (1,0))) = _
    rw [hx]
  · change (f i).linear (T.linear (ParallelProductPlane.coordinates.symm (0,1))) = _
    rw [hy]

/-- The coordinate realization is constructed here, including negative scales
and null endpoints. No realization or equality-motion hypothesis is supplied. -/
theorem cross_not_tight {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (S : CrossedQuadrilateralAttainment.Shape)
    (T : Point ≃ᵃ[ℝ] Point) (hbody : K = T '' CrossedQuadrilateralFormDirections.body S)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1) {k : ℝ} (hk : k ≠ 0)
    (s c : Fin 3 → ℝ) (hs : ∀ i, s i ≠ 0)
    (hf : ∀ i z, productFamily T f i z = s i*forms k i z+c i)
    (p : Endpoints 3) (hp : p ∈ domain K f) (hR : budget K f p < 1) (hpos : p.1 2 < p.2 2)
    (he : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) : False := by
  apply CrossedQuadrilateralMixedCompact.no_equality_of_realization hG hV S T hbody f hnorm hunit
    ![k,k] (by intro i; fin_cases i <;> exact hk) (encode s c) (continuous_encode s c)
    (fun q hq => ordered_encode hs hq)
    (fun q => (budget_encode S _ k s c hs hf q).trans (budget_eq S T hbody f q))
    (fun q _ hq => tight_encode S _ k s c hs hf q (physical_equality S T hbody f q hq))
    ?_ p hp hR ((positive_bad_iff S k s c (hs 2) p).mpr hpos) he
  intro q _ hq
  obtain ⟨hpos,hbad⟩ := bad_witness S _ hk s c hs hf q hq
  refine ⟨2,hpos,?_⟩
  rwa [(coefficients T f 2).1,(coefficients T f 2).2] at hbad

end Quant.CrossedQuadrilateralPhysicalCoordinates

/-- info: 'Quant.CrossedQuadrilateralPhysicalCoordinates.cross_not_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralPhysicalCoordinates.cross_not_tight
