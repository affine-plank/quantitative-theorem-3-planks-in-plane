/- Transport the established parallel-plank bound/rigidity to the product plane. -/
module
public import Plank.Proofs.Quant.PlanarParallelClassification
public import Plank.Proofs.Quant.CrossedQuadrilateralPlacement
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.ParallelProductPlane
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment
open scoped BigOperators

def coordinates : (Fin 2 → ℝ) ≃L[ℝ] Point := ContinuousLinearEquiv.finTwoArrow ℝ ℝ

theorem volume_preimage (A : Set Point) : volume (coordinates ⁻¹' A) = volume A := by
  change volume (MeasurableEquiv.finTwoArrow ⁻¹' A) = volume A
  rw [← MeasurableEquiv.map_apply, (volume_preserving_finTwoArrow ℝ).map_eq]

theorem compact_preimage {K : Set Point} (hK : IsCompact K) :
    IsCompact (coordinates ⁻¹' K) := by
  have he : coordinates ⁻¹' K = coordinates.symm '' K := by
    ext x
    constructor
    · intro hx
      exact ⟨coordinates x,hx,by simp⟩
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
  rw [he]
  exact hK.image coordinates.symm.continuous

def pullForm (f : Point →ᵃ[ℝ] ℝ) : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
  f.comp coordinates.toLinearEquiv.toAffineEquiv.toAffineMap

@[simp] theorem pullForm_apply (f : Point →ᵃ[ℝ] ℝ) (x : Fin 2 → ℝ) :
    pullForm f x = f (coordinates x) := rfl

theorem volume_gap_preimage {ι : Type*} (K : Set Point) (f : Point →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) :
    volume ((coordinates ⁻¹' K) \ ⋃ i, Plank.LinearBands.closedBand (pullForm f) (lo i) (hi i)) =
      volume (K \ ⋃ i, Plank.LinearBands.closedBand f (lo i) (hi i)) := by
  rw [← volume_preimage]
  congr 1
  ext x
  simp [Plank.LinearBands.closedBand]

theorem parallel_lower_bound {ι : Type*} [Fintype ι] {K : Set Point}
    (hK : IsCompact K) (hc : Convex ℝ K) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR : (∑ i, (hi i-lo i)) < 1) (f : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0) :
    (1-∑ i, (hi i-lo i))^2*(volume K).toReal ≤
      (volume (K \ ⋃ i, Plank.LinearBands.closedBand f (lo i) (hi i))).toReal := by
  have h := Plank.PlanarParallelBound.uncovered_area_lower_bound (compact_preimage hK)
    (hc.linear_preimage coordinates.toLinearMap) lo hi ho hR (pullForm f)
    (coordinates.symm a) (coordinates.symm b) (by simpa using ha) (by simpa using hb)
    (by simpa using hfa) (by simpa using hfb)
  rw [volume_gap_preimage,volume_preimage] at h
  exact h

/-- A positive parallel pair separated by a nonempty gap cannot attain the
square bound. The endpoints have no prior location restriction. -/
theorem separated_pair_not_equality {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (lo hi : Bool → ℝ) (ho : ∀ i, lo i < hi i) (hsep : hi false < lo true)
    (hR : (∑ i, (hi i-lo i)) < 1) (f : Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ z ∈ K, 0 ≤ f z ∧ f z ≤ 1) :
    (volume (K \ ⋃ i, Plank.LinearBands.closedBand f (lo i) (hi i))).toReal ≠
      (1-∑ i, (hi i-lo i))^2*(volume K).toReal := by
  intro he
  have hpos : 0 < Plank.PlanarParallelTranslations.total lo hi := by
    change 0 < ∑ i, (hi i-lo i)
    exact Finset.sum_pos (fun i _ => sub_pos.mpr (ho i)) Finset.univ_nonempty
  have ht := (Plank.PlanarParallelClassification.equality_iff_tiling (compact_preimage hK)
    (hc.linear_preimage coordinates.toLinearMap) (by rwa [volume_preimage]) lo hi
    (fun i => (ho i).le) hpos hR (pullForm f) (coordinates.symm a) (coordinates.symm b)
    (by simpa using ha) (by simpa using hb) (by simpa using hfa) (by simpa using hfb)
    (fun z hz => hf (coordinates z) hz)).mp (by
      rw [volume_gap_preimage,volume_preimage]
      exact he)
  obtain ⟨L,H,_,_,_,hunion,_⟩ := ht
  have hl : hi false ∈ Icc L H := by
    rw [← hunion]
    exact mem_iUnion.mpr ⟨⟨false,ho false⟩,(ho false).le,le_rfl⟩
  have hh : lo true ∈ Icc L H := by
    rw [← hunion]
    exact mem_iUnion.mpr ⟨⟨true,ho true⟩,le_rfl,(ho true).le⟩
  have hm : (hi false+lo true)/2 ∈ Icc L H := ⟨by linarith [hl.1],by linarith [hh.2]⟩
  rw [← hunion] at hm
  obtain ⟨i,hi⟩ := mem_iUnion.mp hm
  rcases i with ⟨i,hi_pos⟩
  cases i <;> dsimp only at hi
  · linarith [hi.2]
  · linarith [hi.1]

end Quant.ParallelProductPlane
