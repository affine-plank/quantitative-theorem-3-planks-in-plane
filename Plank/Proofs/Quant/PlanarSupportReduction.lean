/- Equality in the supporting-plank induction, for actual gap areas. -/
module

public import Plank.Proofs.Quant.PlanarSupportPairReduction
public import Plank.Proofs.Quant.PlanarTwoPlank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSupportReduction

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarInductionBoundary
  PlanarSupportGap PlanarSupportPairReduction
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem area_homothety_gap_union {m : ℕ} (K : Set Point)
    (g : Fin m → Point →ᵃ[ℝ] ℝ) (a : Point) {r : ℝ} (hq : 0 < 1-r)
    (lo hi : Fin m → ℝ) :
    (volume ((AffineMap.homothety a (1-r) '' K) \
        ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i})).toReal =
      (1-r)^2*(volume (K \
        ⋃ i, {x | pulledEndpoint (g i) a r (lo i) ≤ g i x ∧
          g i x ≤ pulledEndpoint (g i) a r (hi i)})).toReal := by
  rw [← image_sdiff_preimage,preimage_iUnion]
  simp_rw [homothety_preimage_band _ a hq]
  simpa only [sub_sub_cancel,pulledEndpoint] using
    area_homothety (K \ ⋃ i, {x | (lo i-r*g i a)/(1-r) ≤ g i x ∧
      g i x ≤ (hi i-r*g i a)/(1-r)}) a (1-r)

/-- Exact equality in the support induction. The hypothesis `hm` is an
explicit bound for the remaining number of planks; the three-plank
specialization below discharges it with the proved full two-plank bound. -/
theorem equality_iff_reduced {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : Point →ᵃ[ℝ] ℝ)
    (g : Fin m → Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (_hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (r : ℝ) (lo hi : Fin m → ℝ) (hr : 0 ≤ r)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hR : r+∑ i, (hi i-lo i)/rangeWidth K (g i) < 1) :
    (volume (K \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪
        ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i}))).toReal =
        (1-r-∑ i, (hi i-lo i)/rangeWidth K (g i))^2*(volume K).toReal ↔
      (volume (K \ ⋃ i, {x | pulledEndpoint (g i) a r (lo i) ≤ g i x ∧
          g i x ≤ pulledEndpoint (g i) a r (hi i)})).toReal =
        (1-∑ i, (pulledEndpoint (g i) a r (hi i)-pulledEndpoint (g i) a r (lo i))/
          rangeWidth K (g i))^2*(volume K).toReal ∧
      K ⊆ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i}) ∪
        (AffineMap.homothety a (1-r) '' K) := by
  let q := 1-r
  let S := ∑ i, (hi i-lo i)/rangeWidth K (g i)
  let C := AffineMap.homothety a q '' K
  let P := {x | 0 ≤ f x ∧ f x ≤ r}
  let U := ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i}
  let l := fun i => pulledEndpoint (g i) a r (lo i)
  let h := fun i => pulledEndpoint (g i) a r (hi i)
  let M := (1-r-S)^2*(volume K).toReal
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ =>
    div_nonneg (sub_nonneg.mpr (horder i)) (hW i).le
  have hq : 0 < q := by dsimp [q]; linarith only [hR,hS]
  have hq1 : q ≤ 1 := by dsimp [q]; linarith only [hr]
  have hsmall : S/q < 1 := (div_lt_one hq).mpr (by dsimp [q]; linarith only [hR])
  have hlinear : f.linear ≠ 0 := by
    intro hz
    obtain ⟨c,hc⟩ := f.linear_eq_zero_iff_exists_const.mp hz
    have he : f a = f b := by rw [hc]; rfl
    rw [hfa,hfb] at he
    norm_num at he
  have hC : IsCompact C := hK.image (AffineMap.homothety_continuous a q)
  have hU : IsClosed U := isClosed_iUnion_of_finite fun i =>
    (isClosed_le continuous_const (continuous_form (g i))).inter
      (isClosed_le (continuous_form (g i)) continuous_const)
  have hCK : C ⊆ K := homothety_subset hconv ha ⟨hq.le,hq1⟩
  have hbeyond : ∀ x ∈ C, r ≤ f x := by
    rintro _ ⟨x,hx,rfl⟩
    rw [form_homothety,hfa,mul_one]
    have hh := mul_nonneg hq.le (hf x hx).1
    dsimp [q] at hh ⊢
    linarith only [hh]
  have harea : (volume (C \ U)).toReal =
      q^2*(volume (K \ ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ h i})).toReal :=
    area_homothety_gap_union K g a hq lo hi
  have hwidth : (∑ i, (h i-l i)/rangeWidth K (g i)) = S/q := by
    simp only [l,h,pulled_relativeWidth]
    exact (Finset.sum_div _ _ _).symm
  have hlh (i) : l i ≤ h i := sub_nonneg.mp (by
    change 0 ≤ pulledEndpoint (g i) a r (hi i)-pulledEndpoint (g i) a r (lo i)
    rw [pulled_width]
    exact div_nonneg (sub_nonneg.mpr (horder i)) hq.le)
  have hscalar : q^2*((1-S/q)^2*(volume K).toReal) = M := by
    have hM : M = (q-S)^2*(volume K).toReal := rfl
    rw [hM]
    field_simp
  have hbound := hm K hK hconv ⟨a,ha⟩ g l h hlh hW
  rw [hwidth,max_eq_right (sub_pos.mpr hsmall).le] at hbound
  have hcapbound : M ≤ (volume (C \ U)).toReal := by
    rw [← hscalar,harea]
    exact mul_le_mul_of_nonneg_left hbound (sq_nonneg q)
  have hcapmono : (volume (C \ U)).toReal ≤ (volume (K \ (P ∪ U))).toReal :=
    area_gap_mono_beyond hK hCK f hlinear 0 r hbeyond
  have hcoveriff := area_eq_iff_cover hK hconv hV hC hU hCK f hlinear 0 r hbeyond
  change (volume (K \ (P ∪ U))).toReal = M ↔ _
  constructor
  · intro he
    have hcap : (volume (C \ U)).toReal = M := le_antisymm (hcapmono.trans_eq he) hcapbound
    refine ⟨?_,hcoveriff.mp (hcap.trans he.symm)⟩
    change (volume (K \ ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ h i})).toReal =
      (1-∑ i, (h i-l i)/rangeWidth K (g i))^2*(volume K).toReal
    rw [hwidth]
    apply (mul_left_cancel₀ (pow_ne_zero 2 hq.ne'))
    rw [← harea,hcap,hscalar]
  · rintro ⟨he,hcover⟩
    have hcap : (volume (C \ U)).toReal = M := by
      rw [harea,he,hwidth,hscalar]
    exact (hcoveriff.mpr hcover).symm.trans hcap

/-- Three actual planks, one at a supporting line. No unproved geometric
or lower-bound assumption occurs in this specialization. -/
theorem equality_three_iff_reduced
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : Point →ᵃ[ℝ] ℝ)
    (g : Fin 2 → Point →ᵃ[ℝ] ℝ) (a b : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (r : ℝ) (lo hi : Fin 2 → ℝ) (hr : 0 ≤ r)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < rangeWidth K (g i))
    (hR : r+∑ i, (hi i-lo i)/rangeWidth K (g i) < 1) :
    (volume (K \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪
        ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i}))).toReal =
        (1-r-∑ i, (hi i-lo i)/rangeWidth K (g i))^2*(volume K).toReal ↔
      (volume (K \ ⋃ i, {x | pulledEndpoint (g i) a r (lo i) ≤ g i x ∧
          g i x ≤ pulledEndpoint (g i) a r (hi i)})).toReal =
        (1-∑ i, (pulledEndpoint (g i) a r (hi i)-pulledEndpoint (g i) a r (lo i))/
          rangeWidth K (g i))^2*(volume K).toReal ∧
      K ⊆ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ ⋃ i, {x | lo i ≤ g i x ∧ g i x ≤ hi i}) ∪
        (AffineMap.homothety a (1-r) '' K) :=
  equality_iff_reduced PlanarTwoPlank.sharpPlanarBound_two hK hconv hV f g a b
    ha hb hfa hfb hf r lo hi hr horder hW hR

end Plank.PlanarSupportReduction

/-- info: 'Plank.PlanarSupportReduction.equality_three_iff_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportReduction.equality_three_iff_reduced
