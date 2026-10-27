/- The parallel classification in an arbitrary common affine coordinate. -/
module

public import Plank.Proofs.Quant.PlanarParallelConsequences

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelClassification

open Set MeasureTheory PlanarQuantitative PlanarParallelTranslations
open Plank.Convex.DeficientHeightTilt

def normalizedForm (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) (b : Point) : Point →ᵃ[ℝ] ℝ :=
  (rangeWidth K f)⁻¹ • (f-AffineMap.const ℝ Point (f b))

def normalizedEndpoints {ι : Type*} (K : Set Point) (f : Point →ᵃ[ℝ] ℝ)
    (b : Point) (endpoints : ι → ℝ) (i : ι) : ℝ := (endpoints i-f b)/rangeWidth K f

/-- No normalization premise is needed: normalize the common affine
functional by its actual range on the body. This proves the classification
for the original area formula and arbitrary common affine coordinates. -/
theorem equality_iff_normalized_tiling {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (f : Point →ᵃ[ℝ] ℝ) (hW : 0 < rangeWidth K f)
    (hR : 0 < ∑ i, (hi i-lo i)/rangeWidth K f)
    (hR1 : (∑ i, (hi i-lo i)/rangeWidth K f) < 1)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x) :
    (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
        (max 0 (1-∑ i, (hi i-lo i)/rangeWidth K f))^2*(volume K).toReal ↔
      Tiling K (normalizedEndpoints K f b lo) (normalizedEndpoints K f b hi)
        (normalizedForm K f b) a b := by
  let g := normalizedForm K f b
  let nl := normalizedEndpoints K f b lo
  let nh := normalizedEndpoints K f b hi
  have hg (x) : g x = (f x-f b)/rangeWidth K f := by
    simp [g,normalizedForm,div_eq_mul_inv,mul_comm]
  have hspan : rangeWidth K f = f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
  have hga : g a = 1 := by rw [hg,← hspan,div_self hW.ne']
  have hgb : g b = 0 := by rw [hg,sub_self,zero_div]
  have hgf (x) (hx : x ∈ K) : 0 ≤ g x ∧ g x ≤ 1 := by
    rw [hg]
    refine ⟨div_nonneg (sub_nonneg.mpr (hmin x hx)) hW.le,?_⟩
    apply (div_le_one hW).mpr
    rw [hspan]
    exact sub_le_sub_right (hmax x hx) _
  have hn (i) : nl i ≤ nh i := (div_le_div_iff_of_pos_right hW).mpr (sub_le_sub_right (ho i) _)
  have htotal : total nl nh = ∑ i, (hi i-lo i)/rangeWidth K f := by
    unfold total widths
    apply Finset.sum_congr rfl
    intro i _
    dsimp [nl,nh,normalizedEndpoints]
    ring
  have hbands : (⋃ i, LinearBands.closedBand g (nl i) (nh i)) =
      ⋃ i, LinearBands.closedBand f (lo i) (hi i) := by
    ext x
    simp only [mem_iUnion,LinearBands.closedBand,mem_ofPred_eq]
    apply exists_congr
    intro i
    rw [hg]
    dsimp only [nl,nh,normalizedEndpoints]
    simp only [div_le_div_iff_of_pos_right hW,sub_le_sub_iff_right]
  have hh := equality_iff_tiling hK hconv hV nl nh hn (by rwa [htotal])
    (by rwa [htotal]) g a b ha hb hga hgb hgf
  rw [hbands,htotal] at hh
  rw [max_eq_right (sub_pos.mpr hR1).le]
  exact hh

/-- Compactness supplies the support points, giving an existential family
description requiring no support-point choices from the caller. -/
theorem equality_iff_exists_normalized_tiling {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (f : Point →ᵃ[ℝ] ℝ) (hW : 0 < rangeWidth K f)
    (hR : 0 < ∑ i, (hi i-lo i)/rangeWidth K f)
    (hR1 : (∑ i, (hi i-lo i)/rangeWidth K f) < 1) :
    (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
        (max 0 (1-∑ i, (hi i-lo i)/rangeWidth K f))^2*(volume K).toReal ↔
      ∃ a ∈ K, ∃ b ∈ K, (∀ x ∈ K, f x ≤ f a) ∧ (∀ x ∈ K, f b ≤ f x) ∧
        Tiling K (normalizedEndpoints K f b lo) (normalizedEndpoints K f b hi)
          (normalizedForm K f b) a b := by
  constructor
  · intro he
    obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (PlanarGapCells.continuous_form f)
    exact ⟨a,ha,b,hb,hmax,hmin,
      (equality_iff_normalized_tiling hK hconv hV lo hi ho f hW hR hR1 a b ha hb hmax hmin).mp he⟩
  · rintro ⟨a,ha,b,hb,hmax,hmin,ht⟩
    exact (equality_iff_normalized_tiling hK hconv hV lo hi ho f hW hR hR1 a b ha hb hmax hmin).mpr ht

end Plank.PlanarParallelClassification

/-- info: 'Plank.PlanarParallelClassification.equality_iff_exists_normalized_tiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelClassification.equality_iff_exists_normalized_tiling
