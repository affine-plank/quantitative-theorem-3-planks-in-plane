/- Actual homothetic bodies and the boundary step in the planar induction. -/
module

public import Plank.Proofs.Quant.PlanarOnePlank
public import Plank.Proofs.Quant.FiniteDimensionalInductionBoundary

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarInductionBoundary

open Set MeasureTheory PlanarQuantitative PlanarGapCells
open Plank.Convex.DeficientHeightTilt

/-- Evaluation at an actual homothetic point. -/
theorem form_homothety (f : Point →ᵃ[ℝ] ℝ) (z : Point) (q : ℝ) (x : Point) :
    f (AffineMap.homothety z q x) = (1-q)*f z + q*f x := by
  exact FiniteDimensionalInductionBoundary.form_homothety f z q x

/-- Homotheties scale the actual directional range of every affine form. -/
theorem rangeWidth_homothety {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (z : Point) (q : ℝ) (hq : 0 ≤ q) :
    rangeWidth (AffineMap.homothety z q '' K) f = q * rangeWidth K f := by
  exact FiniteDimensionalInductionBoundary.width_homothety hK hne f z q hq

/-- The actual Lebesgue area scales by the square of the homothety ratio. -/
theorem area_homothety (K : Set Point) (z : Point) (q : ℝ) :
    (volume (AffineMap.homothety z q '' K)).toReal = q^2 * (volume K).toReal := by
  rw [volume.addHaar_image_homothety, ENNReal.toReal_mul]
  simp only [Module.finrank_pi, Fintype.card_fin]
  rw [abs_of_nonneg (sq_nonneg q), ENNReal.toReal_ofReal (sq_nonneg q)]

/-- Contracting a convex body toward one of its points stays inside the body. -/
theorem homothety_subset {K : Set Point} (hconv : Convex ℝ K) {z : Point}
    (hz : z ∈ K) {q : ℝ} (hq : q ∈ Icc 0 1) :
    AffineMap.homothety z q '' K ⊆ K := by
  exact FiniteDimensionalInductionBoundary.homothety_subset hconv hz hq

/-- A zero-width affine plank can be deleted without changing actual gap area. -/
theorem area_delete_zero_width (K U : Set Point) (f : Point →ᵃ[ℝ] ℝ)
    (hf : f.linear ≠ 0) (c : ℝ) :
    (volume (K \ ({x | c ≤ f x ∧ f x ≤ c} ∪ U))).toReal =
      (volume (K \ U)).toReal := by
  exact FiniteDimensionalInductionBoundary.volume_delete_zero_width K U f hf c

/-- A sub-body lying on the upper side of an extra plank contributes all of
its remaining gap area. Its common boundary line has zero area. -/
theorem area_gap_mono_beyond {K C U : Set Point} (hK : IsCompact K)
    (hCK : C ⊆ K) (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (lo hi : ℝ)
    (hbeyond : ∀ x ∈ C, hi ≤ f x) :
    (volume (C \ U)).toReal ≤
      (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪ U))).toReal := by
  exact FiniteDimensionalInductionBoundary.volume_gap_mono_beyond hK hCK f hf lo hi hbeyond

/-- The lower-support boundary step for actual affine planks. Assuming the
full theorem for `m` planks on every body, an additional plank whose lower
endpoint is at or below the body's minimum satisfies the sharp bound.
The homothetic body's area, ranges and containment are proved here. -/
theorem bound_extra_lower_support {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (g : Fin m → Point →ᵃ[ℝ] ℝ) (l u : Fin m → ℝ)
    (horder : ∀ i, l i ≤ u i) (hWg : ∀ i, 0 < rangeWidth K (g i))
    (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) (horderf : lo ≤ hi)
    (hWf : 0 < rangeWidth K f) (hlower : ∀ x ∈ K, lo ≤ f x) :
    (max 0 (1 - (hi-lo)/rangeWidth K f - ∑ i, (u i-l i)/rangeWidth K (g i)))^2 *
        (volume K).toReal ≤
      (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪
        ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal := by
  exact FiniteDimensionalInductionBoundary.bound_extra_lower_support hm hK hconv hne g l u horder hWg f lo hi horderf hWf hlower

/-- The upper-support case is the lower-support construction with the extra
functional reversed. All other physical planks stay fixed. -/
theorem bound_extra_upper_support {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (g : Fin m → Point →ᵃ[ℝ] ℝ) (l u : Fin m → ℝ)
    (horder : ∀ i, l i ≤ u i) (hWg : ∀ i, 0 < rangeWidth K (g i))
    (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) (horderf : lo ≤ hi)
    (hWf : 0 < rangeWidth K f) (hupper : ∀ x ∈ K, f x ≤ hi) :
    (max 0 (1 - (hi-lo)/rangeWidth K f - ∑ i, (u i-l i)/rangeWidth K (g i)))^2 *
        (volume K).toReal ≤
      (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪
        ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal := by
  exact FiniteDimensionalInductionBoundary.bound_extra_upper_support hm hK hconv hne g l u horder hWg f lo hi horderf hWf hupper

/-- The zero-width boundary case follows by deleting the null extra plank
and applying the actual-area induction hypothesis. -/
theorem bound_extra_zero_width {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (g : Fin m → Point →ᵃ[ℝ] ℝ) (l u : Fin m → ℝ)
    (horder : ∀ i, l i ≤ u i) (hWg : ∀ i, 0 < rangeWidth K (g i))
    (f : Point →ᵃ[ℝ] ℝ) (c : ℝ) (hWf : 0 < rangeWidth K f) :
    (max 0 (1 - ∑ i, (u i-l i)/rangeWidth K (g i)))^2 * (volume K).toReal ≤
      (volume (K \ ({x | c ≤ f x ∧ f x ≤ c} ∪
        ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal := by
  exact FiniteDimensionalInductionBoundary.bound_extra_zero_width hm hK hconv hne g l u horder hWg f c hWf

/-- The boundary estimate in the final theorem's indexing convention,
when the distinguished plank is indexed by zero. -/
theorem bound_at_zero_index {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (lo hi : Fin (m+1) → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hface : lo 0 = hi 0 ∨ (∀ x ∈ K, lo 0 ≤ f 0 x) ∨ (∀ x ∈ K, f 0 x ≤ hi 0)) :
    (max 0 (1 - ∑ i, (hi i-lo i)/rangeWidth K (f i)))^2 * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal := by
  exact FiniteDimensionalInductionBoundary.bound_at_zero_index hm hK hconv hne f lo hi horder hW hface

/-- Any zero-width or support-touching plank pays the boundary through the
previous actual-area theorem. The distinguished index is arbitrary. -/
theorem bound_at_index {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin (m+1) → Point →ᵃ[ℝ] ℝ) (lo hi : Fin (m+1) → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < rangeWidth K (f i))
    (j : Fin (m+1))
    (hface : lo j = hi j ∨ (∀ x ∈ K, lo j ≤ f j x) ∨ (∀ x ∈ K, f j x ≤ hi j)) :
    (max 0 (1 - ∑ i, (hi i-lo i)/rangeWidth K (f i)))^2 * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal := by
  exact FiniteDimensionalInductionBoundary.bound_at_index hm hK hconv hne f lo hi horder hW j hface

end Plank.PlanarInductionBoundary
