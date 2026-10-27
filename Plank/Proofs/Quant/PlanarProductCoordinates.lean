/- Read the planar quantitative statement in product coordinates using
Mathlib's measure-preserving coordinate equivalence. -/
module
public import Plank.Proofs.Quant.PlanarStatement
public import Plank.Proofs.AffineWidth
public import Mathlib.Topology.Algebra.Module.Equiv.Pi
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
noncomputable section

namespace Plank.PlanarQuantitative
open Set MeasureTheory
open Plank.Convex.DeficientHeightTilt

/-- The same sharp bound in the standard product representation of the plane.
This is coordinate transport for every plank count, with no new geometric input. -/
theorem bound_prod {m : ℕ} (h : SharpPlanarBound m)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin m → (ℝ × ℝ) →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ)
    (hle : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < rangeWidth K (f i)) :
    (max 0 (1 - ∑ i, (hi i-lo i)/rangeWidth K (f i)))^2 * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal := by
  let e := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let a := e.toLinearEquiv.toAffineEquiv
  have hvolume (S : Set (ℝ × ℝ)) : volume (e ⁻¹' S) = volume S :=
    (volume_preserving_finTwoArrow ℝ).measure_preimage_emb
      MeasurableEquiv.finTwoArrow.measurableEmbedding S
  have hwidth (i : Fin m) :
      rangeWidth (e ⁻¹' K) ((f i).comp a.toAffineMap) = rangeWidth K (f i) :=
    Body.width_affine_preimage a K (f i)
  have hh := h (e ⁻¹' K) (e.toHomeomorph.isCompact_preimage.mpr hK)
    (hc.affine_preimage a.toAffineMap) (hne.preimage e.surjective)
    (fun i => (f i).comp a.toAffineMap) lo hi hle (fun i => by rw [hwidth]; exact hW i)
  have hgap :
      (e ⁻¹' K) \ ⋃ i, {x | lo i ≤ (f i).comp a.toAffineMap x ∧
        (f i).comp a.toAffineMap x ≤ hi i} =
      e ⁻¹' (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) := by
    ext x
    simp only [mem_sdiff, mem_preimage, mem_iUnion, mem_ofPred_eq, AffineMap.comp_apply]
    rfl
  simpa only [hwidth,hgap,hvolume] using hh

end Plank.PlanarQuantitative

#print axioms Plank.PlanarQuantitative.bound_prod
