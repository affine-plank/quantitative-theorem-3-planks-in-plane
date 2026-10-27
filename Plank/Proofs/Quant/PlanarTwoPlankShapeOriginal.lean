/- Four-vertex rigidity for actual two-plank equality in original coordinates. -/
module

public import Plank.Proofs.Quant.PlanarTwoPlankFourVertices
public import Plank.Proofs.Quant.PlanarCellNormalization
public import Plank.Proofs.Quant.PlanarFourCellShape

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTwoPlankShapeOriginal

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarNormalization
open Plank.Convex.DeficientHeightTilt

/-- Every actual two-plank equality with 0<R<1 has a body which is
the convex hull of at most four points. Only compactness, convexity,
positive area, ordered windows and positive directional ranges are assumed.
This is a necessary shape theorem, not sufficiency of arbitrary placements. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨g,q,hunit,hnorm,horder,hbudget,hgap,_⟩ :=
    PlanarCellNormalization.normalize_with_cells hK hne f p ho hW
  have hgW : ∀ i, 0 < rangeWidth K (g i) := by intro i; rw [hunit]; exact zero_lt_one
  have hqR : budget K g q < 1 := by rwa [hbudget]
  have hqeq : gapArea K g q = (1-budget K g q)^2*(volume K).toReal := by
    rwa [hgap,hbudget]
  let q' := clipEndpoints q
  have hq' : q' ∈ domain K g := clipEndpoints_mem_domain g hgW q horder hqR.le
  have hgclip : gapArea K g q' = gapArea K g q := gapArea_clip hne g hgW hnorm q
  have hble : budget K g q' ≤ budget K g q := budget_clip_le g hgW q horder
  have hbclip : budget K g q' = budget K g q := by
    have hh := PlanarTwoPlank.sharpPlanarBound_two K hK hconv hne g q'.1 q'.2
      (fun i => (hq'.1 i).2.1) hgW
    change (max 0 (1-budget K g q'))^2*(volume K).toReal ≤ gapArea K g q' at hh
    rw [max_eq_right (sub_nonneg.mpr (hble.trans hqR.le)),hgclip,hqeq] at hh
    have hs := (mul_le_mul_iff_left₀ hV).mp hh
    have hl := (sq_le_sq₀ (sub_nonneg.mpr (hble.trans hqR.le))
      (sub_pos.mpr hqR).le).mp hs
    exact le_antisymm hble (by linarith only [hl])
  apply PlanarTwoPlankFourVertices.four_vertices hK hconv hne hV g
    (PlanarFourCellShape.ranges_of_unit hK hne g hnorm hunit) q' hq'
  · rwa [hbclip,hbudget]
  · rwa [hbclip,hbudget]
  · rwa [hgclip,hbclip,hgap,hbudget]

end Plank.PlanarTwoPlankShapeOriginal

/-- info: 'Plank.PlanarTwoPlankShapeOriginal.four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarTwoPlankShapeOriginal.four_vertices
