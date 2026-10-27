/- Original-coordinate equality classification for contained pair overlaps. -/
module

public import Plank.Proofs.Quant.PlanarPairContainedEquality
public import Plank.Proofs.Quant.PlanarTransverseNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPairContainedOriginal

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open PlanarSevenCellArea PlanarDirectionDerivatives PlanarNormalization PlanarTransverseNormalization
open PlanarAffineEquality PlanarFourPointClassification
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- The normalized theorem applies to the original planks: normalization
preserves every individual plank as a set, and hence both overlap conditions. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0)
    (heq : Equality K f p.1 p.2) : ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  classical
  choose g a hg hnorm hunit using fun i => exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints 3 := (fun i => (p.1 i-a i)/rangeWidth K (f i),
    fun i => (p.2 i-a i)/rangeWidth K (f i))
  have hqo (i) : q.1 i < q.2 i :=
    (div_lt_div_iff_of_pos_right (hW i)).mpr (sub_lt_sub_right (ho i) _)
  have hb (i) : plank (g i) (q.1 i) (q.2 i) = plank (f i) (p.1 i) (p.2 i) := by
    ext x
    simp only [plank,mem_ofPred_eq,hg]
    dsimp only [q]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  have hbudget : budget K g q = budget K f p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit]
    dsimp only [q]
    ring
  have hgap : gapArea K g q = gapArea K f p := by
    change (volume (K \ ⋃ i, plank (g i) (q.1 i) (q.2 i))).toReal =
      (volume (K \ ⋃ i, plank (f i) (p.1 i) (p.2 i))).toReal
    simp only [hb]
  have hgpairs (i j) (hij : i ≠ j) : cross (g i) (g j) ≠ 0 := by
    rw [cross_scaled_pair (f i) (g i) (f j) (g j) _ _
      (linear_eq_of_formula _ _ _ _ (hg i)) (linear_eq_of_formula _ _ _ _ (hg j))]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero (hW i).ne') (inv_ne_zero (hW j).ne'))
      (hpairs i j hij)
  have hct (i j) (hij : i ≠ j) :
      plank (g i) (q.1 i) (q.2 i) ∩ plank (g j) (q.1 j) (q.2 j) ⊆ K := by
    rw [hb,hb]
    exact hcontain i j hij
  have ht : {x | ∀ i, q.1 i ≤ g i x ∧ g i x ≤ q.2 i} =
      {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
    ext x
    simp only [mem_ofPred_eq]
    apply forall_congr'
    intro i
    change x ∈ plank (g i) (q.1 i) (q.2 i) ↔ x ∈ plank (f i) (p.1 i) (p.2 i)
    rw [hb]
  apply PlanarPairContainedEquality.four_vertices hK hc hne hV g hnorm hunit hgpairs q hqo
    (by rwa [hbudget]) hct (by rwa [ht])
  change gapArea K g q = (max 0 (1-budget K g q))^2*(volume K).toReal
  rwa [hgap,hbudget]

/-- Exhaustive equality in this geometric stratum, without any assumption
on the number of positive cells, body shape, normalization or supporting faces.
Both containment and zero triple area are explicit geometric hypotheses. -/
theorem equality_iff {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i < p.2 i)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (hR : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0) :
    Equality K f p.1 p.2 ↔ Family K f p.1 p.2 := by
  constructor
  · intro he
    exact (equality_iff_of_four_vertices hV
      (four_vertices hK hc hne hV f p hW ho hpairs hR hcontain htriple he)
      f p.1 p.2 hW (fun i => (ho i).le)).mp he
  · exact family_sound f p.1 p.2 hW (fun i => (ho i).le)

end Plank.PlanarPairContainedOriginal

/-- info: 'Plank.PlanarPairContainedOriginal.equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarPairContainedOriginal.equality_iff
