/- Actual affine normalization preserves every exterior sign cell. -/
module

public import Plank.Proofs.Quant.PlanarNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellNormalization

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open Plank.Convex.DeficientHeightTilt

/-- Normalize any finite family using actual attained support values.
Both the covered union and every closed exterior cell are unchanged as
sets in the original plane. No clipping or positivity of window widths
is required. -/
theorem normalize_with_cells {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (hne : K.Nonempty) (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (horder : ∀ i, p.1 i ≤ p.2 i) (hW : ∀ i, 0 < rangeWidth K (f i)) :
    ∃ (g : Fin m → Point →ᵃ[ℝ] ℝ) (q : Endpoints m),
      (∀ i, rangeWidth K (g i) = 1) ∧
      (∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1) ∧
      (∀ i, q.1 i ≤ q.2 i) ∧ budget K g q = budget K f p ∧
      gapArea K g q = gapArea K f p ∧
      ∀ s, signCell K g q.1 q.2 s = signCell K f p.1 p.2 s := by
  classical
  choose g c happly hbounds hunit using fun i =>
    PlanarNormalization.exists_unit_form hK hne (f i) (hW i)
  let q : Endpoints m := (fun i => (p.1 i-c i)/rangeWidth K (f i),
    fun i => (p.2 i-c i)/rangeWidth K (f i))
  have hordered : ∀ i, q.1 i ≤ q.2 i := by
    intro i
    apply (div_le_div_iff_of_pos_right (hW i)).mpr
    exact sub_le_sub_right (horder i) _
  have hbudget : budget K g q = budget K f p := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit]
    dsimp only [q]
    ring
  have hset : (⋃ i, {x | q.1 i ≤ g i x ∧ g i x ≤ q.2 i}) =
      ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    apply exists_congr
    intro i
    rw [happly]
    dsimp only [q]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  refine ⟨g,q,hunit,hbounds,hordered,hbudget,?_,?_⟩
  · unfold gapArea
    rw [hset]
  · intro s
    ext x
    simp only [signCell,mem_inter_iff,LinearBands.weakCell,mem_ofPred_eq]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    split_ifs <;> rw [happly] <;> dsimp only [q] <;>
      simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]

end Plank.PlanarCellNormalization

/-- info: 'Plank.PlanarCellNormalization.normalize_with_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCellNormalization.normalize_with_cells
