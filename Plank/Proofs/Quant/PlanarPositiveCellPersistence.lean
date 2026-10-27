/- Persistence of positive exterior cells for arbitrary normalized convex bodies. -/
module

public import Plank.Proofs.Quant.PlanarSevenCellGeometry
public import Plank.Proofs.Quant.PlanarGapAnalysis

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPositiveCellPersistence

open Set MeasureTheory Filter Topology PlanarQuantitative PlanarGapCells
open PlanarSevenCellGeometry PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt

/-- Every actual exterior-cell area is continuous in the endpoints. The
body need not be a polygon, and the directions need not be independent. -/
theorem continuous_cell_area {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (f : ι → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) (s : Finset ι) :
    Continuous (fun e : (ι → ℝ) × (ι → ℝ) =>
      (volume (signCell K f e.1 e.2 s)).toReal) := by
  classical
  let T (e : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
    (fun i => if i ∈ s then -2 else e.1 i, fun i => if i ∈ s then e.2 i else 2)
  have hT : Continuous T := by
    apply Continuous.prodMk <;> apply continuous_pi <;> intro i <;>
      by_cases hi : i ∈ s <;> simp only [hi,↓reduceIte] <;> fun_prop
  have he (e : (ι → ℝ) × (ι → ℝ)) :
      K \ ⋃ i, {x | (T e).1 i ≤ f i x ∧ f i x ≤ (T e).2 i} =
        K ∩ LinearBands.strictCell (fun i x => f i x) e.1 e.2 s := by
    ext x
    simp only [Set.mem_sdiff,mem_iUnion,mem_ofPred_eq,not_exists,not_and,
      mem_inter_iff,LinearBands.strictCell]
    apply and_congr_right
    intro hx
    apply forall_congr'
    intro i
    have hb := hnorm i x hx
    by_cases hi : i ∈ s <;> simp only [T,hi,↓reduceIte] <;> constructor
    · intro h
      exact lt_of_not_ge (h (by linarith only [hb.1]))
    · intro h _
      exact not_le_of_gt h
    · intro h
      exact lt_of_not_ge (fun hh => h hh (by linarith only [hb.2]))
    · intro h hh
      exact (not_le_of_gt h hh).elim
  have hh := (PlanarGapAnalysis.continuous_gap_area hK hne f hW).comp hT
  simpa only [Function.comp_def,he,measure_strict_eq_signCell K f
    (fun i => linear_ne_zero_of_rangeWidth_pos hne (f i) (hW i))] using hh

/-- Every currently positive exterior cell remains positive in a whole
endpoint neighborhood. This is genuine area persistence, not a genericity
or fixed-combinatorial-chart assumption. -/
theorem eventually_positive_subset {K : Set Point} (hK : IsCompact K)
    (hne : K.Nonempty) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) (p : Endpoints 3) :
    ∀ᶠ e in 𝓝 p, positiveCells K f p ⊆ positiveCells K f e := by
  classical
  have hs (s : Finset (Fin 3)) : ∀ᶠ e in 𝓝 p,
      s ∈ positiveCells K f p → s ∈ positiveCells K f e := by
    by_cases hp : s ∈ positiveCells K f p
    · have hh := (continuous_cell_area hK hne f hW hnorm s).continuousAt.eventually_const_lt
        ((mem_positiveCells K f p s).mp hp)
      exact hh.mono fun e he _ => (mem_positiveCells K f e s).mpr he
    · exact Filter.Eventually.of_forall fun _ h => (hp h).elim
  exact Filter.eventually_all.mpr hs

end Plank.PlanarPositiveCellPersistence

/-- info: 'Plank.PlanarPositiveCellPersistence.eventually_positive_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarPositiveCellPersistence.eventually_positive_subset
