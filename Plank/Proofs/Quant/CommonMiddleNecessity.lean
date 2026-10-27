/- Necessity of ordered stacks in the common minimum/maximum triangle chart. -/
module

public import Plank.Proofs.Quant.CommonVertexTranslationEquality
public import Plank.Convex.PlanarTight.CommonChordClassification
public import Plank.Convex.AffineSlabNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CommonMiddleNecessity

open Set MeasureTheory Function CommonVertex TranslationEquality
open scoped BigOperators

theorem relative_width (C : Config) (b : Fin 3 → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hu : ∀ i, (C.plank i).u = (1, b i)) (i : Fin 3) :
    C.relW i = (C.plank i).hi - (C.plank i).lo := by
  simp only [Config.relW, Plank.relWidth, Proofs.Transport.stdTriangle_width_eq, hu]
  simp only [max_eq_left (hb i).2, max_eq_right zero_le_one,
    min_eq_right (hb i).2, min_eq_left (hb i).1, sub_zero, div_one]

/-- Horizontal escape steps include the boundary direction `b = 1`. -/
def horizontalSteps (C : Config) (i : Fin 3) : ℝ × ℝ := (C.relW i, 0)

/-- Equality exhausts the uncovered set by horizontal translates of the small
triangle. Consequently almost every uncovered point lies below its height. -/
theorem gap_below (C : Config) (b : Fin 3 → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hu : ∀ i, (C.plank i).u = (1, b i)) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C) :
    ∀ᵐ z ∂volume, z ∈ C.uncovered → z.2 ≤ C.deficit := by
  classical
  have hv (i : Fin 3) :
      0 ≤ (horizontalSteps C i).1 ∧ 0 ≤ (horizontalSteps C i).2 :=
    ⟨relWidth_nonneg (C.plank i), le_rfl⟩
  have hself (i : Fin 3) : dot (C.plank i).u (horizontalSteps C i) =
      (C.plank i).hi - (C.plank i).lo := by
    simpa [hu, horizontalSteps, dot] using relative_width C b hb hu i
  have hcross (i j : Fin 3) : 0 ≤ dot (C.plank i).u (horizontalSteps C j) := by
    simpa only [hu, horizontalSteps, dot, mul_zero, add_zero, one_mul, Config.relW]
      using relWidth_nonneg (C.plank j)
  have hTfin : volume stdTriangle.set ≠ ⊤ := by
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  have hassign : ∀ z ∈ RowDeletion.triangle C.deficit,
      ∃ s, z + shift (horizontalSteps C) s ∈ Plank.LinearBands.weakCell
        (fun i => dot (C.plank i).u) (fun i => (C.plank i).lo)
        (fun i => (C.plank i).hi) s := by
    intro z _
    obtain ⟨s, hh, hl⟩ := exists_side_assignment C.plank (horizontalSteps C) hself hcross z
    refine ⟨s, fun i => ?_⟩
    by_cases hi : i ∈ s
    · simpa only [hi, ↓reduceIte] using (hh i hi).le
    · simpa only [hi, ↓reduceIte] using hl i hi
  have hinside (s : Finset (Fin 3)) (z : ℝ × ℝ)
      (hz : z ∈ RowDeletion.triangle C.deficit) :
      z + shift (horizontalSteps C) s ∈ stdTriangle.set := by
    apply shifted_mem_triangle (horizontalSteps C) hv s
    simpa only [horizontalSteps, add_zero, Config.deficit, Config.sumRelW] using hz
  have hpartition := (closed_gap_measure_eq_iff volume
    (fun i => dot (C.plank i).u) (fun i => (Proofs.GapCells.continuous_dot _).measurable)
    (fun i => (C.plank i).lo) (fun i => (C.plank i).hi) (fun i => (C.plank i).lo_le_hi)
    (fun i => volume_line_zero (C.plank i).u_ne_zero _)
    (fun i => volume_line_zero (C.plank i).u_ne_zero _)
    (RowDeletion.triangle C.deficit) (RowDeletion.measurableSet_triangle _)
    (shift (horizontalSteps C)) hassign stdTriangle.set hTfin hinside).mp
      ((CommonVertexTranslationEquality.equality_iff_core_measure C hδ).mp he)
  filter_upwards [hpartition.2] with z hz hgap
  obtain ⟨s, hs⟩ := mem_iUnion.mp ((iff_of_eq hz).mpr hgap)
  have hc := hs.1
  have hzero : (shift (horizontalSteps C) s).2 = 0 := by
    simp [shift_snd, horizontalSteps]
  change 0 ≤ z.1 - (shift (horizontalSteps C) s).1 ∧
    0 ≤ z.2 - (shift (horizontalSteps C) s).2 ∧
    z.1 - (shift (horizontalSteps C) s).1 +
      (z.2 - (shift (horizontalSteps C) s).2) ≤ C.deficit at hc
  rw [hzero, sub_zero] at hc
  linarith only [hc.1, hc.2.2]

end Quant.CommonMiddleNecessity

/-- info: 'Quant.CommonMiddleNecessity.gap_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleNecessity.gap_below
