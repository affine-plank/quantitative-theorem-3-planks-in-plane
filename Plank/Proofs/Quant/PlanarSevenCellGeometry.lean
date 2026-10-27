/- Seven actual positive cells force pair containment and no triple intersection. -/
module

public import Plank.Proofs.Quant.PlanarPairContainment
public import Plank.Proofs.Quant.PlanarSevenCellReduction
public import Plank.Proofs.Quant.PlanarSignPatterns
public import ResearchFormalized.Algebra.SignedSum
import Mathlib.Tactic.FinCases

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenCellGeometry

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarPairContainment
open PlanarCounterexampleChart PlanarPositiveCellRank PlanarSevenCellReduction
open PlanarParameterDomain (Endpoints)

def positiveCells (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3) :
    Finset (Finset (Fin 3)) :=
  Finset.univ.filter (fun s => 0 < (volume (signCell K f e.1 e.2 s)).toReal)

theorem mem_positiveCells (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (e : Endpoints 3) (s : Finset (Fin 3)) :
    s ∈ positiveCells K f e ↔ 0 < (volume (signCell K f e.1 e.2 s)).toReal := by
  simp [positiveCells]

theorem corners_of_seven (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (e : Endpoints 3) (hcount : 7 ≤ (positiveCells K f e).card)
    (i j : Fin 3) (hij : i ≠ j) :
    ∀ b c : Bool, ∃ x ∈ K,
      (if b then e.2 i ≤ f i x else f i x ≤ e.1 i) ∧
      (if c then e.2 j ≤ f j x else f j x ≤ e.1 j) := by
  intro b c
  obtain ⟨s, hs, hsi, hsj⟩ := exists_pair_pattern (positiveCells K f e) hcount i j hij b c
  obtain ⟨x, hx⟩ := PlanarCellChartCalculus.nonempty_of_area_pos K f s e
    ((mem_positiveCells K f e s).mp hs)
  refine ⟨x, hx.1, ?_, ?_⟩
  · simpa only [hsi] using hx.2 i
  · simpa only [hsj] using hx.2 j

/-- The entire intersection of any pair of transverse planks lies in the
closed convex body when seven actual exterior cells have positive area. -/
theorem pair_subset_of_seven {K : Set Point} (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3)
    (hcount : 7 ≤ (positiveCells K f e).card) (i j : Fin 3) (hij : i ≠ j)
    (hcross : PlanarDirectionDerivatives.cross (f i) (f j) ≠ 0) :
    {x | e.1 i ≤ f i x ∧ f i x ≤ e.2 i} ∩
      {x | e.1 j ≤ f j x ∧ f j x ≤ e.2 j} ⊆ K :=
  pair_subset_of_corners hclosed hconv (f i) (f j) hcross _ _ _ _
    (corners_of_seven K f e hcount i j hij)

/-- A strict exterior cell directed along a constant affine relation is
empty if a point lies in all the closed planks. Zero coefficients are allowed. -/
theorem strictCell_empty_of_triple_relation {κ : Type*} [Fintype κ]
    (f : κ → Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ) (s : Finset κ)
    (a : κ → ℝ) (ha : ∃ i, a i ≠ 0) (d : ℝ) (hrel : ∀ x, ∑ i, a i*f i x = d)
    (hsign : ∀ i, (0 < a i → i ∈ s) ∧ (a i < 0 → i ∉ s))
    (y : Point) (hy : ∀ i, lo i ≤ f i y ∧ f i y ≤ hi i) :
    LinearBands.strictCell (fun i x => f i x) lo hi s = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := ResearchFormalized.sum_mul_lt_sum_mul_of_signs a
    (fun i => f i y) (fun i => f i x) ha fun i => by
      constructor
      · intro hp
        exact (hy i).2.trans_lt (by simpa only [(hsign i).1 hp, ite_true] using hx i)
      · intro hn
        exact (show f i x < lo i by
          simpa only [(hsign i).2 hn, ite_false] using hx i).trans_le (hy i).1
  rw [hrel, hrel] at hh
  exact lt_irrefl d hh

/-- Closing null affine boundaries cannot give positive area to an empty
strict exterior cell. -/
theorem area_zero_of_strictCell_empty {κ : Type*} [Fintype κ] (K : Set Point)
    (f : κ → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : κ → ℝ) (s : Finset κ)
    (hs : LinearBands.strictCell (fun i x => f i x) lo hi s = ∅) :
    (volume (signCell K f lo hi s)).toReal = 0 := by
  rw [← measure_strict_eq_signCell K f hf lo hi s, hs]
  simp

/-- Seven positive cells exclude a common point of all three planks in
the whole plane, including points outside the body. -/
theorem triple_empty_of_seven (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (e : Endpoints 3)
    (hcount : 7 ≤ (positiveCells K f e).card) :
    {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i} = ∅ := by
  classical
  obtain ⟨a, ha, d, hrel⟩ := Plank.Convex.PlanarAffineRelation.exists_relation f
  let s := Finset.univ.filter (fun i => 0 < a i)
  have hsign : ∀ i, (0 < a i → i ∈ s) ∧ (a i < 0 → i ∉ s) := by
    intro i
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨id, fun hn => not_lt_of_ge hn.le⟩
  have hasign : ∀ i, (0 < -a i → i ∈ sᶜ) ∧ (-a i < 0 → i ∉ sᶜ) := by
    intro i
    simp only [Finset.mem_compl, s, Finset.mem_filter, Finset.mem_univ, true_and, not_not]
    constructor <;> intro hh <;> linarith
  have harel : ∀ x, ∑ i, (-a i)*f i x = -d := by
    intro x
    simpa only [neg_mul, Finset.sum_neg_distrib] using congrArg Neg.neg (hrel x)
  have hane : ∃ i, (-a i) ≠ 0 := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨i, neg_ne_zero.mpr hi⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hs := area_zero_of_strictCell_empty K f hf e.1 e.2 s
    (strictCell_empty_of_triple_relation f e.1 e.2 s a ha d hrel hsign y hy)
  have ht := area_zero_of_strictCell_empty K f hf e.1 e.2 sᶜ
    (strictCell_empty_of_triple_relation f e.1 e.2 sᶜ (fun i => -a i) hane (-d) harel hasign y hy)
  rcases mem_or_mem_of_seven (positiveCells K f e) hcount s sᶜ ne_compl_self with hmem | hmem
  · have hp := (mem_positiveCells K f e s).mp hmem
    simp [hs] at hp
  · have hp := (mem_positiveCells K f e sᶜ).mp hmem
    simp [ht] at hp

/-- Every open-chart point has the seven actual positive cells identified
by the preceding rank and limit argument. No endpoint ordering is needed. -/
theorem chart_positive_count {K : Set Point} {f : Fin 3 → Point →ᵃ[ℝ] ℝ}
    (ch : CounterexampleChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (e : Endpoints 3) (he : e ∈ ch.chart.region) :
    (positiveCells K f e).card = 7 := by
  have hh := counterexample_cell_count_seven ch hK hconv hV
  simpa only [Cells, Fintype.card_coe, activeCells_eq_positive ch hK hconv e he,
    positiveCells] using hh

/-- The actual counterexample chart supplies every pair containment. -/
theorem chart_pair_subset {K : Set Point} {f : Fin 3 → Point →ᵃ[ℝ] ℝ}
    (ch : CounterexampleChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (e : Endpoints 3) (he : e ∈ ch.chart.region)
    (i j : Fin 3) (hij : i ≠ j)
    (hcross : PlanarDirectionDerivatives.cross (f i) (f j) ≠ 0) :
    {x | e.1 i ≤ f i x ∧ f i x ≤ e.2 i} ∩
      {x | e.1 j ≤ f j x ∧ f j x ≤ e.2 j} ⊆ K := by
  apply pair_subset_of_seven hK.isClosed hconv f e _ i j hij hcross
  rw [chart_positive_count ch hK hconv hV e he]

/-- The actual counterexample chart supplies emptiness of the full triple
intersection. Positive widths here are the actual directional ranges. -/
theorem chart_triple_empty {K : Set Point} {f : Fin 3 → Point →ᵃ[ℝ] ℝ}
    (ch : CounterexampleChart K f) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (hne : K.Nonempty)
    (hf : ∀ i, 0 < Plank.Convex.DeficientHeightTilt.rangeWidth K (f i))
    (e : Endpoints 3) (he : e ∈ ch.chart.region) :
    {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i} = ∅ := by
  apply triple_empty_of_seven K f (fun i => linear_ne_zero_of_rangeWidth_pos hne (f i) (hf i)) e
  rw [chart_positive_count ch hK hconv hV e he]

end Plank.PlanarSevenCellGeometry
