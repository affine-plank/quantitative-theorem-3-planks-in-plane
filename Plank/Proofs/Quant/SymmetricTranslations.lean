module
/-
# A finite symmetric potential and area-preserving translations

Weighted symmetry of the escape interactions supplies a maximizing side
assignment. Disjoint strict sign cells turn any such finite translation
construction into an area lower bound, with closed boundaries removed by
nullity of affine lines.
-/
public import Plank.Proofs.Quant.CommonVertex
public import Plank.Convex.BangMap

@[expose] public section

noncomputable section

namespace Quant.SymmetricTranslations

open Set MeasureTheory Function CommonVertex

variable {ι : Type*}

abbrev score (a : ι → ℝ) (b : ι → ι → ℝ) (s : Finset ι) : ℝ :=
  Plank.SymmetricSubset.score a b s

theorem score_insert [DecidableEq ι] (a : ι → ℝ) (b : ι → ι → ℝ)
    (hsym : ∀ i j, b i j = b j i) (hdiag : ∀ i, b i i = 0)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    score a b (insert i s) = score a b s + a i + s.sum (b i) :=
  Plank.SymmetricSubset.score_insert a b hsym hdiag s i hi

theorem dot_shift (u : ℝ × ℝ) (v : ι → ℝ × ℝ) (s : Finset ι) :
    dot u (shift v s) = s.sum (fun i => dot u (v i)) := by
  simp only [dot, shift_fst, shift_snd, Finset.mul_sum, Finset.sum_add_distrib]

/-- A finite version of the Bang maximization argument. It requires weighted
symmetry, but no separately constructed inner product. -/
theorem exists_side_assignment [Fintype ι] (p : ι → Plank) (v : ι → ℝ × ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hself : ∀ i, dot (p i).u (v i) = (p i).hi - (p i).lo)
    (hsym : ∀ i j, w i * dot (p i).u (v j) = w j * dot (p j).u (v i))
    (t : ℝ × ℝ) :
    ∃ s : Finset ι,
      (∀ i ∈ s, (p i).hi ≤ dot (p i).u (t + shift v s)) ∧
      (∀ i ∉ s, dot (p i).u (t + shift v s) ≤ (p i).lo) := by
  obtain ⟨s, hhigh, hlow⟩ := Plank.SymmetricSubset.exists_side_assignment w
    (fun i => dot (p i).u t) (fun i => (p i).lo) (fun i => (p i).hi)
    (fun i j => dot (p i).u (v j)) hw hself hsym
  refine ⟨s, ?_, ?_⟩
  · simpa only [Proofs.Basic.dot_add_right, dot_shift] using hhigh
  · simpa only [Proofs.Basic.dot_add_right, dot_shift] using hlow

/-- Disjoint sign cells certify the area of a finite translation construction.
The seed may be any measurable set, and the shifts need not be additive. -/
theorem volume_le_gap_of_translations [Fintype ι] (p : ι → Plank)
    (core : Set (ℝ × ℝ)) (hcore : MeasurableSet core)
    (v : Finset ι → ℝ × ℝ)
    (hassign : ∀ t ∈ core, ∃ s : Finset ι,
      (∀ i ∈ s, (p i).hi ≤ dot (p i).u (t + v s)) ∧
      (∀ i ∉ s, dot (p i).u (t + v s) ≤ (p i).lo))
    (hinside : ∀ s t, t ∈ core → t + v s ∈ stdTriangle.set) :
    volume core ≤ volume (stdTriangle.set \ ⋃ i, (p i).set) := by
  classical
  apply Plank.LinearBands.measure_le_closed_gap_of_translations volume
    (fun i => dot (p i).u) (fun i => (Proofs.GapCells.continuous_dot (p i).u).measurable)
    (fun i => (p i).lo) (fun i => (p i).hi) (fun i => (p i).lo_le_hi)
    (fun i => volume_line_zero (p i).u_ne_zero (p i).lo)
    (fun i => volume_line_zero (p i).u_ne_zero (p i).hi) core hcore v
  · intro t ht
    obtain ⟨s, hhigh, hlow⟩ := hassign t ht
    refine ⟨s, ?_⟩
    intro i
    by_cases his : i ∈ s
    · simpa only [his, ↓reduceIte] using hhigh i his
    · simpa only [his, ↓reduceIte] using hlow i his
  · exact hinside

end Quant.SymmetricTranslations
