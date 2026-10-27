/- An exhaustive translation-partition criterion in the strict ABC chart.
It has no clipping or minimum assumptions. Turning this criterion into a
list of parameterized geometric families remains a separate obligation. -/
module

public import Plank.Proofs.Quant.CyclicEqualityObstruction
public import Plank.Proofs.Quant.TranslationEquality

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CyclicTranslationEquality

open Set MeasureTheory Function CommonVertex OrdinalArea CyclicArea TranslationEquality

def translations (C : Config) (s : Finset (Fin 3)) : ℝ × ℝ :=
  base C+shift (steps (widths C)) s

def exteriorCells (C : Config) : Finset (Fin 3) → Set (ℝ × ℝ) :=
  Plank.LinearBands.strictCell (fun i => dot (C.plank i).u)
    (fun i => (C.plank i).lo) (fun i => (C.plank i).hi)

/-- The eight translated source pieces partition the deficit triangle and
exhaust the actual gap, up to null boundaries. Duplication of seed area is
excluded explicitly. These are geometric partition conditions, not a
restatement of the quantitative area equation. -/
def TranslationPartition (C : Config) : Prop :=
  Pairwise (AEDisjoint volume on
    sourcePiece (RowDeletion.triangle C.deficit) (translations C) (exteriorCells C)) ∧
  (⋃ s, targetPiece (RowDeletion.triangle C.deficit) (translations C)
    (exteriorCells C) s) =ᵐ[volume] C.uncovered

theorem weak_assignments_of_no_bad_seed (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1))
    (hn : ∀ z ∈ RowDeletion.triangle C.deficit, z ∉ badSeeds C b a c) :
    ∀ z ∈ RowDeletion.triangle C.deficit, ∃ s,
      z+translations C s ∈ Plank.LinearBands.weakCell
        (fun i => dot (C.plank i).u) (fun i => (C.plank i).lo) (fun i => (C.plank i).hi) s := by
  classical
  let r := widths C
  have hr : ∀ i, 0 ≤ r i := fun i => sub_nonneg.mpr (C.plank i).lo_le_hi
  have hu : ∀ i, (C.plank i).u = ![(1,b),(a,1),(c,c-1)] i := by
    intro i
    fin_cases i
    · exact hu₀
    · exact hu₁
    · exact hu₂
  have hself : ∀ i, dot (C.plank i).u (steps r i) = (C.plank i).hi-(C.plank i).lo := by
    intro i
    rw [hu]
    change dot (![(1,b),(a,1),(c,c-1)] i) (steps r i) = r i
    fin_cases i <;> dsimp [steps,dot] <;> ring
  have hmatrix : ∀ i j, OrdinalTranslations.interaction C.plank (steps r) i j =
      OrdinalMatrix.matrix (b*r 1) ((1-b)*r 2) (a*r 0) ((1-a)*r 2)
        (c*r 0) ((1-c)*r 1) i j := by
    intro i j
    simp only [OrdinalTranslations.interaction,hu]
    fin_cases i <;> fin_cases j <;> norm_num [steps,OrdinalMatrix.matrix,dot] <;> ring
  intro z hz
  have hpat := (CyclicAssignment.pattern_iff_not_bad
    (mul_nonneg hb.1.le (hr 1)) (mul_nonneg (sub_nonneg.mpr hb.2.le) (hr 2))
    (mul_nonneg ha.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr ha.2.le) (hr 2))
    (mul_nonneg hc.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr hc.2.le) (hr 1))).mpr (hn z hz)
  obtain ⟨s,hhigh,hlow⟩ := CyclicAssignment.exists_side_assignment
    C.plank (steps r) hself _ _ _ _ _ _ hmatrix (z+base C) hpat
  refine ⟨s,fun i => ?_⟩
  by_cases his : i ∈ s
  · simpa only [his,↓reduceIte,translations,← add_assoc] using hhigh i his
  · simpa only [his,↓reduceIte,translations,← add_assoc] using hlow i his

/-- Both directions for arbitrary endpoints in the strict ABC chart.
The right side consists of two explicit obstruction boxes and the eight
translation pieces. No NoClippingRegion hypothesis is present. -/
theorem equality_iff_partition (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔
      (∀ z ∈ RowDeletion.triangle C.deficit, z ∉ badSeeds C b a c) ∧
      TranslationPartition C := by
  have hTfin : volume stdTriangle.set ≠ ⊤ := by
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  have hgapfin : volume C.uncovered ≠ ⊤ :=
    ne_top_of_le_ne_top hTfin (measure_mono sdiff_subset)
  have harea : TriangleEqualityReductions.Equality C ↔
      volume (RowDeletion.triangle C.deficit) = volume C.uncovered := by
    rw [RowDeletion.volume_triangle hδ]
    constructor
    · intro he
      have hh := congrArg ENNReal.ofReal he
      dsimp [Config.gapArea] at hh
      rw [ENNReal.ofReal_toReal hgapfin,max_eq_right hδ.le] at hh
      simpa only [div_eq_mul_inv,one_mul] using hh.symm
    · intro he
      have hh := congrArg ENNReal.toReal he
      rw [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (by norm_num))] at hh
      rw [TriangleEqualityReductions.Equality,max_eq_right hδ.le]
      change (volume C.uncovered).toReal = _
      linarith only [hh]
  have hpart (hn : ∀ z ∈ RowDeletion.triangle C.deficit, z ∉ badSeeds C b a c) :
      TriangleEqualityReductions.Equality C ↔ TranslationPartition C := by
    rw [harea]
    apply closed_gap_measure_eq_iff volume
      (fun i => dot (C.plank i).u) (fun i => (Proofs.GapCells.continuous_dot _).measurable)
      (fun i => (C.plank i).lo) (fun i => (C.plank i).hi) (fun i => (C.plank i).lo_le_hi)
      (fun i => volume_line_zero (C.plank i).u_ne_zero _)
      (fun i => volume_line_zero (C.plank i).u_ne_zero _)
      (RowDeletion.triangle C.deficit) (RowDeletion.measurableSet_triangle _) (translations C)
      (weak_assignments_of_no_bad_seed C hb ha hc hu₀ hu₁ hu₂ hn) stdTriangle.set hTfin
    intro s z hz
    apply translated_mem_triangle (widths C)
      (fun i => sub_nonneg.mpr (C.plank i).lo_le_hi) s z
    simpa only [CyclicArea.deficit_eq C hb ha hc hu₀ hu₁ hu₂] using hz
  constructor
  · intro he
    have hn := CyclicEqualityObstruction.equality_has_no_bad_seed C hb ha hc hu₀ hu₁ hu₂ hδ he
    exact ⟨hn,(hpart hn).mp he⟩
  · rintro ⟨hn,hp⟩
    exact (hpart hn).mpr hp

end Quant.CyclicTranslationEquality

/-- info: 'Quant.CyclicTranslationEquality.equality_iff_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicTranslationEquality.equality_iff_partition
