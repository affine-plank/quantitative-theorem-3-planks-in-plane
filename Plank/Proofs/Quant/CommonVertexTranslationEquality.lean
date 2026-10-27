/- Equality conditions for the common-extreme-vertex translation proof.
All endpoints and zero widths are allowed. -/
module

public import Plank.Proofs.Quant.CommonVertexChambers
public import Plank.Proofs.Quant.TriangleEqualityReductions
public import Plank.Proofs.Quant.TranslationEquality

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CommonVertexTranslationEquality

open Set MeasureTheory Function CommonVertex TranslationEquality

/-- Move equivalence preserves the actual equality statement. -/
theorem equality_iff_of_equiv {C D : Config} (e : C.Equiv D) :
    TriangleEqualityReductions.Equality C ↔ TriangleEqualityReductions.Equality D := by
  simp only [TriangleEqualityReductions.Equality,Config.deficit,e.gapArea_eq,e.sumRelW_eq]

theorem equality_iff_core_measure (C : Config) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔
      volume (RowDeletion.triangle C.deficit) = volume C.uncovered := by
  have hfin : volume C.uncovered ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
      (measure_mono sdiff_subset)
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  rw [RowDeletion.volume_triangle hδ]
  constructor
  · intro he
    have hh := congrArg ENNReal.ofReal he
    dsimp [Config.gapArea] at hh
    rw [ENNReal.ofReal_toReal hfin,max_eq_right hδ.le] at hh
    simpa only [div_eq_mul_inv,one_mul] using hh.symm
  · intro he
    have hh := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (by norm_num))] at hh
    rw [TriangleEqualityReductions.Equality,max_eq_right hδ.le]
    change (volume C.uncovered).toReal = _
    linarith only [hh]

/-- The escape step goes towards a maximizing vertex of the triangle. -/
def steps (C : Config) (i : Fin 3) : ℝ × ℝ :=
  if (C.plank i).u.1 ≤ (C.plank i).u.2 then (0,C.relW i) else (C.relW i,0)

def exteriorCells (C : Config) : Finset (Fin 3) → Set (ℝ × ℝ) :=
  Plank.LinearBands.strictCell (fun i => dot (C.plank i).u)
    (fun i => (C.plank i).lo) (fun i => (C.plank i).hi)

/-- Eight explicit translated pieces, with no duplicated seed area or unused
gap area. It is a geometric criterion, not a scalar area equality. -/
def TranslationPartition (C : Config) : Prop :=
  Pairwise (AEDisjoint volume on sourcePiece (RowDeletion.triangle C.deficit)
    (shift (steps C)) (exteriorCells C)) ∧
  (⋃ s, targetPiece (RowDeletion.triangle C.deficit) (shift (steps C))
    (exteriorCells C) s) =ᵐ[volume] C.uncovered

theorem steps_nonneg (C : Config) (i : Fin 3) :
    0 ≤ (steps C i).1 ∧ 0 ≤ (steps C i).2 := by
  have hr : 0 ≤ C.relW i := relWidth_nonneg (C.plank i)
  dsimp [steps]
  split_ifs <;> simpa using hr

theorem steps_cost (C : Config) (i : Fin 3) :
    (steps C i).1 + (steps C i).2 = C.relW i := by
  dsimp [steps]
  split_ifs <;> simp

theorem steps_self (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2) (i : Fin 3) :
    dot (C.plank i).u (steps C i) = (C.plank i).hi-(C.plank i).lo := by
  have hwidth : stdTriangle.width (C.plank i).u = max (C.plank i).u.1 (C.plank i).u.2 := by
    rw [Proofs.Transport.stdTriangle_width_eq,
      max_eq_right ((hu i).1.trans (le_max_left _ _)),
      min_eq_left (le_min (hu i).1 (hu i).2),sub_zero]
  have hpos : 0 < max (C.plank i).u.1 (C.plank i).u.2 := by
    by_contra h
    have hm := le_of_not_gt h
    exact (C.plank i).u_ne_zero (Prod.ext
      (le_antisymm ((le_max_left _ _).trans hm) (hu i).1)
      (le_antisymm ((le_max_right _ _).trans hm) (hu i).2))
  by_cases h : (C.plank i).u.1 ≤ (C.plank i).u.2
  · have hn : (C.plank i).u.2 ≠ 0 := ne_of_gt (by simpa [max_eq_right h] using hpos)
    simp only [steps,if_pos h,dot,mul_zero,zero_add,Config.relW,Plank.relWidth,
      hwidth,max_eq_right h]
    field_simp
  · have hn : (C.plank i).u.1 ≠ 0 :=
      ne_of_gt (by simpa [max_eq_left (le_of_not_ge h)] using hpos)
    simp only [steps,if_neg h,dot,mul_zero,add_zero,Config.relW,Plank.relWidth,
      hwidth,max_eq_left (le_of_not_ge h)]
    field_simp

/-- The full common-minimum chart, including boundary/repeated directions,
arbitrary endpoints, and zero-width planks. -/
theorem equality_iff_partition (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔ TranslationPartition C := by
  rw [equality_iff_core_measure C hδ]
  have hTfin : volume stdTriangle.set ≠ ⊤ := by
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  refine closed_gap_measure_eq_iff volume
    (fun i => dot (C.plank i).u) (fun i => (Proofs.GapCells.continuous_dot _).measurable)
    (fun i => (C.plank i).lo) (fun i => (C.plank i).hi) (fun i => (C.plank i).lo_le_hi)
    (fun i => volume_line_zero (C.plank i).u_ne_zero _)
    (fun i => volume_line_zero (C.plank i).u_ne_zero _)
    (RowDeletion.triangle C.deficit) (RowDeletion.measurableSet_triangle _)
    (shift (steps C)) ?_ stdTriangle.set hTfin ?_
  · intro z _
    have hc : ∀ i j, 0 ≤ dot (C.plank i).u (steps C j) := fun i j =>
      add_nonneg (mul_nonneg (hu i).1 (steps_nonneg C j).1)
        (mul_nonneg (hu i).2 (steps_nonneg C j).2)
    obtain ⟨s,hh,hl⟩ := exists_side_assignment C.plank (steps C) (steps_self C hu) hc z
    refine ⟨s,fun i => ?_⟩
    by_cases hi : i ∈ s
    · simpa only [hi,↓reduceIte] using (hh i hi).le
    · simpa only [hi,↓reduceIte] using hl i hi
  · intro s z hz
    apply shifted_mem_triangle (steps C) (steps_nonneg C) s
    simpa only [steps_cost,Config.deficit,Config.sumRelW] using hz

end Quant.CommonVertexTranslationEquality

/-- info: 'Quant.CommonVertexTranslationEquality.equality_iff_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonVertexTranslationEquality.equality_iff_partition
