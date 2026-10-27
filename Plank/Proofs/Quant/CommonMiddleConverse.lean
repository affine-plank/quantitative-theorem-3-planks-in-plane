/- Exact ordered-stack area, including endpoint and repeated directions. -/
module

public import Plank.Proofs.Quant.CommonMiddleClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CommonMiddleNecessity

open Set MeasureTheory
open scoped BigOperators

theorem column_plank (C : Config) (b : Fin 3 → ℝ)
    (hu : ∀ i, (C.plank i).u = (1,b i)) (i : Fin 3) (x y : ℝ) :
    (x,y) ∈ (C.plank i).set ↔
      x ∈ Icc ((C.plank i).lo-b i*y) ((C.plank i).hi-b i*y) := by
  change ((C.plank i).lo ≤ dot (C.plank i).u (x,y) ∧
    dot (C.plank i).u (x,y) ≤ (C.plank i).hi) ↔ _
  rw [hu]
  simp only [dot, one_mul, mem_Icc]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

theorem column_uncovered (C : Config) (b : Fin 3 → ℝ)
    (hu : ∀ i, (C.plank i).u = (1,b i)) (σ : Equiv.Perm (Fin 3))
    (y : ℝ) (hy : 0 ≤ y) :
    {x : ℝ | (x,y) ∈ C.uncovered} = Icc 0 (1-y) \
      (Icc ((C.plank (σ 0)).lo-b (σ 0)*y) ((C.plank (σ 0)).hi-b (σ 0)*y) ∪
       Icc ((C.plank (σ 1)).lo-b (σ 1)*y) ((C.plank (σ 1)).hi-b (σ 1)*y) ∪
       Icc ((C.plank (σ 2)).lo-b (σ 2)*y) ((C.plank (σ 2)).hi-b (σ 2)*y)) := by
  have hperm : (⋃ i, (C.plank i).set) =
      (C.plank (σ 0)).set ∪ (C.plank (σ 1)).set ∪ (C.plank (σ 2)).set := by
    ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      obtain ⟨j, rfl⟩ := σ.surjective i
      fin_cases j
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      exacts [⟨σ 0,h⟩,⟨σ 1,h⟩,⟨σ 2,h⟩]
  ext x
  have hT : (x,y) ∈ stdTriangle.set ↔ x ∈ Icc 0 (1-y) := by
    rw [Proofs.Quant.stdTriangle_set_eq]
    change (0 ≤ x ∧ 0 ≤ y ∧ x+y ≤ 1) ↔ 0 ≤ x ∧ x ≤ 1-y
    constructor
    · rintro ⟨hx, _, hs⟩
      exact ⟨hx, by linarith⟩
    · rintro ⟨hx, hs⟩
      exact ⟨hx, hy, by linarith⟩
  simp only [mem_ofPred_eq, Config.uncovered, hperm, mem_sdiff, mem_union,
    hT, column_plank C b hu]

/-- Below height `1-R`, the ordered windows occupy exactly length `R` in
each row. Above that height their overlaps cover the entire row. -/
theorem orderedStack_column_volume (C : Config) (b : Fin 3 → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hu : ∀ i, (C.plank i).u = (1,b i)) (hstack : OrderedStack C b)
    (y : ℝ) (hy : 0 ≤ y) :
    volume {x : ℝ | (x,y) ∈ C.uncovered} = ENNReal.ofReal (C.deficit-y) := by
  obtain ⟨σ,h01,h12,hl0,hh0,hl1,hh1,hl2,hh2⟩ := hstack
  rw [column_uncovered C b hu σ y hy]
  have hw0 := relative_width C b hb hu (σ 0)
  have hw1 := relative_width C b hb hu (σ 1)
  have hw2 := relative_width C b hb hu (σ 2)
  have hsum : C.relW (σ 0) + C.relW (σ 1) + C.relW (σ 2) = C.sumRelW := by
    rw [Config.sumRelW, ← Equiv.sum_comp σ (fun i => C.relW i), Fin.sum_univ_three]
  have hd : C.deficit + C.sumRelW = 1 := by rw [Config.deficit]; ring
  by_cases hlow : y ≤ C.deficit
  · have hs : 0 ≤ C.deficit-y := sub_nonneg.mpr hlow
    have hm := mul_nonneg (hb (σ 0)).1 hs
    have hs01 := mul_le_mul_of_nonneg_right h01 hs
    have hs12 := mul_le_mul_of_nonneg_right h12 hs
    have hM := mul_le_mul_of_nonneg_right (hb (σ 2)).2 hs
    have hlength := Proofs.Quant.volume_Icc_sdiff_three
      (L := 1-y)
      (p₁ := (C.plank (σ 0)).lo-b (σ 0)*y)
      (q₁ := (C.plank (σ 0)).hi-b (σ 0)*y)
      (p₂ := (C.plank (σ 1)).lo-b (σ 1)*y)
      (q₂ := (C.plank (σ 1)).hi-b (σ 1)*y)
      (p₃ := (C.plank (σ 2)).lo-b (σ 2)*y)
      (q₃ := (C.plank (σ 2)).hi-b (σ 2)*y)
      (by nlinarith only [hm,hl0])
      (sub_le_sub_right (C.plank (σ 0)).lo_le_hi _)
      (by nlinarith only [hs01,hh0,hl1])
      (sub_le_sub_right (C.plank (σ 1)).lo_le_hi _)
      (by nlinarith only [hs12,hh1,hl2])
      (sub_le_sub_right (C.plank (σ 2)).lo_le_hi _)
      (by nlinarith only [hM,hh2,hd])
    rw [hlength]
    congr 1
    linarith only [hw0,hw1,hw2,hsum,hd]
  · have hs : C.deficit-y ≤ 0 := by linarith only [hlow]
    have hm := mul_nonpos_of_nonneg_of_nonpos (hb (σ 0)).1 hs
    have hs01 := mul_le_mul_of_nonpos_right h01 hs
    have hs12 := mul_le_mul_of_nonpos_right h12 hs
    have hM := mul_le_mul_of_nonpos_right (hb (σ 2)).2 hs
    have hcover := Proofs.Quant.Icc_subset_union_three
      (L := 1-y)
      (p₁ := (C.plank (σ 0)).lo-b (σ 0)*y)
      (q₁ := (C.plank (σ 0)).hi-b (σ 0)*y)
      (p₂ := (C.plank (σ 1)).lo-b (σ 1)*y)
      (q₂ := (C.plank (σ 1)).hi-b (σ 1)*y)
      (p₃ := (C.plank (σ 2)).lo-b (σ 2)*y)
      (q₃ := (C.plank (σ 2)).hi-b (σ 2)*y)
      (by nlinarith only [hm,hl0])
      (by nlinarith only [hs01,hh0,hl1])
      (by nlinarith only [hs12,hh1,hl2])
      (by nlinarith only [hM,hh2,hd])
    rw [sdiff_eq_empty.mpr hcover, measure_empty, ENNReal.ofReal_eq_zero.mpr hs]

/-- Matching actual area of every ordered stack, including zero widths
when their windows have the displayed stack positions. -/
theorem equality_of_orderedStack (C : Config) (b : Fin 3 → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hu : ∀ i, (C.plank i).u = (1,b i)) (hR1 : C.sumRelW < 1)
    (hstack : OrderedStack C b) : TriangleEqualityReductions.Equality C := by
  apply (CommonVertexTranslationEquality.equality_iff_core_measure C (sub_pos.mpr hR1)).mpr
  have hgap : MeasurableSet C.uncovered :=
    Proofs.Quant.measurableSet_stdTriangle.diff
      (MeasurableSet.iUnion fun i => (Proofs.Quant.isClosed_plank_set (C.plank i)).measurableSet)
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (RowDeletion.measurableSet_triangle _),
    Measure.prod_apply_symm hgap]
  apply lintegral_congr
  intro y
  change volume {x : ℝ | (x,y) ∈ RowDeletion.triangle C.deficit} =
    volume {x : ℝ | (x,y) ∈ C.uncovered}
  by_cases hy : 0 ≤ y
  · rw [RowDeletion.column_triangle hy, orderedStack_column_volume C b hb hu hstack y hy,
      Real.volume_Icc, sub_zero]
  · have hcore : {x : ℝ | (x,y) ∈ RowDeletion.triangle C.deficit} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      exact fun x hx => hy hx.2.1
    have hgap : {x : ℝ | (x,y) ∈ C.uncovered} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have ht := hx.1
      rw [Proofs.Quant.stdTriangle_set_eq] at ht
      exact hy ht.2.1
    rw [hcore,hgap]

/-- Complete equality classification in the normalized shared-extremal-
segment chart, with positive widths and a strictly subcritical budget. -/
theorem equality_iff_orderedStack (C : Config) (b : Fin 3 → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hu : ∀ i, (C.plank i).u = (1,b i))
    (hw : ∀ i, 0 < C.relW i) (hR : 0 < C.sumRelW) (hR1 : C.sumRelW < 1) :
    TriangleEqualityReductions.Equality C ↔ OrderedStack C b :=
  ⟨orderedStack_of_equality C b hb hu hw hR hR1,
    equality_of_orderedStack C b hb hu hR1⟩

end Quant.CommonMiddleNecessity

/-- info: 'Quant.CommonMiddleNecessity.equality_iff_orderedStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleNecessity.equality_iff_orderedStack
