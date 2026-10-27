/- Equality in a finite translation construction is exactly the absence of
duplicated seed area and unused target area. This is a structural criterion;
solving its geometric conditions remains a separate task. -/
module

public import Plank.Proofs.Quant.SymmetricTranslations

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.TranslationEquality

open Set MeasureTheory Function

variable {ι E : Type*} [MeasurableSpace E]

/-- Equality in the finite union bound forces all overlaps to be null. -/
theorem pairwise_null_of_union_measure_eq_sum (μ : Measure E)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, μ (A i) ≠ ⊤)
    (s : Finset ι) (he : μ (⋃ i ∈ s, A i) = ∑ i ∈ s, μ (A i)) :
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j → μ (A i ∩ A j) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    have hU : MeasurableSet (⋃ i ∈ s, A i) :=
      s.finite_toSet.measurableSet_biUnion (fun i _ => hA i)
    have hsum : (∑ i ∈ s, μ (A i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hfin i)
    have hle := measure_biUnion_finset_le s A (μ := μ)
    have hins : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by simp
    rw [hins,Finset.sum_insert has] at he
    have htail : μ (⋃ i ∈ s, A i) = ∑ i ∈ s, μ (A i) := by
      apply le_antisymm hle
      apply (ENNReal.add_le_add_iff_left (hfin a)).mp
      rw [← he]
      exact measure_union_le _ _
    have hdis : μ (A a ∩ ⋃ i ∈ s, A i) = 0 := by
      have hid := measure_union_add_inter (A a) hU (μ := μ)
      rw [he,htail] at hid
      apply (ENNReal.add_right_inj (ENNReal.add_ne_top.mpr ⟨hfin a,hsum⟩)).mp
      simpa only [add_zero] using hid
    have hrest := ih htail
    intro i hi j hj hij
    simp only [Finset.mem_insert] at hi hj
    rcases hi with rfl | hi
    · have hj' : j ∈ s := hj.resolve_left (Ne.symm hij)
      exact measure_mono_null (inter_subset_inter_right _ (subset_biUnion_of_mem hj')) hdis
    · rcases hj with rfl | hj
      · rw [inter_comm]
        exact measure_mono_null (inter_subset_inter_right _ (subset_biUnion_of_mem hi)) hdis
      · exact hrest i hi j hj hij

theorem union_measure_eq_sum_iff [Fintype ι] (μ : Measure E)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, μ (A i) ≠ ⊤) :
    μ (⋃ i, A i) = ∑ i, μ (A i) ↔ Pairwise (AEDisjoint μ on A) := by
  classical
  constructor
  · intro he i j hij
    apply pairwise_null_of_union_measure_eq_sum μ A hA hfin Finset.univ
      (by simpa only [Finset.mem_univ, iUnion_true] using he) i (Finset.mem_univ i)
      j (Finset.mem_univ j) hij
  · intro hdis
    rw [measure_iUnion₀ hdis (fun i => (hA i).nullMeasurableSet),tsum_fintype]

section Translations

variable [AddGroup E] [MeasurableAdd E] [Fintype ι]

/-- Seeds admitting a particular strict target cell. -/
def sourcePiece (core : Set E) (v : ι → E) (C : ι → Set E) (i : ι) : Set E :=
  core ∩ (fun x => x+v i) ⁻¹' C i

/-- The actual translated piece in that cell. -/
def targetPiece (core : Set E) (v : ι → E) (C : ι → Set E) (i : ι) : Set E :=
  (fun x => x-v i) ⁻¹' core ∩ C i

/-- Exhaustive equality conditions for a finite translation certificate.
They require unique assignments almost everywhere and exhaustion of the
target almost everywhere. No area equality appears on the right side. -/
theorem measure_eq_iff (μ : Measure E) [μ.IsAddRightInvariant]
    (core : Set E) (hcore : MeasurableSet core) (v : ι → E)
    (C : ι → Set E) (hC : ∀ i, MeasurableSet (C i))
    (hdis : Pairwise (Disjoint on C)) (target : Set E) (hfin : μ target ≠ ⊤)
    (hassign : ∀ᵐ x ∂μ, x ∈ core → ∃ i, x+v i ∈ C i)
    (hinside : ∀ i x, x ∈ core → x+v i ∈ C i → x+v i ∈ target) :
    μ core = μ target ↔
      Pairwise (AEDisjoint μ on sourcePiece core v C) ∧
      (⋃ i, targetPiece core v C i) =ᵐ[μ] target := by
  classical
  let A := sourcePiece core v C
  let B := targetPiece core v C
  have hA (i) : MeasurableSet (A i) := hcore.inter ((hC i).preimage (measurable_add_const _))
  have hB (i) : MeasurableSet (B i) := by
    have hm : Measurable (fun x : E => x-v i) := by
      simpa only [sub_eq_add_neg] using measurable_add_const (-v i)
    exact (hcore.preimage hm).inter (hC i)
  have heAB (i) : μ (A i) = μ (B i) := by
    have hs : A i = (fun x => x+v i) ⁻¹' B i := by
      ext x
      simp only [A,B,sourcePiece,targetPiece,mem_inter_iff,mem_preimage,add_sub_cancel_right]
    rw [hs,measure_preimage_add_right]
  have hcover : (⋃ i, A i) =ᵐ[μ] core := by
    filter_upwards [hassign] with x hxassign
    apply propext
    change x ∈ (⋃ i, A i) ↔ x ∈ core
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact hi.1
    · intro hx
      obtain ⟨i,hi⟩ := hxassign hx
      exact mem_iUnion.mpr ⟨i,hx,hi⟩
  have hcorearea : μ (⋃ i, A i) = μ core := measure_congr hcover
  have hBdis : Pairwise (Disjoint on B) := fun i j hij =>
    (hdis hij).mono inter_subset_right inter_subset_right
  have hsub : (⋃ i, B i) ⊆ target := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    simpa only [sub_add_cancel] using hinside i (x-v i) hi.1 (by simpa using hi.2)
  have hAf (i) : μ (A i) ≠ ⊤ := by
    rw [heAB]
    exact ne_top_of_le_ne_top hfin (measure_mono ((subset_iUnion B i).trans hsub))
  have hsum : (∑ i, μ (A i)) = μ (⋃ i, B i) := by
    simp_rw [heAB]
    rw [measure_iUnion hBdis hB,tsum_fintype]
  have hlow : μ core ≤ ∑ i, μ (A i) := by
    rw [← hcorearea]
    exact measure_iUnion_fintype_le μ A
  constructor
  · intro he
    have heq : μ core = ∑ i, μ (A i) := by
      apply le_antisymm hlow
      rw [hsum,he]
      exact measure_mono hsub
    refine ⟨(union_measure_eq_sum_iff μ A hA hAf).mp (hcorearea.trans heq),?_⟩
    apply ae_eq_of_subset_of_measure_ge hsub _ (MeasurableSet.iUnion hB).nullMeasurableSet hfin
    rw [← hsum,← heq,he]
  · rintro ⟨hunique,hfull⟩
    calc
      μ core = μ (⋃ i, A i) := hcorearea.symm
      _ = ∑ i, μ (A i) := (union_measure_eq_sum_iff μ A hA hAf).mpr hunique
      _ = μ (⋃ i, B i) := hsum
      _ = μ target := measure_congr hfull

end Translations

/-- The equality criterion applies directly to weak exterior assignments
for closed bands. Null translated boundaries supply the strict assignments. -/
theorem closed_gap_measure_eq_iff [AddGroup E] [MeasurableAdd E] [Fintype ι]
    (μ : Measure E) [μ.IsAddRightInvariant]
    (f : ι → E → ℝ) (hf : ∀ i, Measurable (f i)) (lo hi : ι → ℝ)
    (ho : ∀ i, lo i ≤ hi i)
    (hlo : ∀ i, μ {x | f i x = lo i} = 0)
    (hhi : ∀ i, μ {x | f i x = hi i} = 0)
    (core : Set E) (hcore : MeasurableSet core) (v : Finset ι → E)
    (hassign : ∀ t ∈ core, ∃ s, t+v s ∈ Plank.LinearBands.weakCell f lo hi s)
    (K : Set E) (hKfin : μ K ≠ ⊤) (hinside : ∀ s t, t ∈ core → t+v s ∈ K) :
    μ core = μ (K \ ⋃ i, Plank.LinearBands.closedBand (f i) (lo i) (hi i)) ↔
      Pairwise (AEDisjoint μ on sourcePiece core v (Plank.LinearBands.strictCell f lo hi)) ∧
      (⋃ s, targetPiece core v (Plank.LinearBands.strictCell f lo hi) s) =ᵐ[μ]
        (K \ ⋃ i, Plank.LinearBands.closedBand (f i) (lo i) (hi i)) := by
  classical
  let bad : Set E := ⋃ s : Finset ι, ⋃ i : ι,
    {x | f i (x+v s) = lo i} ∪ {x | f i (x+v s) = hi i}
  have hbad : μ bad = 0 := by
    apply measure_iUnion_null
    intro s
    apply measure_iUnion_null
    intro i
    apply measure_union_null
    · change μ ((fun x => x+v s) ⁻¹' {x | f i x = lo i}) = 0
      rw [measure_preimage_add_right,hlo]
    · change μ ((fun x => x+v s) ⁻¹' {x | f i x = hi i}) = 0
      rw [measure_preimage_add_right,hhi]
  have hstrict : ∀ᵐ x ∂μ, x ∈ core →
      ∃ s, x+v s ∈ Plank.LinearBands.strictCell f lo hi s := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hbad] with x hx hc
    obtain ⟨s,hs⟩ := hassign x hc
    refine ⟨s,fun i => ?_⟩
    have hi' := hs i
    by_cases his : i ∈ s <;> simp only [his,↓reduceIte] at hi' ⊢
    · apply lt_of_le_of_ne hi'
      intro he
      exact hx (mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨i,Or.inr he.symm⟩⟩)
    · apply lt_of_le_of_ne hi'
      intro he
      exact hx (mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨i,Or.inl he⟩⟩)
  apply measure_eq_iff μ core hcore v (Plank.LinearBands.strictCell f lo hi)
    (Plank.LinearBands.measurableSet_strictCell f hf lo hi)
    (Plank.LinearBands.disjoint_strictCells f lo hi ho) _
    (ne_top_of_le_ne_top hKfin (measure_mono sdiff_subset)) hstrict
  intro s x hx hs
  exact ⟨hinside s x hx,Plank.LinearBands.strictCell_subset_gap f lo hi s hs⟩

end Quant.TranslationEquality

/-- info: 'Quant.TranslationEquality.measure_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TranslationEquality.measure_eq_iff
/-- info: 'Quant.TranslationEquality.closed_gap_measure_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TranslationEquality.closed_gap_measure_eq_iff
