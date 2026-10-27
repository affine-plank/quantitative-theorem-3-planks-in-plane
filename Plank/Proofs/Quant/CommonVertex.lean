module
/-
# Translations for planks sharing an extreme vertex

Nonnegative interactions between escape steps give a maximal feasible subset.
Its translated point lies on the designated side of every plank. Distinct side
assignments give disjoint translated pieces, which preserve the area budget.
-/
public import Plank.Proofs.Quant.RowDeletion
import Plank.Algebra.MonotoneSubset

@[expose] public section

noncomputable section

namespace Quant.CommonVertex

open Set MeasureTheory Function

variable {ι : Type*}

def shift (v : ι → ℝ × ℝ) (s : Finset ι) : ℝ × ℝ := s.sum v

/-- The finite maximization needs no metric or symmetry of the interactions. -/
theorem exists_side_assignment [Fintype ι] (p : ι → Plank) (v : ι → ℝ × ℝ)
    (hself : ∀ i, dot (p i).u (v i) = (p i).hi - (p i).lo)
    (hcross : ∀ i j, 0 ≤ dot (p i).u (v j)) (t : ℝ × ℝ) :
    ∃ s : Finset ι,
      (∀ i ∈ s, (p i).hi < dot (p i).u (t + shift v s)) ∧
      (∀ i ∉ s, dot (p i).u (t + shift v s) ≤ (p i).lo) := by
  classical
  let D (i : ι) : (ℝ × ℝ) →+ ℝ :=
    { toFun := dot (p i).u
      map_zero' := Proofs.Basic.dot_zero_right (p i).u
      map_add' := Proofs.Basic.dot_add_right (p i).u }
  have hdot (s : Finset ι) (i : ι) : dot (p i).u (t + shift v s) =
      dot (p i).u t + ∑ j ∈ s, dot (p i).u (v j) := by
    rw [Proofs.Basic.dot_add_right]
    exact congrArg (fun z : ℝ => dot (p i).u t + z) (map_sum (D i) v s)
  obtain ⟨s, hhigh, hlow⟩ := Plank.MonotoneSubset.exists_side_assignment
    (fun i => dot (p i).u t) (fun j i => dot (p i).u (v j))
    (fun j i => hcross i j) (fun i => (p i).lo) (fun i => (p i).hi)
    (fun i => (hself i).ge)
  refine ⟨s, ?_, ?_⟩
  · simpa only [hdot] using hhigh
  · simpa only [hdot] using hlow

/-- Fubini makes every nonconstant affine level set null. -/
theorem volume_line_zero {u : ℝ × ℝ} (hu : u ≠ 0) (c : ℝ) :
    volume {x : ℝ × ℝ | dot u x = c} = 0 := by
  have hm : MeasurableSet {x : ℝ × ℝ | dot u x = c} :=
    measurableSet_eq_fun (Proofs.GapCells.continuous_dot u).measurable measurable_const
  by_cases h₂ : u.2 = 0
  · have h₁ : u.1 ≠ 0 := by
      intro h₁
      exact hu (Prod.ext h₁ h₂)
    rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm]
    have hrow : ∀ y : ℝ, {x : ℝ | dot u (x, y) = c} = {c / u.1} := by
      intro y
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff, dot, h₂, zero_mul, add_zero]
      rw [eq_div_iff h₁, mul_comm]
    change (∫⁻ y : ℝ, volume {x : ℝ | dot u (x, y) = c}) = 0
    simp only [hrow, Real.volume_singleton, lintegral_zero]
  · rw [Measure.volume_eq_prod, Measure.prod_apply hm]
    have hrow : ∀ x : ℝ,
        Prod.mk x ⁻¹' {p : ℝ × ℝ | dot u p = c} = {(c - u.1 * x) / u.2} := by
      intro x
      ext y
      simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff, dot]
      rw [eq_div_iff h₂]
      constructor <;> intro h <;> linarith
    simp only [hrow, Real.volume_singleton, lintegral_zero]

def cell (p : ι → Plank) (s : Finset ι) : Set (ℝ × ℝ) := by
  classical
  exact {x | ∀ i, if i ∈ s then (p i).hi < dot (p i).u x else dot (p i).u x < (p i).lo}

theorem measurableSet_cell [Fintype ι] (p : ι → Plank) (s : Finset ι) :
    MeasurableSet (cell p s) := by
  classical
  rw [cell, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ s
  · simpa [hi] using (Proofs.GapCells.isOpen_lt_dot (p i).u (p i).hi).measurableSet
  · simpa [hi] using (Proofs.GapCells.isOpen_dot_lt (p i).u (p i).lo).measurableSet

theorem disjoint_cells (p : ι → Plank) : Pairwise (Disjoint on cell p) := by
  classical
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  have he : s = t := by
    ext i
    have hsi := hs i
    have hti := ht i
    by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
      simp only [his, hit, ↓reduceIte] at hsi hti ⊢
    · linarith [(p i).lo_le_hi]
    · linarith [(p i).lo_le_hi]
  exact hst he

theorem shift_fst (v : ι → ℝ × ℝ) (s : Finset ι) :
    (shift v s).1 = s.sum (fun i => (v i).1) :=
  map_sum (AddMonoidHom.fst ℝ ℝ) v s

theorem shift_snd (v : ι → ℝ × ℝ) (s : Finset ι) :
    (shift v s).2 = s.sum (fun i => (v i).2) :=
  map_sum (AddMonoidHom.snd ℝ ℝ) v s

theorem shifted_mem_triangle [Fintype ι] (v : ι → ℝ × ℝ)
    (hv : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2) (s : Finset ι)
    {t : ℝ × ℝ}
    (ht : t ∈ RowDeletion.triangle (1 - ∑ i, ((v i).1 + (v i).2))) :
    t + shift v s ∈ stdTriangle.set := by
  classical
  have hx : 0 ≤ (shift v s).1 := by
    rw [shift_fst]
    exact Finset.sum_nonneg fun i _ => (hv i).1
  have hy : 0 ≤ (shift v s).2 := by
    rw [shift_snd]
    exact Finset.sum_nonneg fun i _ => (hv i).2
  have hsum : (shift v s).1 + (shift v s).2 ≤ ∑ i, ((v i).1 + (v i).2) := by
    rw [shift_fst, shift_snd, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun i _ _ => add_nonneg (hv i).1 (hv i).2)
  rw [Proofs.Quant.stdTriangle_set_eq]
  change 0 ≤ t.1 + (shift v s).1 ∧ 0 ≤ t.2 + (shift v s).2 ∧
    t.1 + (shift v s).1 + (t.2 + (shift v s).2) ≤ 1
  exact ⟨add_nonneg ht.1 hx, add_nonneg ht.2.1 hy, by linarith [ht.2.2]⟩

/-- The area budget for a finite family of mutually nonnegative escape steps.
Planks are closed and their widths may vanish. -/
theorem area_of_monotone_steps [Fintype ι] (p : ι → Plank) (v : ι → ℝ × ℝ)
    (hself : ∀ i, dot (p i).u (v i) = (p i).hi - (p i).lo)
    (hcross : ∀ i j, 0 ≤ dot (p i).u (v j))
    (hv : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2) :
    ENNReal.ofReal ((max 0 (1 - ∑ i, ((v i).1 + (v i).2))) ^ 2 / 2) ≤
      volume (stdTriangle.set \ ⋃ i, (p i).set) := by
  classical
  by_cases hδ : 0 < 1 - ∑ i, ((v i).1 + (v i).2)
  · rw [max_eq_right hδ.le]
    let core := RowDeletion.triangle (1 - ∑ i, ((v i).1 + (v i).2))
    let bad : Set (ℝ × ℝ) := ⋃ s : Finset ι, ⋃ i : ι,
      {x | dot (p i).u (x + shift v s) = (p i).lo}
    have hbad : volume bad = 0 := by
      apply measure_iUnion_null
      intro s
      apply measure_iUnion_null
      intro i
      change volume ((fun x => x + shift v s) ⁻¹'
        {x : ℝ × ℝ | dot (p i).u x = (p i).lo}) = 0
      rw [measure_preimage_add_right]
      exact volume_line_zero (p i).u_ne_zero (p i).lo
    let B : Finset ι → Set (ℝ × ℝ) := fun s =>
      (fun x => x - shift v s) ⁻¹' core ∩ cell p s
    let A : Finset ι → Set (ℝ × ℝ) := fun s =>
      (fun x => x + shift v s) ⁻¹' B s
    have hB : ∀ s, MeasurableSet (B s) := by
      intro s
      exact ((RowDeletion.measurableSet_triangle _).preimage
        (by fun_prop)).inter (measurableSet_cell p s)
    have hdis : Pairwise (Disjoint on B) := by
      intro s t hst
      exact (disjoint_cells p hst).mono inter_subset_right inter_subset_right
    have hcover : core \ bad ⊆ ⋃ s, A s := by
      intro x hx
      obtain ⟨s, hhigh, hlow⟩ := exists_side_assignment p v hself hcross x
      apply mem_iUnion.mpr
      refine ⟨s, ?_⟩
      change (x + shift v s - shift v s ∈ core) ∧ x + shift v s ∈ cell p s
      refine ⟨by simpa using hx.1, ?_⟩
      intro i
      by_cases hi : i ∈ s
      · simpa only [hi, ↓reduceIte] using hhigh i hi
      · simp only [hi, ↓reduceIte]
        rcases lt_or_eq_of_le (hlow i hi) with h | h
        · exact h
        · exact (hx.2 (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨i, h⟩⟩)).elim
    have hinside : (⋃ s, B s) ⊆ stdTriangle.set \ ⋃ i, (p i).set := by
      intro x hx
      obtain ⟨s, hs⟩ := mem_iUnion.mp hx
      have hxT := shifted_mem_triangle v hv s hs.1
      refine ⟨by simpa using hxT, ?_⟩
      intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      change (p i).lo ≤ dot (p i).u x ∧ dot (p i).u x ≤ (p i).hi at hi
      have hc := hs.2 i
      by_cases his : i ∈ s <;> simp only [his, ↓reduceIte] at hc
      · exact (not_lt_of_ge hi.2) hc
      · exact (not_lt_of_ge hi.1) hc
    calc
      ENNReal.ofReal ((1 - ∑ i, ((v i).1 + (v i).2)) ^ 2 / 2) = volume core :=
        (RowDeletion.volume_triangle hδ).symm
      _ = volume (core \ bad) := (measure_sdiff_null hbad).symm
      _ ≤ volume (⋃ s, A s) := measure_mono hcover
      _ ≤ ∑ s, volume (A s) := measure_iUnion_fintype_le volume A
      _ = ∑ s, volume (B s) := by
        apply Finset.sum_congr rfl
        intro s _
        exact measure_preimage_add_right volume (shift v s) (B s)
      _ = volume (⋃ s, B s) := by rw [measure_iUnion hdis hB, tsum_fintype]
      _ ≤ volume (stdTriangle.set \ ⋃ i, (p i).set) := measure_mono hinside
  · rw [max_eq_left (le_of_not_gt hδ)]
    simp

/-- Planks with nonnegative normal coordinates share the origin as a minimum
vertex. No normal normalization or positivity of the plank widths is assumed. -/
theorem finite_nonnegative_normals [Fintype ι] (p : ι → Plank)
    (hu : ∀ i, 0 ≤ (p i).u.1 ∧ 0 ≤ (p i).u.2) :
    ENNReal.ofReal ((max 0 (1 - ∑ i, (p i).relWidth stdTriangle)) ^ 2 / 2) ≤
      volume (stdTriangle.set \ ⋃ i, (p i).set) := by
  classical
  have hwidth : ∀ i, stdTriangle.width (p i).u = max (p i).u.1 (p i).u.2 := by
    intro i
    rw [Proofs.Transport.stdTriangle_width_eq,
      max_eq_right ((hu i).1.trans (le_max_left _ _)),
      min_eq_left (le_min (hu i).1 (hu i).2), sub_zero]
  have hpos : ∀ i, 0 < max (p i).u.1 (p i).u.2 := by
    intro i
    by_contra h
    have hm := le_of_not_gt h
    have h₁ : (p i).u.1 = 0 :=
      le_antisymm ((le_max_left _ _).trans hm) (hu i).1
    have h₂ : (p i).u.2 = 0 :=
      le_antisymm ((le_max_right _ _).trans hm) (hu i).2
    exact (p i).u_ne_zero (Prod.ext h₁ h₂)
  have hr : ∀ i, 0 ≤ (p i).relWidth stdTriangle := by
    intro i
    rw [Plank.relWidth, hwidth]
    exact div_nonneg (sub_nonneg.mpr (p i).lo_le_hi) (hpos i).le
  let v : ι → ℝ × ℝ := fun i =>
    if (p i).u.1 ≤ (p i).u.2 then (0, (p i).relWidth stdTriangle)
    else ((p i).relWidth stdTriangle, 0)
  have hv : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2 := by
    intro i
    dsimp [v]
    split_ifs <;> simpa using hr i
  have hcost : ∀ i, (v i).1 + (v i).2 = (p i).relWidth stdTriangle := by
    intro i
    dsimp [v]
    split_ifs <;> simp
  have hself : ∀ i, dot (p i).u (v i) = (p i).hi - (p i).lo := by
    intro i
    by_cases h : (p i).u.1 ≤ (p i).u.2
    · have hne : (p i).u.2 ≠ 0 := ne_of_gt (by simpa [max_eq_right h] using hpos i)
      simp only [v, if_pos h, dot, mul_zero, zero_add, Plank.relWidth,
        hwidth, max_eq_right h]
      field_simp
    · have hne : (p i).u.1 ≠ 0 :=
        ne_of_gt (by simpa [max_eq_left (le_of_not_ge h)] using hpos i)
      simp only [v, if_neg h, dot, mul_zero, add_zero, Plank.relWidth,
        hwidth, max_eq_left (le_of_not_ge h)]
      field_simp
  have hcross : ∀ i j, 0 ≤ dot (p i).u (v j) := by
    intro i j
    exact add_nonneg (mul_nonneg (hu i).1 (hv j).1) (mul_nonneg (hu i).2 (hv j).2)
  simpa only [hcost] using area_of_monotone_steps p v hself hcross hv

theorem config_positive_square_bound (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  have h := finite_nonnegative_normals C.plank hu
  have hfin : volume C.uncovered ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
      (measure_mono Set.sdiff_subset)
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h

theorem config_sqBound (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hs : C.sumRelW ≤ 1) : C.SqBound := by
  have h := config_positive_square_bound C hu
  have hd : 0 ≤ C.deficit := by unfold Config.deficit; linarith
  rw [max_eq_right hd] at h
  change C.deficit ^ 2 * (1 / 2) ≤ C.gapArea
  linarith

def reverse (p : Plank) : Plank :=
  ⟨-p.u, -p.hi, -p.lo, neg_ne_zero.mpr p.u_ne_zero, neg_le_neg p.lo_le_hi⟩

theorem reverse_set (p : Plank) : (reverse p).set = p.set := by
  ext x
  change (-p.hi ≤ dot (-p.u) x ∧ dot (-p.u) x ≤ -p.lo) ↔
    p.lo ≤ dot p.u x ∧ dot p.u x ≤ p.hi
  rw [Proofs.Basic.dot_neg_left]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem reverse_relWidth (p : Plank) :
    (reverse p).relWidth stdTriangle = p.relWidth stdTriangle := by
  simp only [Plank.relWidth, reverse, Proofs.Transport.width_neg]
  congr 1
  ring

def Coherent (u : ℝ × ℝ) : Prop :=
  (0 ≤ u.1 ∧ 0 ≤ u.2) ∨ (u.1 ≤ 0 ∧ u.2 ≤ 0)

theorem finite_coherent_normals [Fintype ι] (p : ι → Plank)
    (hu : ∀ i, Coherent (p i).u) :
    ENNReal.ofReal ((max 0 (1 - ∑ i, (p i).relWidth stdTriangle)) ^ 2 / 2) ≤
      volume (stdTriangle.set \ ⋃ i, (p i).set) := by
  classical
  let q : ι → Plank := fun i =>
    if 0 ≤ (p i).u.1 ∧ 0 ≤ (p i).u.2 then p i else reverse (p i)
  have hq : ∀ i, 0 ≤ (q i).u.1 ∧ 0 ≤ (q i).u.2 := by
    intro i
    by_cases h : 0 ≤ (p i).u.1 ∧ 0 ≤ (p i).u.2
    · simp [q, h]
    · have hn := (hu i).resolve_left h
      simpa [q, h, reverse] using hn
  have hset : ∀ i, (q i).set = (p i).set := by
    intro i
    dsimp [q]
    split_ifs
    · rfl
    · exact reverse_set _
  have hr : ∀ i, (q i).relWidth stdTriangle = (p i).relWidth stdTriangle := by
    intro i
    dsimp [q]
    split_ifs
    · rfl
    · exact reverse_relWidth _
  simpa only [hset, hr] using finite_nonnegative_normals q hq

theorem config_coherent_positive_square_bound (C : Config)
    (hu : ∀ i, Coherent (C.plank i).u) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  have h := finite_coherent_normals C.plank hu
  have hfin : volume C.uncovered ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
      (measure_mono Set.sdiff_subset)
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h

theorem config_coherent_sqBound (C : Config)
    (hu : ∀ i, Coherent (C.plank i).u)
    (hs : C.sumRelW ≤ 1) : C.SqBound := by
  have h := config_coherent_positive_square_bound C hu
  have hd : 0 ≤ C.deficit := by unfold Config.deficit; linarith
  rw [max_eq_right hd] at h
  change C.deficit ^ 2 * (1 / 2) ≤ C.gapArea
  linarith

end Quant.CommonVertex
