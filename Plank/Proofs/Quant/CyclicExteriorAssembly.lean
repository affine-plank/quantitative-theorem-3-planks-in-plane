module
/-
# Exact assembly of the eight cyclic exterior cells

For arbitrary positive plank widths, the uncovered area is the sum of the six
raw pair areas, minus their threshold corrections, plus the all-low and all-high
cells. All sets use weak inequalities; affine boundary lines have zero area.
-/
public import Plank.Proofs.Quant.CyclicBadThresholds

@[expose] public section

noncomputable section

namespace Quant.CyclicExteriorAssembly

open Set MeasureTheory Function CyclicWeightedThresholdGeometry CyclicThresholdCaps

/-- The part of the triangle below two successive lower endpoints. -/
def rawLow (a b c : ℝ) (l : Fin 3 → ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ {x | value a b c i x ≤ l i ∧
    value a b c (i+1) x ≤ l (i+1)}

/-- The part of the triangle above two successive upper endpoints. -/
def rawHigh (a b c : ℝ) (h : Fin 3 → ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ {x | h i ≤ value a b c i x ∧
    h (i+1) ≤ value a b c (i+1) x}

/-- Lower endpoints on the chosen pair and the upper endpoint on its complement. -/
def lowerCorrectionLevels (l h : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if j = i+2 then h j else l j

/-- Upper endpoints on the chosen pair and the lower endpoint on its complement. -/
def upperCorrectionLevels (l h : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if j = i+2 then l j else h j

/-- The actual complement of the three closed bands in the standard triangle. -/
def uncovered (a b c : ℝ) (l h : Fin 3 → ℝ) : Set (ℝ × ℝ) :=
  stdTriangle.set \ ⋃ i, Plank.LinearBands.closedBand (value a b c i) (l i) (h i)

/-- A weak exterior sign cell, restricted to the triangle. -/
def exteriorCell (a b c : ℝ) (l h : Fin 3 → ℝ) (s : Finset (Fin 3)) :
    Set (ℝ × ℝ) :=
  stdTriangle.set ∩ Plank.LinearBands.weakCell (value a b c) l h s

theorem volume_value_level (a b c q : ℝ) (i : Fin 3) :
    volume {x : ℝ × ℝ | value a b c i x = q} = 0 := by
  fin_cases i
  · change volume {x | value a b c 0 x = q} = 0
    have he : {x | value a b c 0 x = q} = {x | dot (1-a,1) x = 1-q} := by
      ext x
      change (1-(1-a)*x.1-x.2 = q) ↔ (1-a)*x.1+1*x.2 = 1-q
      constructor <;> intro hx <;> linarith
    rw [he]
    exact CommonVertex.volume_line_zero
      (fun he => one_ne_zero (congrArg Prod.snd he)) (1-q)
  · simpa [value, dot] using CommonVertex.volume_line_zero
      (u := (1,b)) (fun he => one_ne_zero (congrArg Prod.fst he)) q
  · change volume {x | value a b c 2 x = q} = 0
    have he : {x | value a b c 2 x = q} = {x | dot (c,c-1) x = c-q} := by
      ext x
      change (c-c*x.1+(1-c)*x.2 = q) ↔ c*x.1+(c-1)*x.2 = c-q
      constructor <;> intro hx <;> nlinarith only [hx]
    rw [he]
    apply CommonVertex.volume_line_zero
    intro he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    dsimp at h₁ h₂
    linarith

theorem volume_ne_top_of_subset_triangle {A : Set (ℝ × ℝ)}
    (hA : A ⊆ stdTriangle.set) : volume A ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono hA)
  rw [Proofs.Quant.volume_stdTriangle]
  exact ENNReal.ofReal_ne_top

theorem measurableSet_exteriorCell (a b c : ℝ) (l h : Fin 3 → ℝ)
    (s : Finset (Fin 3)) : MeasurableSet (exteriorCell a b c l h s) :=
  Proofs.Quant.measurableSet_stdTriangle.inter
    (Plank.LinearBands.measurableSet_weakCell (value a b c)
      (fun i => (continuous_value a b c i).measurable) l h s)

theorem measurableSet_lowerCell (a b c : ℝ) (t : Fin 3 → ℝ) :
    MeasurableSet (lowerCell a b c t) := by
  apply Proofs.Quant.measurableSet_stdTriangle.inter
  rw [lowerRegion, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    measurableSet_le (continuous_value a b c i).measurable measurable_const)

theorem measurableSet_upperCell (a b c : ℝ) (t : Fin 3 → ℝ) :
    MeasurableSet (upperCell a b c t) := by
  apply Proofs.Quant.measurableSet_stdTriangle.inter
  rw [upperRegion, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i =>
    measurableSet_le measurable_const (continuous_value a b c i).measurable)

private theorem open_gap_eq_iUnion (a b c : ℝ) (l h : Fin 3 → ℝ) :
    stdTriangle.set \ ⋃ i, Plank.LinearBands.openBand (value a b c i) (l i) (h i) =
      ⋃ s, exteriorCell a b c l h s := by
  classical
  ext x
  simp only [mem_sdiff, mem_iUnion, Plank.LinearBands.openBand, mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hg⟩
    refine ⟨Finset.univ.filter (fun i => h i ≤ value a b c i x), hx, ?_⟩
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hi
    · exact hi
    · exact le_of_not_gt (fun hlo => hg ⟨i, hlo, lt_of_not_ge hi⟩)
  · rintro ⟨s, hx, hs⟩
    refine ⟨hx, ?_⟩
    rintro ⟨i, hli, hhi⟩
    have hi := hs i
    split_ifs at hi with his
    · exact (not_lt_of_ge hi) hhi
    · exact (not_lt_of_ge hi) hli

private theorem disjoint_exteriorCells (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hlh : ∀ i, l i < h i) : Pairwise (Disjoint on exteriorCell a b c l h) := by
  intro s t hst
  exact (Plank.LinearBands.disjoint_weakCells (value a b c) l h hlh hst).mono
    inter_subset_right inter_subset_right

theorem volume_uncovered_eq_sum (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hlh : ∀ i, l i < h i) :
    volume (uncovered a b c l h) = ∑ s, volume (exteriorCell a b c l h s) := by
  rw [uncovered, Plank.LinearBands.measure_closed_gap_eq_open_gap volume
    (value a b c) l h (fun i => volume_value_level a b c (l i) i)
    (fun i => volume_value_level a b c (h i) i), open_gap_eq_iUnion,
    measure_iUnion (disjoint_exteriorCells a b c l h hlh)
      (measurableSet_exteriorCell a b c l h), tsum_fintype]

private theorem rawLow_eq_union (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    rawLow a b c l i = exteriorCell a b c l h {i+2} ∪
      lowerCell a b c (lowerCorrectionLevels l h i) := by
  classical
  ext x
  have hs := le_total (value a b c (i+2) x) (h (i+2))
  fin_cases i <;>
    simp_all [rawLow, exteriorCell, Plank.LinearBands.weakCell, lowerCell,
      lowerRegion, lowerCorrectionLevels, Fin.forall_fin_succ] <;> tauto

private theorem rawHigh_eq_union (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    rawHigh a b c h i = exteriorCell a b c l h ({i+2} : Finset (Fin 3))ᶜ ∪
      upperCell a b c (upperCorrectionLevels l h i) := by
  classical
  ext x
  have hs := le_total (value a b c (i+2) x) (l (i+2))
  fin_cases i <;>
    simp_all [rawHigh, exteriorCell, Plank.LinearBands.weakCell, upperCell,
      upperRegion, upperCorrectionLevels, Fin.forall_fin_succ] <;> tauto

private theorem rawLow_union_aedisjoint (a b c : ℝ) (l h : Fin 3 → ℝ)
    (i : Fin 3) : AEDisjoint volume (exteriorCell a b c l h {i+2})
      (lowerCell a b c (lowerCorrectionLevels l h i)) := by
  change volume (_ ∩ _) = 0
  apply measure_mono_null _ (volume_value_level a b c (h (i+2)) (i+2))
  rintro x ⟨hx,hy⟩
  have hlo := hx.2 (i+2)
  have hhi := hy.2 (i+2)
  simp only [Finset.mem_singleton_self, ite_true] at hlo
  simp only [lowerCorrectionLevels, ite_true] at hhi
  exact le_antisymm hhi hlo

private theorem rawHigh_union_aedisjoint (a b c : ℝ) (l h : Fin 3 → ℝ)
    (i : Fin 3) : AEDisjoint volume
      (exteriorCell a b c l h ({i+2} : Finset (Fin 3))ᶜ)
      (upperCell a b c (upperCorrectionLevels l h i)) := by
  change volume (_ ∩ _) = 0
  apply measure_mono_null _ (volume_value_level a b c (l (i+2)) (i+2))
  rintro x ⟨hx,hy⟩
  have hlo := hy.2 (i+2)
  have hhi := hx.2 (i+2)
  simp only [Finset.mem_compl, Finset.mem_singleton_self, not_true_eq_false,
    ite_false] at hhi
  simp only [upperCorrectionLevels, ite_true] at hlo
  exact le_antisymm hhi hlo

theorem rawLow_area_eq (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    (volume (rawLow a b c l i)).toReal =
      (volume (exteriorCell a b c l h {i+2})).toReal +
      (volume (lowerCell a b c (lowerCorrectionLevels l h i))).toReal := by
  rw [rawLow_eq_union, measure_union₀ (measurableSet_lowerCell a b c _).nullMeasurableSet
    (rawLow_union_aedisjoint a b c l h i)]
  exact ENNReal.toReal_add
    (volume_ne_top_of_subset_triangle inter_subset_left)
    (volume_ne_top_of_subset_triangle inter_subset_left)

theorem rawHigh_area_eq (a b c : ℝ) (l h : Fin 3 → ℝ) (i : Fin 3) :
    (volume (rawHigh a b c h i)).toReal =
      (volume (exteriorCell a b c l h ({i+2} : Finset (Fin 3))ᶜ)).toReal +
      (volume (upperCell a b c (upperCorrectionLevels l h i))).toReal := by
  rw [rawHigh_eq_union, measure_union₀ (measurableSet_upperCell a b c _).nullMeasurableSet
    (rawHigh_union_aedisjoint a b c l h i)]
  exact ENNReal.toReal_add
    (volume_ne_top_of_subset_triangle inter_subset_left)
    (volume_ne_top_of_subset_triangle inter_subset_left)

@[simp] theorem exteriorCell_empty (a b c : ℝ) (l h : Fin 3 → ℝ) :
    exteriorCell a b c l h ∅ = lowerCell a b c l := by
  ext x
  simp [exteriorCell, Plank.LinearBands.weakCell, lowerCell, lowerRegion]

@[simp] theorem exteriorCell_univ (a b c : ℝ) (l h : Fin 3 → ℝ) :
    exteriorCell a b c l h Finset.univ = upperCell a b c h := by
  ext x
  simp [exteriorCell, Plank.LinearBands.weakCell, upperCell, upperRegion]

private theorem sum_eight (g : Finset (Fin 3) → ℝ) :
    ∑ s, g s = (∑ i : Fin 3, g {i+2}) +
      (∑ i : Fin 3, g ({i+2} : Finset (Fin 3))ᶜ) + g ∅ + g Finset.univ := by
  have hu : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0,1}, {0,2}, {1,2}, Finset.univ} := by decide
  have hc0 : ({0} : Finset (Fin 3))ᶜ = {1,2} := by decide
  have hc1 : ({1} : Finset (Fin 3))ᶜ = {0,2} := by decide
  have hc2 : ({2} : Finset (Fin 3))ᶜ = {0,1} := by decide
  simp [hu, Fin.sum_univ_three, hc0, hc1, hc2, Finset.ext_iff, Fin.forall_fin_succ]
  ring

/-- The exact eight-exterior-cell identity. It makes no assumption on the
directions, the positions of the bands, or any symmetry between them. -/
theorem uncovered_area_eq (a b c : ℝ) (l h : Fin 3 → ℝ)
    (hlh : ∀ i, l i < h i) :
    (volume (uncovered a b c l h)).toReal =
      (∑ i, (volume (rawLow a b c l i)).toReal) +
      (∑ i, (volume (rawHigh a b c h i)).toReal) -
      (∑ i, (volume (lowerCell a b c (lowerCorrectionLevels l h i))).toReal) -
      (∑ i, (volume (upperCell a b c (upperCorrectionLevels l h i))).toReal) +
      (volume (lowerCell a b c l)).toReal +
      (volume (upperCell a b c h)).toReal := by
  have hlo : (∑ i, (volume (rawLow a b c l i)).toReal) =
      (∑ i : Fin 3, (volume (exteriorCell a b c l h {i+2})).toReal) +
      ∑ i, (volume (lowerCell a b c (lowerCorrectionLevels l h i))).toReal := by
    simp_rw [rawLow_area_eq a b c l h]
    exact Finset.sum_add_distrib
  have hhi : (∑ i, (volume (rawHigh a b c h i)).toReal) =
      (∑ i : Fin 3, (volume (exteriorCell a b c l h ({i+2} : Finset (Fin 3))ᶜ)).toReal) +
      ∑ i, (volume (upperCell a b c (upperCorrectionLevels l h i))).toReal := by
    simp_rw [rawHigh_area_eq a b c l h]
    exact Finset.sum_add_distrib
  rw [volume_uncovered_eq_sum a b c l h hlh,
    ENNReal.toReal_sum (fun i _ => volume_ne_top_of_subset_triangle
      (show exteriorCell a b c l h i ⊆ stdTriangle.set from inter_subset_left)),
    sum_eight, exteriorCell_empty, exteriorCell_univ, hlo, hhi]
  ring

/-- The endpoint conversion from the ABC chart preserves strict widths. -/
theorem lowerLevels_lt_upperLevels (C : Config) (c : ℝ)
    (hwidth : ∀ i, (C.plank i).lo < (C.plank i).hi) :
    ∀ i, CyclicBadThresholds.lowerLevels C c i < CyclicBadThresholds.upperLevels C c i := by
  intro i
  fin_cases i <;> dsimp [CyclicBadThresholds.lowerLevels, CyclicBadThresholds.upperLevels] <;>
    linarith [hwidth 0, hwidth 1, hwidth 2]

/-- The three cyclic bands are exactly the three original ABC planks. -/
theorem configuration_uncovered (C : Config) {a b c : ℝ}
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) :
    C.uncovered = uncovered (1-a) b c
      (CyclicBadThresholds.lowerLevels C c) (CyclicBadThresholds.upperLevels C c) := by
  have hcovered (x : ℝ × ℝ) :
      (∃ i, x ∈ (C.plank i).set) ↔
        ∃ i, CyclicBadThresholds.lowerLevels C c i ≤ value (1-a) b c i x ∧
          value (1-a) b c i x ≤ CyclicBadThresholds.upperLevels C c i := by
    constructor
    · rintro ⟨i, hi⟩
      change (C.plank i).lo ≤ dot (C.plank i).u x ∧
        dot (C.plank i).u x ≤ (C.plank i).hi at hi
      fin_cases i
      · refine ⟨1, ?_⟩
        change (C.plank 0).lo ≤ dot (C.plank 0).u x ∧
          dot (C.plank 0).u x ≤ (C.plank 0).hi at hi
        rw [hu₀] at hi
        dsimp [value, CyclicBadThresholds.lowerLevels, CyclicBadThresholds.upperLevels, dot] at *
        constructor <;> linarith [hi.1,hi.2]
      · refine ⟨0, ?_⟩
        change (C.plank 1).lo ≤ dot (C.plank 1).u x ∧
          dot (C.plank 1).u x ≤ (C.plank 1).hi at hi
        rw [hu₁] at hi
        dsimp [value, CyclicBadThresholds.lowerLevels, CyclicBadThresholds.upperLevels, dot] at *
        constructor <;> linarith [hi.1,hi.2]
      · refine ⟨2, ?_⟩
        change (C.plank 2).lo ≤ dot (C.plank 2).u x ∧
          dot (C.plank 2).u x ≤ (C.plank 2).hi at hi
        rw [hu₂] at hi
        dsimp [value, CyclicBadThresholds.lowerLevels, CyclicBadThresholds.upperLevels, dot] at *
        constructor <;> nlinarith only [hi.1,hi.2]
    · rintro ⟨i, hi⟩
      fin_cases i
      · refine ⟨1, ?_⟩
        change (C.plank 1).lo ≤ dot (C.plank 1).u x ∧
          dot (C.plank 1).u x ≤ (C.plank 1).hi
        rw [hu₁]
        dsimp [value, CyclicBadThresholds.lowerLevels, CyclicBadThresholds.upperLevels, dot] at *
        constructor <;> linarith [hi.1,hi.2]
      · refine ⟨0, ?_⟩
        change (C.plank 0).lo ≤ dot (C.plank 0).u x ∧
          dot (C.plank 0).u x ≤ (C.plank 0).hi
        rw [hu₀]
        dsimp [value, CyclicBadThresholds.lowerLevels, CyclicBadThresholds.upperLevels, dot] at *
        constructor <;> linarith [hi.1,hi.2]
      · refine ⟨2, ?_⟩
        change (C.plank 2).lo ≤ dot (C.plank 2).u x ∧
          dot (C.plank 2).u x ≤ (C.plank 2).hi
        rw [hu₂]
        dsimp [value, CyclicBadThresholds.lowerLevels, CyclicBadThresholds.upperLevels, dot] at *
        constructor <;> nlinarith only [hi.1,hi.2]
  ext x
  simp only [Config.uncovered, uncovered, mem_sdiff, mem_iUnion,
    Plank.LinearBands.closedBand, mem_ofPred_eq, hcovered]

/-- The exact identity in the original configuration's gap-area currency. -/
theorem gapArea_eq (C : Config) {a b c : ℝ}
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1))
    (hwidth : ∀ i, (C.plank i).lo < (C.plank i).hi) :
    let l := CyclicBadThresholds.lowerLevels C c
    let h := CyclicBadThresholds.upperLevels C c
    C.gapArea =
      (∑ i, (volume (rawLow (1-a) b c l i)).toReal) +
      (∑ i, (volume (rawHigh (1-a) b c h i)).toReal) -
      (∑ i, (volume (lowerCell (1-a) b c (lowerCorrectionLevels l h i))).toReal) -
      (∑ i, (volume (upperCell (1-a) b c (upperCorrectionLevels l h i))).toReal) +
      (volume (lowerCell (1-a) b c l)).toReal +
      (volume (upperCell (1-a) b c h)).toReal := by
  dsimp only
  rw [Config.gapArea, configuration_uncovered C hu₀ hu₁ hu₂]
  exact uncovered_area_eq (1-a) b c _ _ (lowerLevels_lt_upperLevels C c hwidth)

end Quant.CyclicExteriorAssembly
