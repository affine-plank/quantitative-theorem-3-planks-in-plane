module
/-
# Localizing the remaining area loss to the cyclic obstruction

Outside two explicit open threshold boxes, the standard eight translations
give the area bound. For arbitrary positions they bound the possible loss
by the area of the obstructed part of the deficit triangle.
-/
public import Plank.Proofs.Quant.CyclicAssignment
public import Plank.Proofs.Quant.OrdinalArea

@[expose] public section

noncomputable section

namespace Quant.CyclicArea

open Set MeasureTheory CommonVertex OrdinalArea

def base (C : Config) : ℝ × ℝ := (0, widths C 2)

def threshold (C : Config) (z : ℝ × ℝ) (i : Fin 3) : ℝ :=
  (C.plank i).lo - dot (C.plank i).u (z + base C)

def badSeeds (C : Config) (b a c : ℝ) : Set (ℝ × ℝ) :=
  {z | CyclicAssignment.Bad
    (b * widths C 1) ((1 - b) * widths C 2)
    (a * widths C 0) ((1 - a) * widths C 2)
    (c * widths C 0) ((1 - c) * widths C 1)
    (threshold C z 0) (threshold C z 1) (threshold C z 2)}

theorem measurableSet_badSeeds (C : Config) (b a c : ℝ) :
    MeasurableSet (badSeeds C b a c) := by
  have hm : ∀ i, Measurable (fun z : ℝ × ℝ => threshold C z i) := by
    intro i
    dsimp [threshold, dot]
    fun_prop
  unfold badSeeds CyclicAssignment.Bad
  exact (((measurableSet_lt measurable_const (hm 0)).inter
    (measurableSet_lt (hm 0) measurable_const)).inter
    (((measurableSet_lt measurable_const (hm 1)).inter
      (measurableSet_lt (hm 1) measurable_const)).inter
    ((measurableSet_lt measurable_const (hm 2)).inter
      (measurableSet_lt (hm 2) measurable_const)))).union
    (((measurableSet_lt measurable_const (hm 0)).inter
      (measurableSet_lt (hm 0) measurable_const)).inter
    (((measurableSet_lt measurable_const (hm 1)).inter
      (measurableSet_lt (hm 1) measurable_const)).inter
    ((measurableSet_lt measurable_const (hm 2)).inter
      (measurableSet_lt (hm 2) measurable_const))))

theorem deficit_eq (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) :
    C.deficit = 1 - (widths C 0 + widths C 1 + widths C 2) := by
  have hrel : ∀ i, C.relW i = widths C i := by
    intro i
    rw [Config.relW, Plank.relWidth, BalancedArea.abc_width_one C hb ha hc hu₀ hu₁ hu₂,
      div_one]
    rfl
  simp only [Config.deficit, Config.sumRelW, hrel, Fin.sum_univ_three]

/-- All unobstructed seed points contribute their area to the actual gap. -/
theorem volume_good_core_le_gap (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) :
    volume (RowDeletion.triangle C.deficit \ badSeeds C b a c) ≤ volume C.uncovered := by
  classical
  let r := widths C
  have hr : ∀ i, 0 ≤ r i := fun i => sub_nonneg.mpr (C.plank i).lo_le_hi
  have hu : ∀ i, (C.plank i).u = ![(1, b), (a, 1), (c, c - 1)] i := by
    intro i
    fin_cases i
    · exact hu₀
    · exact hu₁
    · exact hu₂
  have hself : ∀ i, dot (C.plank i).u (steps r i) = (C.plank i).hi - (C.plank i).lo := by
    intro i
    rw [hu]
    change dot (![(1, b), (a, 1), (c, c - 1)] i) (steps r i) = r i
    fin_cases i <;> dsimp [steps, dot] <;> ring
  have hmatrix : ∀ i j, OrdinalTranslations.interaction C.plank (steps r) i j =
      OrdinalMatrix.matrix (b * r 1) ((1 - b) * r 2)
        (a * r 0) ((1 - a) * r 2) (c * r 0) ((1 - c) * r 1) i j := by
    intro i j
    simp only [OrdinalTranslations.interaction, hu]
    fin_cases i <;> fin_cases j <;> norm_num [steps, OrdinalMatrix.matrix, dot] <;> ring
  apply SymmetricTranslations.volume_le_gap_of_translations C.plank
    (RowDeletion.triangle C.deficit \ badSeeds C b a c)
    ((RowDeletion.measurableSet_triangle _).diff (measurableSet_badSeeds C b a c))
    (fun S => base C + shift (steps r) S)
  · intro z hz
    have hpat := (CyclicAssignment.pattern_iff_not_bad
      (mul_nonneg hb.1.le (hr 1)) (mul_nonneg (sub_nonneg.mpr hb.2.le) (hr 2))
      (mul_nonneg ha.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr ha.2.le) (hr 2))
      (mul_nonneg hc.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr hc.2.le) (hr 1))).mpr hz.2
    simpa only [add_assoc] using CyclicAssignment.exists_side_assignment
      C.plank (steps r) hself _ _ _ _ _ _ hmatrix (z + base C) hpat
  · intro S z hz
    apply translated_mem_triangle r hr S z
    simpa only [deficit_eq C hb ha hc hu₀ hu₁ hu₂, r] using hz.1

/-- If the obstruction misses the deficit triangle, the full bound holds. -/
theorem positive_part_of_no_bad_seed (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hbad : ∀ z ∈ RowDeletion.triangle C.deficit, z ∉ badSeeds C b a c) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  by_cases hδ : 0 < C.deficit
  · have he : RowDeletion.triangle C.deficit \ badSeeds C b a c =
        RowDeletion.triangle C.deficit := by
      ext z
      exact ⟨fun h => h.1, fun h => ⟨h, hbad z h⟩⟩
    have hvol := volume_good_core_le_gap C hb ha hc hu₀ hu₁ hu₂
    rw [he, RowDeletion.volume_triangle hδ] at hvol
    have hfin : volume C.uncovered ≠ ⊤ := by
      apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
        (measure_mono Set.sdiff_subset)
      rw [Proofs.Quant.volume_stdTriangle]
      exact ENNReal.ofReal_ne_top
    rw [max_eq_right hδ.le]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hvol
  · rw [max_eq_left (le_of_not_gt hδ)]
    simp [Config.gapArea]

theorem sqPos_of_no_bad_seed (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hbad : ∀ z ∈ RowDeletion.triangle C.deficit, z ∉ badSeeds C b a c) :
    Quant.SqPos C := by
  have h := positive_part_of_no_bad_seed C hb ha hc hu₀ hu₁ hu₂ hbad
  change (max 0 C.deficit) ^ 2 * (1 / 2) ≤ C.gapArea
  linarith

/-- A quantitative bound for every position, with the obstruction area explicit. -/
theorem positive_part_with_bad_area (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea +
      (volume (RowDeletion.triangle C.deficit ∩ badSeeds C b a c)).toReal := by
  by_cases hδ : 0 < C.deficit
  · have hsub : RowDeletion.triangle C.deficit ⊆
        (RowDeletion.triangle C.deficit \ badSeeds C b a c) ∪
          (RowDeletion.triangle C.deficit ∩ badSeeds C b a c) := by
      intro z hz
      by_cases hzbad : z ∈ badSeeds C b a c
      · exact Or.inr ⟨hz, hzbad⟩
      · exact Or.inl ⟨hz, hzbad⟩
    have hvol := (measure_mono (μ := volume) hsub).trans
      ((measure_union_le _ _).trans
        (add_le_add (volume_good_core_le_gap C hb ha hc hu₀ hu₁ hu₂) le_rfl))
    have hgap : volume C.uncovered ≠ ⊤ := by
      apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
        (measure_mono Set.sdiff_subset)
      rw [Proofs.Quant.volume_stdTriangle]
      exact ENNReal.ofReal_ne_top
    have hbad : volume (RowDeletion.triangle C.deficit ∩ badSeeds C b a c) ≠ ⊤ := by
      apply ne_top_of_le_ne_top (show volume (RowDeletion.triangle C.deficit) ≠ ⊤ from ?_)
        (measure_mono Set.inter_subset_left)
      rw [RowDeletion.volume_triangle hδ]
      exact ENNReal.ofReal_ne_top
    rw [RowDeletion.volume_triangle hδ] at hvol
    have h := (ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.mpr ⟨hgap, hbad⟩)).mp hvol
    rw [ENNReal.toReal_add hgap hbad] at h
    simpa only [max_eq_right hδ.le, Config.gapArea] using h
  · rw [max_eq_left (le_of_not_gt hδ)]
    have hgap := ENNReal.toReal_nonneg (a := volume C.uncovered)
    have hbad := ENNReal.toReal_nonneg
      (a := volume (RowDeletion.triangle C.deficit ∩ badSeeds C b a c))
    change (0 : ℝ) ^ 2 / 2 ≤ (volume C.uncovered).toReal + _
    linarith

/-- An obstructed seed forces every window strictly between its two supporting
levels on the triangle. -/
theorem bad_seed_implies_internal (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) {z : ℝ × ℝ}
    (hz : z ∈ RowDeletion.triangle C.deficit) (hzbad : z ∈ badSeeds C b a c) :
    (0 < (C.plank 0).lo ∧ (C.plank 0).hi < 1) ∧
      (0 < (C.plank 1).lo ∧ (C.plank 1).hi < 1) ∧
      (c - 1 < (C.plank 2).lo ∧ (C.plank 2).hi < c) := by
  have hr : ∀ i, 0 ≤ widths C i := fun i => sub_nonneg.mpr (C.plank i).lo_le_hi
  have hw : ∀ i, (C.plank i).hi = (C.plank i).lo + widths C i := by
    intro i
    dsimp [widths]
    ring
  have hdef := deficit_eq C hb ha hc hu₀ hu₁ hu₂
  have hbounds := CyclicAssignment.Bad.bounds
    (mul_nonneg hb.1.le (hr 1)) (mul_nonneg (sub_nonneg.mpr hb.2.le) (hr 2))
    (mul_nonneg ha.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr ha.2.le) (hr 2))
    (mul_nonneg hc.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr hc.2.le) (hr 1)) hzbad
  simp only [threshold, hu₀, hu₁, hu₂, base, dot, Prod.fst_add, Prod.snd_add] at hbounds
  rcases hbounds with ⟨hx0, hxpq, hys, hyr, hzu, hzt⟩
  change 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ C.deficit at hz
  have hrem : 0 ≤ C.deficit - (z.1 + z.2) := sub_nonneg.mpr hz.2.2
  rw [hw 0, hw 1, hw 2]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · nlinarith [mul_nonneg hb.1.le hz.2.1, mul_nonneg hb.1.le (hr 2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hb.2.le) hz.2.1,
      mul_nonneg (sub_nonneg.mpr hb.2.le) (hr 1)]
  · nlinarith [mul_nonneg ha.1.le hz.1, mul_nonneg ha.1.le (hr 2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2.le) hz.1,
      mul_nonneg (sub_nonneg.mpr ha.2.le) (hr 0)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hc.2.le) hrem,
      mul_nonneg (sub_nonneg.mpr hc.2.le) (hr 0)]
  · nlinarith [mul_nonneg hc.1.le hrem, mul_nonneg hc.1.le (hr 1)]

/-- A window meeting or extending beyond a supporting level closes the ABC
area bound, including the strict cyclic direction and width patterns. -/
theorem sqPos_of_noninternal (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (h : ¬ ((0 < (C.plank 0).lo ∧ (C.plank 0).hi < 1) ∧
      (0 < (C.plank 1).lo ∧ (C.plank 1).hi < 1) ∧
      (c - 1 < (C.plank 2).lo ∧ (C.plank 2).hi < c))) :
    Quant.SqPos C := by
  apply sqPos_of_no_bad_seed C hb ha hc hu₀ hu₁ hu₂
  intro z hz hzbad
  exact h (bad_seed_implies_internal C hb ha hc hu₀ hu₁ hu₂ hz hzbad)

theorem sqPos_of_bad_area_zero (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hbad : volume (RowDeletion.triangle C.deficit ∩ badSeeds C b a c) = 0) :
    Quant.SqPos C := by
  have h := positive_part_with_bad_area C hb ha hc hu₀ hu₁ hu₂
  rw [hbad, ENNReal.toReal_zero, add_zero] at h
  change (max 0 C.deficit) ^ 2 * (1 / 2) ≤ C.gapArea
  linarith

theorem abcConfig_sqPos_of_no_bad_seed (b a c : ℝ)
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hbad : ∀ z ∈ RowDeletion.triangle (abcConfig b a c hb ha hc lo hi hle).deficit,
      z ∉ badSeeds (abcConfig b a c hb ha hc lo hi hle) b a c) :
    Quant.SqPos (abcConfig b a c hb ha hc lo hi hle) :=
  sqPos_of_no_bad_seed _ hb ha hc rfl rfl rfl hbad

def UnobstructedOrbit (C : Config) : Prop :=
  ∃ (b a c : ℝ) (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1)
    (hc : 0 < c ∧ c < 1) (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i),
    (∀ z ∈ RowDeletion.triangle (abcConfig b a c hb ha hc lo hi hle).deficit,
      z ∉ badSeeds (abcConfig b a c hb ha hc lo hi hle) b a c) ∧
    C.Equiv (abcConfig b a c hb ha hc lo hi hle)

theorem moveOrbit_sqPos (C : Config) (h : UnobstructedOrbit C) : Quant.SqPos C := by
  obtain ⟨b, a, c, hb, ha, hc, lo, hi, hle, hbad, he⟩ := h
  have hD := abcConfig_sqPos_of_no_bad_seed b a c hb ha hc lo hi hle hbad
  simp only [Quant.SqPos, Config.deficit] at hD ⊢
  rw [he.sumRelW_eq, he.gapArea_eq]
  exact hD

end Quant.CyclicArea
