module
/-
# The square area bound for balanced ABC directions

The direction condition is a * (1-c) * (1-b) = (1-a) * c * b for
the normalized normals (1,b), (a,1), and (c,c-1). Window positions
are arbitrary. Zero-width planks are handled by nullity and chamber C.
-/
public import Plank.Proofs.Quant.SymmetricTranslations
public import Plank.Proofs.Quant.CommonVertexChambers

@[expose] public section

noncomputable section

namespace Quant.BalancedArea

open Set MeasureTheory CommonVertex

theorem volume_plank_zero_width (p : Plank) (h : p.lo = p.hi) :
    volume p.set = 0 := by
  have he : p.set = {x : ℝ × ℝ | dot p.u x = p.lo} := by
    ext x
    change (p.lo ≤ dot p.u x ∧ dot p.u x ≤ p.hi) ↔ dot p.u x = p.lo
    rw [← h]
    exact ⟨fun hx => le_antisymm hx.2 hx.1, fun hx => by rw [hx]; exact ⟨le_rfl, le_rfl⟩⟩
  rw [he]
  exact volume_line_zero p.u_ne_zero p.lo

/-- Any three-plank configuration with one zero-width plank satisfies the
positive-part bound, with arbitrary directions of the other two planks. -/
theorem positive_part_of_zero_width (C : Config) (i : Fin 3)
    (hi : (C.plank i).lo = (C.plank i).hi) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  classical
  let z : Plank := ⟨(1, 0), 0, 0,
    fun h => one_ne_zero (congrArg Prod.fst h), le_rfl⟩
  let D : Config := ⟨fun j => if j = i then z else C.plank j⟩
  have hD : D.ChamberC := by
    refine ⟨i, ?_⟩
    change SectorBoundary (if i = i then z else C.plank i).u
    simp only [ite_true]
    exact ⟨1, one_ne_zero, Or.inl (by simp [z])⟩
  have hr : ∀ j, D.relW j = C.relW j := by
    intro j
    by_cases hj : j = i
    · subst j
      simp [Config.relW, D, z, Plank.relWidth, hi]
    · simp [Config.relW, D, hj]
  have hd : D.deficit = C.deficit := by simp only [Config.deficit, Config.sumRelW, hr]
  have hsub : D.uncovered \ (C.plank i).set ⊆ C.uncovered := by
    intro x hx
    refine ⟨hx.1.1, ?_⟩
    intro hp
    obtain ⟨j, hj⟩ := mem_iUnion.mp hp
    by_cases hji : j = i
    · subst j
      exact hx.2 hj
    · apply hx.1.2
      apply mem_iUnion.mpr
      refine ⟨j, ?_⟩
      simpa only [D, hji, ↓reduceIte] using hj
  have hvol : volume D.uncovered ≤ volume C.uncovered := by
    calc
      volume D.uncovered = volume (D.uncovered \ (C.plank i).set) :=
        (measure_sdiff_null (volume_plank_zero_width (C.plank i) hi)).symm
      _ ≤ volume C.uncovered := measure_mono hsub
  have hfin : volume C.uncovered ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
      (measure_mono Set.sdiff_subset)
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  have h := CommonVertex.chamberC_positive_square_bound D hD
  rw [hd] at h
  exact h.trans (ENNReal.toReal_mono hfin hvol)

theorem abc_width_one (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) (i : Fin 3) :
    stdTriangle.width (C.plank i).u = 1 := by
  fin_cases i
  · change stdTriangle.width (C.plank 0).u = 1
    rw [hu₀, Proofs.Transport.stdTriangle_width_eq]
    simp only [max_def, min_def]
    split_ifs <;> linarith
  · change stdTriangle.width (C.plank 1).u = 1
    rw [hu₁, Proofs.Transport.stdTriangle_width_eq]
    simp only [max_def, min_def]
    split_ifs <;> linarith
  · change stdTriangle.width (C.plank 2).u = 1
    rw [hu₂, Proofs.Transport.stdTriangle_width_eq]
    simp only [max_def, min_def]
    split_ifs <;> linarith

/-- Strictly positive widths admit a symmetric potential built from the
three extreme chords. Every translated seed remains in the triangle. -/
theorem gap_bound_of_positive_widths (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hbalance : a * (1 - c) * (1 - b) = (1 - a) * c * b)
    (hpos : ∀ i, (C.plank i).lo < (C.plank i).hi) (hδ : 0 < C.deficit) :
    C.deficit ^ 2 / 2 ≤ C.gapArea := by
  classical
  let r : Fin 3 → ℝ := fun i => (C.plank i).hi - (C.plank i).lo
  have hr : ∀ i, 0 < r i := fun i => sub_pos.mpr (hpos i)
  have hrel : ∀ i, C.relW i = r i := by
    intro i
    rw [Config.relW, Plank.relWidth, abc_width_one C hb ha hc hu₀ hu₁ hu₂, div_one]
  have hdef : C.deficit = 1 - (r 0 + r 1 + r 2) := by
    simp only [Config.deficit, Config.sumRelW, hrel, Fin.sum_univ_three]
  let v : Fin 3 → ℝ × ℝ := ![(r 0, 0), (0, r 1), (r 2, -r 2)]
  let w : Fin 3 → ℝ := ![r 0 * a * (1 - c), r 1 * b * (1 - c),
    r 2 * b * (1 - a)]
  have hu : ∀ i, (C.plank i).u = ![(1, b), (a, 1), (c, c - 1)] i := by
    intro i
    fin_cases i
    · exact hu₀
    · exact hu₁
    · exact hu₂
  have hw : ∀ i, 0 < w i := by
    intro i
    fin_cases i <;> dsimp [w]
    · exact mul_pos (mul_pos (hr 0) ha.1) (sub_pos.mpr hc.2)
    · exact mul_pos (mul_pos (hr 1) hb.1) (sub_pos.mpr hc.2)
    · exact mul_pos (mul_pos (hr 2) hb.1) (sub_pos.mpr ha.2)
  have hself : ∀ i, dot (C.plank i).u (v i) = (C.plank i).hi - (C.plank i).lo := by
    intro i
    rw [hu]
    change dot (![(1, b), (a, 1), (c, c - 1)] i) (v i) = r i
    fin_cases i <;> dsimp [v, dot] <;> ring
  have hsym : ∀ i j, w i * dot (C.plank i).u (v j) =
      w j * dot (C.plank j).u (v i) := by
    have hk := congrArg (fun z : ℝ => r 0 * r 2 * z) hbalance
    intro i j
    rw [hu i, hu j]
    fin_cases i <;> fin_cases j <;> dsimp [w, v, dot] <;> nlinarith only [hk]
  let base : ℝ × ℝ := (0, r 2)
  let core := RowDeletion.triangle C.deficit
  have hinside : ∀ (s : Finset (Fin 3)) (t : ℝ × ℝ), t ∈ core →
      t + (base + shift v s) ∈ stdTriangle.set := by
    intro s t ht
    have he : shift v s = ∑ i : Fin 3, if i ∈ s then v i else 0 := by
      simp [shift, Finset.sum_ite_mem]
    rw [he, Fin.sum_univ_three, Proofs.Quant.stdTriangle_set_eq]
    change 0 ≤ t.1 ∧ 0 ≤ t.2 ∧ t.1 + t.2 ≤ C.deficit at ht
    rw [hdef] at ht
    by_cases h₀ : (0 : Fin 3) ∈ s <;> by_cases h₁ : (1 : Fin 3) ∈ s <;>
      by_cases h₂ : (2 : Fin 3) ∈ s <;>
      simp only [h₀, h₁, h₂, ↓reduceIte, v, base, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
        Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero,
        mem_ofPred_eq] <;>
      constructor <;> (try constructor) <;> linarith [hr 0, hr 1, hr 2]
  have hvol : volume core ≤ volume C.uncovered := by
    apply SymmetricTranslations.volume_le_gap_of_translations C.plank core
      (RowDeletion.measurableSet_triangle _) (fun s => base + shift v s)
    · intro t _
      simpa only [add_assoc] using
        SymmetricTranslations.exists_side_assignment C.plank v w hw hself hsym (t + base)
    · exact hinside
  have hfin : volume C.uncovered ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
      (measure_mono Set.sdiff_subset)
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  rw [RowDeletion.volume_triangle hδ] at hvol
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hvol

/-- Balanced ABC directions, arbitrary closed windows, and all width budgets. -/
theorem positive_part (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hbalance : a * (1 - c) * (1 - b) = (1 - a) * c * b) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  by_cases hδ : 0 < C.deficit
  · by_cases hpos : ∀ i, (C.plank i).lo < (C.plank i).hi
    · rw [max_eq_right hδ.le]
      exact gap_bound_of_positive_widths C hb ha hc hu₀ hu₁ hu₂ hbalance hpos hδ
    · push Not at hpos
      obtain ⟨i, hi⟩ := hpos
      exact positive_part_of_zero_width C i (le_antisymm (C.plank i).lo_le_hi hi)
  · rw [max_eq_left (le_of_not_gt hδ)]
    simp [Config.gapArea]

theorem sqBound (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1))
    (hbalance : a * (1 - c) * (1 - b) = (1 - a) * c * b)
    (hs : C.sumRelW ≤ 1) : C.SqBound := by
  have h := positive_part C hb ha hc hu₀ hu₁ hu₂ hbalance
  have hd : 0 ≤ C.deficit := by unfold Config.deficit; linarith
  rw [max_eq_right hd] at h
  change C.deficit ^ 2 * (1 / 2) ≤ C.gapArea
  linarith

theorem abcConfig_sqPos (b a c : ℝ)
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hbalance : a * (1 - c) * (1 - b) = (1 - a) * c * b) :
    Quant.SqPos (abcConfig b a c hb ha hc lo hi hle) := by
  have h := positive_part (abcConfig b a c hb ha hc lo hi hle)
    hb ha hc rfl rfl rfl hbalance
  change (max 0 (abcConfig b a c hb ha hc lo hi hle).deficit) ^ 2 * (1 / 2) ≤ _
  linarith

/-- The balanced family, allowing all existing configuration moves. This
predicate imposes a genuine direction restriction on the ABC chamber. -/
def BalancedOrbit (C : Config) : Prop :=
  ∃ (b a c : ℝ) (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1)
    (hc : 0 < c ∧ c < 1) (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i),
    a * (1 - c) * (1 - b) = (1 - a) * c * b ∧
    C.Equiv (abcConfig b a c hb ha hc lo hi hle)

theorem moveOrbit_sqPos (C : Config) (h : BalancedOrbit C) : Quant.SqPos C := by
  obtain ⟨b, a, c, hb, ha, hc, lo, hi, hle, hbalance, he⟩ := h
  have hD := abcConfig_sqPos b a c hb ha hc lo hi hle hbalance
  simp only [Quant.SqPos, Config.deficit] at hD ⊢
  rw [he.sumRelW_eq, he.gapArea_eq]
  exact hD

theorem sqPos_of_zero_width (C : Config) (i : Fin 3)
    (hi : (C.plank i).lo = (C.plank i).hi) : Quant.SqPos C := by
  have h := positive_part_of_zero_width C i hi
  change (max 0 C.deficit) ^ 2 * (1 / 2) ≤ C.gapArea
  linarith

end Quant.BalancedArea
