module
/-
# ABC area bounds from compatible width comparisons

The actual interactions need not be symmetric. Their three local orders
can instead be represented by a symmetric auxiliary matrix. This covers
six weak comparison patterns and leaves two strictly cyclic patterns.
-/
public import Plank.Proofs.Quant.OrdinalMatrix
public import Plank.Proofs.Quant.BalancedArea

@[expose] public section

noncomputable section

namespace Quant.OrdinalArea

open Set MeasureTheory CommonVertex

def widths (C : Config) (i : Fin 3) : ℝ := (C.plank i).hi - (C.plank i).lo

def steps (r : Fin 3 → ℝ) : Fin 3 → ℝ × ℝ := ![(r 0, 0), (0, r 1), (r 2, -r 2)]

def CompatibleWidths (C : Config) (b a c : ℝ) : Prop :=
  OrdinalMatrix.Compatible
    (b * widths C 1) ((1 - b) * widths C 2)
    (a * widths C 0) ((1 - a) * widths C 2)
    (c * widths C 0) ((1 - c) * widths C 1)

/-- The two strict cyclic comparisons left by the ordinal construction. -/
def CyclicWidths (C : Config) (b a c : ℝ) : Prop :=
  (((1 - b) * widths C 2 < b * widths C 1 ∧
    a * widths C 0 < (1 - a) * widths C 2 ∧
    (1 - c) * widths C 1 < c * widths C 0) ∨
   (b * widths C 1 < (1 - b) * widths C 2 ∧
    (1 - a) * widths C 2 < a * widths C 0 ∧
    c * widths C 0 < (1 - c) * widths C 1))

theorem compatible_iff_not_cyclic (C : Config) (b a c : ℝ) :
    CompatibleWidths C b a c ↔ ¬ CyclicWidths C b a c :=
  OrdinalMatrix.compatible_iff_not_cycles _ _ _ _ _ _

theorem compatible_of_balance (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hbalance : a * (1 - c) * (1 - b) = (1 - a) * c * b) :
    CompatibleWidths C b a c := by
  have hr : ∀ i, 0 ≤ widths C i := fun i => sub_nonneg.mpr (C.plank i).lo_le_hi
  apply OrdinalMatrix.compatible_of_product_eq
    (b * widths C 1) ((1 - b) * widths C 2)
    (a * widths C 0) ((1 - a) * widths C 2)
    (c * widths C 0) ((1 - c) * widths C 1)
    (mul_nonneg hb.1.le (hr 1)) (mul_nonneg (sub_nonneg.mpr hb.2.le) (hr 2))
    (mul_nonneg ha.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr ha.2.le) (hr 2))
    (mul_nonneg hc.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr hc.2.le) (hr 1))
  calc
    b * widths C 1 * ((1 - a) * widths C 2) * (c * widths C 0) =
        ((1 - a) * c * b) * (widths C 0 * widths C 1 * widths C 2) := by ring
    _ = (a * (1 - c) * (1 - b)) * (widths C 0 * widths C 1 * widths C 2) := by
      rw [hbalance]
    _ = (1 - b) * widths C 2 * (a * widths C 0) * ((1 - c) * widths C 1) := by ring

theorem translated_mem_triangle (r : Fin 3 → ℝ) (hr : ∀ i, 0 ≤ r i)
    (s : Finset (Fin 3)) (t : ℝ × ℝ)
    (ht : t ∈ RowDeletion.triangle (1 - (r 0 + r 1 + r 2))) :
    t + ((0, r 2) + shift (steps r) s) ∈ stdTriangle.set := by
  classical
  have he : shift (steps r) s = ∑ i : Fin 3, if i ∈ s then steps r i else 0 := by
    simp [shift, Finset.sum_ite_mem]
  rw [he, Fin.sum_univ_three, Proofs.Quant.stdTriangle_set_eq]
  change 0 ≤ t.1 ∧ 0 ≤ t.2 ∧ t.1 + t.2 ≤ 1 - (r 0 + r 1 + r 2) at ht
  by_cases h₀ : (0 : Fin 3) ∈ s <;> by_cases h₁ : (1 : Fin 3) ∈ s <;>
    by_cases h₂ : (2 : Fin 3) ∈ s <;>
    simp only [h₀, h₁, h₂, ↓reduceIte, steps, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Fin.isValue,
      Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero,
      mem_ofPred_eq] <;>
    constructor <;> (try constructor) <;> linarith [hr 0, hr 1, hr 2]

/-- The six compatible width patterns give the actual positive-part area
bound, at arbitrary positions and including zero-width planks. -/
theorem positive_part (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) (hcompat : CompatibleWidths C b a c) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  classical
  by_cases hδ : 0 < C.deficit
  · rw [max_eq_right hδ.le]
    let r := widths C
    have hr : ∀ i, 0 ≤ r i := fun i => sub_nonneg.mpr (C.plank i).lo_le_hi
    have hrel : ∀ i, C.relW i = r i := by
      intro i
      rw [Config.relW, Plank.relWidth, BalancedArea.abc_width_one C hb ha hc hu₀ hu₁ hu₂,
        div_one]
      rfl
    have hdef : C.deficit = 1 - (r 0 + r 1 + r 2) := by
      simp only [Config.deficit, Config.sumRelW, hrel, Fin.sum_univ_three]
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
    have hreal : ∀ i j, OrdinalTranslations.interaction C.plank (steps r) i j =
        OrdinalMatrix.matrix (b * r 1) ((1 - b) * r 2)
          (a * r 0) ((1 - a) * r 2) (c * r 0) ((1 - c) * r 1) i j := by
      intro i j
      simp only [OrdinalTranslations.interaction, hu]
      fin_cases i <;> fin_cases j <;> norm_num [steps, OrdinalMatrix.matrix, dot] <;> ring
    obtain ⟨x, y, z, hx, hy, hz, ho₀, ho₁, ho₂⟩ := OrdinalMatrix.exists_model
      (b * r 1) ((1 - b) * r 2) (a * r 0) ((1 - a) * r 2)
      (c * r 0) ((1 - c) * r 1) hcompat
    have horder := OrdinalMatrix.matrix_order
      (b * r 1) ((1 - b) * r 2) (a * r 0) ((1 - a) * r 2)
      (c * r 0) ((1 - c) * r 1) x y z
      (mul_nonneg hb.1.le (hr 1)) (mul_nonneg (sub_nonneg.mpr hb.2.le) (hr 2))
      (mul_nonneg ha.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr ha.2.le) (hr 2))
      (mul_nonneg hc.1.le (hr 0)) (mul_nonneg (sub_nonneg.mpr hc.2.le) (hr 1))
      hx hy hz ho₀ ho₁ ho₂
    have hactual : ∀ (i : Fin 3) (S T : Finset (Fin 3)),
        S.sum (OrdinalMatrix.model x y z i) ≤ T.sum (OrdinalMatrix.model x y z i) →
        S.sum (OrdinalTranslations.interaction C.plank (steps r) i) ≤
          T.sum (OrdinalTranslations.interaction C.plank (steps r) i) := by
      intro i S T h
      simpa only [hreal] using horder i S T h
    let base : ℝ × ℝ := (0, r 2)
    let core := RowDeletion.triangle C.deficit
    have hvol : volume core ≤ volume C.uncovered := by
      apply SymmetricTranslations.volume_le_gap_of_translations C.plank core
        (RowDeletion.measurableSet_triangle _)
        (fun s => base + shift (steps r) s)
      · intro t _
        simpa only [add_assoc] using OrdinalTranslations.exists_side_assignment
          C.plank (steps r) (OrdinalMatrix.model x y z)
          (OrdinalMatrix.model_symmetric x y z) (OrdinalMatrix.model_diagonal x y z)
          hself hactual (t + base)
      · intro s t ht
        apply translated_mem_triangle r hr s t
        simpa only [core, hdef] using ht
    have hfin : volume C.uncovered ≠ ⊤ := by
      apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
        (measure_mono Set.sdiff_subset)
      rw [Proofs.Quant.volume_stdTriangle]
      exact ENNReal.ofReal_ne_top
    rw [RowDeletion.volume_triangle hδ] at hvol
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hvol
  · rw [max_eq_left (le_of_not_gt hδ)]
    simp [Config.gapArea]

theorem sqPos (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) (hcompat : CompatibleWidths C b a c) :
    Quant.SqPos C := by
  have h := positive_part C hb ha hc hu₀ hu₁ hu₂ hcompat
  change (max 0 C.deficit) ^ 2 * (1 / 2) ≤ C.gapArea
  linarith

theorem abcConfig_sqPos (b a c : ℝ)
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hcompat : CompatibleWidths (abcConfig b a c hb ha hc lo hi hle) b a c) :
    Quant.SqPos (abcConfig b a c hb ha hc lo hi hle) :=
  sqPos _ hb ha hc rfl rfl rfl hcompat

theorem sqPos_of_not_cyclic (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1, b)) (hu₁ : (C.plank 1).u = (a, 1))
    (hu₂ : (C.plank 2).u = (c, c - 1)) (h : ¬ CyclicWidths C b a c) :
    Quant.SqPos C :=
  sqPos C hb ha hc hu₀ hu₁ hu₂ ((compatible_iff_not_cyclic C b a c).mpr h)

def CompatibleOrbit (C : Config) : Prop :=
  ∃ (b a c : ℝ) (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1)
    (hc : 0 < c ∧ c < 1) (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i),
    CompatibleWidths (abcConfig b a c hb ha hc lo hi hle) b a c ∧
    C.Equiv (abcConfig b a c hb ha hc lo hi hle)

theorem moveOrbit_sqPos (C : Config) (h : CompatibleOrbit C) : Quant.SqPos C := by
  obtain ⟨b, a, c, hb, ha, hc, lo, hi, hle, hcompat, he⟩ := h
  have hD := abcConfig_sqPos b a c hb ha hc lo hi hle hcompat
  simp only [Quant.SqPos, Config.deficit] at hD ⊢
  rw [he.sumRelW_eq, he.gapArea_eq]
  exact hD

end Quant.OrdinalArea
