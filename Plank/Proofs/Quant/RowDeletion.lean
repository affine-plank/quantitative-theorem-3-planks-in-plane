module
/-
# A second sweep pays for deleted rows

If every surviving vertical row loses at most W of its length, and the
set of deleted row coordinates has length at most R, the uncovered area
is at least max(0, 1-W-R)^2/2. The second Fubini sweep proves this without
any restriction on the positions or number of deleted intervals.
-/
public import Plank.Proofs.Quant

@[expose] public section

noncomputable section

namespace Quant.RowDeletion

open Set MeasureTheory
open scoped Pointwise

def triangle (k : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ k}

theorem measurableSet_triangle (k : ℝ) : MeasurableSet (triangle k) :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))

theorem row_triangle {x : ℝ} (hx : 0 ≤ x) (k : ℝ) :
    Prod.mk x ⁻¹' triangle k = Icc 0 (k - x) := by
  ext y
  change (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ k) ↔ 0 ≤ y ∧ y ≤ k - x
  constructor
  · rintro ⟨_, hy, hxy⟩
    exact ⟨hy, by linarith⟩
  · rintro ⟨hy, hxy⟩
    exact ⟨hx, hy, by linarith⟩

theorem column_triangle {y : ℝ} (hy : 0 ≤ y) (k : ℝ) :
    {x : ℝ | (x, y) ∈ triangle k} = Icc 0 (k - y) := by
  ext x
  change (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ k) ↔ 0 ≤ x ∧ x ≤ k - y
  constructor
  · rintro ⟨hx, _, hxy⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨hx, hy, by linarith⟩

theorem volume_triangle {k : ℝ} (hk : 0 < k) :
    volume (triangle k) = ENNReal.ofReal (k ^ 2 / 2) := by
  have himg : k • stdTriangle.set = triangle k := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [Proofs.Quant.stdTriangle_set_eq] at hq
      change 0 ≤ k * q.1 ∧ 0 ≤ k * q.2 ∧ k * q.1 + k * q.2 ≤ k
      exact ⟨mul_nonneg hk.le hq.1, mul_nonneg hk.le hq.2.1,
        by nlinarith [hq.2.2]⟩
    · rintro ⟨hx, hy, hxy⟩
      refine ⟨(p.1 / k, p.2 / k), ?_, ?_⟩
      · rw [Proofs.Quant.stdTriangle_set_eq]
        refine ⟨div_nonneg hx hk.le, div_nonneg hy hk.le, ?_⟩
        rw [← add_div, div_le_one hk]
        exact hxy
      · ext <;> dsimp <;> field_simp
  rw [← himg, Measure.addHaar_smul_of_nonneg volume hk.le,
    Proofs.Quant.volume_stdTriangle]
  rw [show Module.finrank ℝ (ℝ × ℝ) = 2 by simp,
    ← ENNReal.ofReal_mul (sq_nonneg k)]
  congr 1
  ring

/-- Only the measure of the removed set matters in this one-dimensional estimate. -/
theorem volume_Icc_diff_ge {A : Set ℝ} {R c d : ℝ}
    (hR : 0 ≤ R) (hA : volume A ≤ ENNReal.ofReal R) :
    ENNReal.ofReal ((d - c) - R) ≤ volume (Icc c d \ A) := by
  have hsub : Icc c d ⊆ (Icc c d \ A) ∪ A := by
    intro x hx
    by_cases ha : x ∈ A
    · exact Or.inr ha
    · exact Or.inl ⟨hx, ha⟩
  have h := (measure_mono (μ := volume) hsub).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl hA))
  rw [Real.volume_Icc] at h
  rw [ENNReal.ofReal_sub _ hR]
  exact tsub_le_iff_right.mpr h

/-- Row deletion costs its one-dimensional measure in the deficit budget.
The measurable set U need not be convex or itself a plank complement. -/
theorem gap_of_row_budget {U : Set (ℝ × ℝ)} {A : Set ℝ} {W R : ℝ}
    (hU : MeasurableSet U) (hA : MeasurableSet A) (hR : 0 ≤ R)
    (hAR : volume A ≤ ENNReal.ofReal R)
    (hrow : ∀ x : ℝ, 0 ≤ x → x ∉ A →
      ENNReal.ofReal (1 - W - x) ≤ volume (Prod.mk x ⁻¹' U)) :
    ENNReal.ofReal ((max 0 (1 - W - R)) ^ 2 / 2) ≤ volume U := by
  by_cases hδ : 0 < 1 - W - R
  · rw [max_eq_right hδ.le]
    let D : Set (ℝ × ℝ) := triangle (1 - W) \ Prod.fst ⁻¹' A
    have hD : MeasurableSet D :=
      (measurableSet_triangle _).diff (hA.preimage measurable_fst)
    have hfirst : volume D ≤ volume U := by
      rw [Measure.volume_eq_prod, Measure.prod_apply hD, Measure.prod_apply hU]
      apply lintegral_mono
      intro x
      change volume (Prod.mk x ⁻¹' D) ≤ volume (Prod.mk x ⁻¹' U)
      by_cases hx : 0 ≤ x
      · by_cases hxa : x ∈ A
        · have he : Prod.mk x ⁻¹' D = ∅ := by
            ext y
            simp [D, hxa]
          rw [he, measure_empty]
          exact zero_le
        · have hs : Prod.mk x ⁻¹' D = Icc 0 (1 - W - x) := by
            rw [Set.preimage_sdiff, row_triangle hx]
            have he : (Prod.mk x : ℝ → ℝ × ℝ) ⁻¹' (Prod.fst ⁻¹' A) = ∅ := by
              ext y
              simp [hxa]
            rw [he, Set.sdiff_empty]
          rw [hs, Real.volume_Icc, sub_zero]
          exact hrow x hx hxa
      · have he : Prod.mk x ⁻¹' D = ∅ := by
          ext y
          simp [D, triangle, hx]
        rw [he, measure_empty]
        exact zero_le
    have hsecond : volume (triangle (1 - W - R)) ≤ volume D := by
      rw [Measure.volume_eq_prod,
        Measure.prod_apply_symm (measurableSet_triangle _), Measure.prod_apply_symm hD]
      apply lintegral_mono
      intro y
      change volume {x : ℝ | (x, y) ∈ triangle (1 - W - R)} ≤
        volume {x : ℝ | (x, y) ∈ D}
      by_cases hy : 0 ≤ y
      · have hs : {x : ℝ | (x, y) ∈ D} = Icc 0 (1 - W - y) \ A := by
          ext x
          change (0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 - W) ∧ x ∉ A ↔
            (0 ≤ x ∧ x ≤ 1 - W - y) ∧ x ∉ A
          constructor
          · rintro ⟨⟨hx, _, hxy⟩, ha⟩
            exact ⟨⟨hx, by linarith⟩, ha⟩
          · rintro ⟨⟨hx, hxy⟩, ha⟩
            exact ⟨⟨hx, hy, by linarith⟩, ha⟩
        rw [column_triangle hy, Real.volume_Icc, sub_zero, hs]
        convert volume_Icc_diff_ge (c := 0) (d := 1 - W - y) hR hAR using 1
        congr 1
        ring
      · have he : {x : ℝ | (x, y) ∈ triangle (1 - W - R)} = ∅ := by
          ext x
          simp [triangle, hy]
        rw [he, measure_empty]
        exact zero_le
    rw [volume_triangle hδ] at hsecond
    exact hsecond.trans hfirst
  · rw [max_eq_left (le_of_not_gt hδ)]
    simp

theorem interval_union_budget {ι : Type*} [Fintype ι]
    (lo hi : ι → ℝ) (hle : ∀ i, lo i ≤ hi i) :
    volume (⋃ i, Icc (lo i) (hi i)) ≤ ENNReal.ofReal (∑ i, (hi i - lo i)) := by
  have h := measure_iUnion_fintype_le volume (fun i => Icc (lo i) (hi i))
  simp only [Real.volume_Icc] at h
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hle i))]
  exact h

theorem row_plank (p : Plank) (hp : p.u.2 = 1) (x : ℝ) :
    Prod.mk x ⁻¹' p.set = Icc (p.lo - p.u.1 * x) (p.hi - p.u.1 * x) := by
  ext y
  change (p.lo ≤ dot p.u (x, y) ∧ dot p.u (x, y) ≤ p.hi) ↔
    p.lo - p.u.1 * x ≤ y ∧ y ≤ p.hi - p.u.1 * x
  simp only [dot, hp, one_mul]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Any finite number of row-constant planks, together with any finite
number of planks that delete entire rows. The budget here is trace width. -/
theorem finite_planks_trace_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → Plank) (q : κ → Plank)
    (hp : ∀ i, (p i).u.2 = 1) (hq : ∀ j, (q j).u = (1, 0)) :
    ENNReal.ofReal ((max 0 (1 - (∑ i, ((p i).hi - (p i).lo)) -
      ∑ j, ((q j).hi - (q j).lo))) ^ 2 / 2) ≤
      volume (stdTriangle.set \ ((⋃ i, (p i).set) ∪ ⋃ j, (q j).set)) := by
  let A : Set ℝ := ⋃ j, Icc (q j).lo (q j).hi
  apply gap_of_row_budget
    (A := A)
    (hU := Proofs.Quant.measurableSet_stdTriangle.diff
      ((MeasurableSet.iUnion fun i => Proofs.Quant.measurableSet_plank (p i)).union
        (MeasurableSet.iUnion fun j => Proofs.Quant.measurableSet_plank (q j))))
    (hA := MeasurableSet.iUnion fun _ => measurableSet_Icc)
    (hR := Finset.sum_nonneg fun j _ => sub_nonneg.mpr (q j).lo_le_hi)
    (hAR := interval_union_budget _ _ fun j => (q j).lo_le_hi)
  intro x hx hxa
  have hqrows : ∀ j, Prod.mk x ⁻¹' (q j).set = ∅ := by
    intro j
    have hout : x ∉ Icc (q j).lo (q j).hi := fun hj => hxa (mem_iUnion.mpr ⟨j, hj⟩)
    ext y
    change ((q j).lo ≤ dot (q j).u (x, y) ∧
      dot (q j).u (x, y) ≤ (q j).hi) ↔ False
    simpa [hq j, dot] using hout
  have hrows : ∀ i, Prod.mk x ⁻¹' (p i).set =
      Icc ((p i).lo - (p i).u.1 * x) ((p i).hi - (p i).u.1 * x) :=
    fun i => row_plank (p i) (hp i) x
  have ht : Prod.mk x ⁻¹' stdTriangle.set = Icc 0 (1 - x) := by
    rw [Proofs.Quant.stdTriangle_set_eq]
    exact row_triangle hx 1
  simp only [Set.preimage_sdiff, Set.preimage_union, Set.preimage_iUnion,
    ht, hqrows, hrows, Set.iUnion_empty, Set.union_empty]
  have hw : (∑ i, ((p i).hi - (p i).u.1 * x - ((p i).lo - (p i).u.1 * x)))
      = ∑ i, ((p i).hi - (p i).lo) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hbud := interval_union_budget
    (fun i => (p i).lo - (p i).u.1 * x)
    (fun i => (p i).hi - (p i).u.1 * x)
    (fun i => by linarith [(p i).lo_le_hi])
  rw [hw] at hbud
  have h := volume_Icc_diff_ge (c := 0) (d := 1 - x)
    (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (p i).lo_le_hi) hbud
  convert h using 1
  congr 1
  ring

/-- A closed sector of directions and the opposite edge-parallel direction.
This is the sharp relative-area estimate for arbitrary finite families. -/
theorem finite_planks_relative_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → Plank) (q : κ → Plank)
    (hp : ∀ i, (p i).u.2 = 1)
    (hb : ∀ i, 0 ≤ (p i).u.1 ∧ (p i).u.1 ≤ 1)
    (hq : ∀ j, (q j).u = (1, 0)) :
    ENNReal.ofReal ((max 0 (1 - ((∑ i, (p i).relWidth stdTriangle) +
      ∑ j, (q j).relWidth stdTriangle))) ^ 2 / 2) ≤
      volume (stdTriangle.set \ ((⋃ i, (p i).set) ∪ ⋃ j, (q j).set)) := by
  have hwp : ∀ i, (p i).relWidth stdTriangle = (p i).hi - (p i).lo := by
    intro i
    norm_num [Plank.relWidth, Proofs.Transport.stdTriangle_width_eq, hp i,
      max_eq_right (hb i).2, min_eq_left (hb i).2, min_eq_left (hb i).1]
  have hwq : ∀ j, (q j).relWidth stdTriangle = (q j).hi - (q j).lo := by
    intro j
    norm_num [Plank.relWidth, Proofs.Transport.stdTriangle_width_eq, hq j]
  simpa only [hwp, hwq, sub_add_eq_sub_sub] using finite_planks_trace_bound p q hp hq

/-- The three-plank client: one vertical plank and two arbitrary planks
whose normalized normals lie in the opposite closed sector. -/
theorem config_positive_square_bound (C : Config) {b₁ b₂ : ℝ}
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1)
    (hu₀ : (C.plank 0).u = (1, 0))
    (hu₁ : (C.plank 1).u = (b₁, 1))
    (hu₂ : (C.plank 2).u = (b₂, 1)) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  have hp : ∀ i : Fin 2, (C.plank i.succ).u.2 = 1 := by
    intro i
    fin_cases i <;> simp [hu₁, hu₂]
  have hb : ∀ i : Fin 2, 0 ≤ (C.plank i.succ).u.1 ∧
      (C.plank i.succ).u.1 ≤ 1 := by
    intro i
    fin_cases i
    · simpa [hu₁] using hb₁
    · simpa [hu₂] using hb₂
  have h := finite_planks_relative_bound (fun i : Fin 2 => C.plank i.succ)
    (fun _ : Fin 1 => C.plank 0) hp hb (fun _ => hu₀)
  have hset : stdTriangle.set \ ((⋃ i : Fin 2, (C.plank i.succ).set) ∪
      ⋃ _ : Fin 1, (C.plank 0).set) = C.uncovered := by
    ext x
    simp [Config.uncovered, Fin.exists_fin_succ]
    tauto
  have hsum : (∑ i : Fin 2, (C.plank i.succ).relWidth stdTriangle) +
      (∑ _ : Fin 1, (C.plank 0).relWidth stdTriangle) = C.sumRelW := by
    simp only [Fin.sum_univ_two, Fin.sum_univ_one, Config.sumRelW, Fin.sum_univ_three,
      Config.relW]
    change (C.plank 1).relWidth stdTriangle + (C.plank 2).relWidth stdTriangle +
        (C.plank 0).relWidth stdTriangle =
      (C.plank 0).relWidth stdTriangle + (C.plank 1).relWidth stdTriangle +
        (C.plank 2).relWidth stdTriangle
    ring
  rw [hset, hsum] at h
  have hfin : volume C.uncovered ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
      (measure_mono Set.sdiff_subset)
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h

theorem config_sqBound (C : Config) {b₁ b₂ : ℝ}
    (hb₁ : 0 ≤ b₁ ∧ b₁ ≤ 1) (hb₂ : 0 ≤ b₂ ∧ b₂ ≤ 1)
    (hu₀ : (C.plank 0).u = (1, 0))
    (hu₁ : (C.plank 1).u = (b₁, 1))
    (hu₂ : (C.plank 2).u = (b₂, 1))
    (hs : C.sumRelW ≤ 1) : C.SqBound := by
  have h := config_positive_square_bound C hb₁ hb₂ hu₀ hu₁ hu₂
  have hd : 0 ≤ C.deficit := by unfold Config.deficit; linarith
  rw [max_eq_right hd] at h
  change C.deficit ^ 2 * (1 / 2) ≤ C.gapArea
  linarith

end Quant.RowDeletion
