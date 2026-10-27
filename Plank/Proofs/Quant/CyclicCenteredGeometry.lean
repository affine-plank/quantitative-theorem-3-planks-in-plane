module
/- # Area tools for the centered cyclic family -/
public import Plank.Proofs.Quant.CommonVertex
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

noncomputable section

namespace Quant.CyclicCenteredGeometry

open Set MeasureTheory

theorem volume_triangle_posPart (A : ℝ) :
    volume (RowDeletion.triangle A) = ENNReal.ofReal ((max 0 A) ^ 2 / 2) := by
  rcases lt_trichotomy A 0 with h | h | h
  · have he : RowDeletion.triangle A = ∅ := by
      ext x
      simp only [RowDeletion.triangle, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨hx, hy, hxy⟩
      linarith
    rw [he, measure_empty, max_eq_left h.le]
    norm_num
  · subst A
    have he : RowDeletion.triangle 0 = {((0 : ℝ), (0 : ℝ))} := by
      ext x
      simp only [RowDeletion.triangle, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨hx, hy, hxy⟩
        apply Prod.ext <;> dsimp <;> linarith
      · rintro rfl
        norm_num
    rw [he, measure_singleton]
    norm_num
  · rw [RowDeletion.volume_triangle h, max_eq_right h.le]

/-- A triangle between two affine lines, parameterized so its area is
the positive-part square of `A`, divided by `2B`. -/
def wedge (A B p q : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 - p - q * x.1 ∧
    B * x.1 + (x.2 - p - q * x.1) ≤ A}

def wedgeLinear (B q : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (B * x.1, x.2 - q * x.1)
  map_add' x y := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] <;> ring
  map_smul' r x := by
    apply Prod.ext <;>
      simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul,
        Prod.smul_mk] <;> ring

theorem det_wedgeLinear (B q : ℝ) : LinearMap.det (wedgeLinear B q) = B := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, wedgeLinear, Module.Basis.finTwoProd]

theorem volume_wedge (A B p q : ℝ) (hB : 0 < B) :
    volume (wedge A B p q) = ENNReal.ofReal ((max 0 A) ^ 2 / (2 * B)) := by
  let v : ℝ × ℝ := (0, -p)
  have he : wedge A B p q = (wedgeLinear B q) ⁻¹'
      ((fun x => x + v) ⁻¹' RowDeletion.triangle A) := by
    ext x
    change (0 ≤ x.1 ∧ 0 ≤ x.2 - p - q * x.1 ∧
      B * x.1 + (x.2 - p - q * x.1) ≤ A) ↔
      (0 ≤ B * x.1 + 0 ∧ 0 ≤ x.2 - q * x.1 + -p ∧
        (B * x.1 + 0) + (x.2 - q * x.1 + -p) ≤ A)
    constructor
    · rintro ⟨hx, hy, hxy⟩
      exact ⟨by nlinarith, by linarith, by linarith⟩
    · rintro ⟨hx, hy, hxy⟩
      exact ⟨by nlinarith, by linarith, by linarith⟩
  rw [he, Measure.addHaar_preimage_linearMap volume
    (by rw [det_wedgeLinear]; exact hB.ne'),
    det_wedgeLinear, measure_preimage_add_right, volume_triangle_posPart,
    abs_of_pos (inv_pos.mpr hB), ← ENNReal.ofReal_mul (inv_pos.mpr hB).le]
  congr 1
  ring

/-- The three cyclic barycentric functionals, written in planar coordinates. -/
def value (d : ℝ) (i : Fin 3) (p : ℝ × ℝ) : ℝ :=
  ![1 - (1 - d) * p.1 - p.2, p.1 + d * p.2,
    d - d * p.1 + (1 - d) * p.2] i

theorem value_sum (d : ℝ) (p : ℝ × ℝ) :
    value d 0 p + value d 1 p + value d 2 p = 1 + d := by
  dsimp [value]
  ring

theorem continuous_value (d : ℝ) (i : Fin 3) : Continuous (value d i) := by
  change Continuous (fun p => value d i p)
  fin_cases i <;> dsimp [value] <;> fun_prop

/-- The closed region where two consecutive cyclic values are below a level. -/
def lowCell (d l : ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ {p | value d i p ≤ l ∧ value d (i + 1) p ≤ l}

/-- The closed region where two consecutive cyclic values are above a level. -/
def highCell (d h : ℝ) (i : Fin 3) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ {p | h ≤ value d i p ∧ h ≤ value d (i + 1) p}

theorem measurableSet_lowCell (d l : ℝ) (i : Fin 3) :
    MeasurableSet (lowCell d l i) :=
  Proofs.GapCells.isCompact_stdTriangle.isClosed.measurableSet.inter
    ((measurableSet_le (continuous_value d i).measurable measurable_const).inter
      (measurableSet_le (continuous_value d (i + 1)).measurable measurable_const))

theorem measurableSet_highCell (d h : ℝ) (i : Fin 3) :
    MeasurableSet (highCell d h i) :=
  Proofs.GapCells.isCompact_stdTriangle.isClosed.measurableSet.inter
    ((measurableSet_le measurable_const (continuous_value d i).measurable).inter
      (measurableSet_le measurable_const (continuous_value d (i + 1)).measurable))

theorem volume_lowCell_ne_top (d l : ℝ) (i : Fin 3) :
    volume (lowCell d l i) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
    (measure_mono Set.inter_subset_left)
  rw [Proofs.Quant.volume_stdTriangle]
  exact ENNReal.ofReal_ne_top

theorem volume_highCell_ne_top (d h : ℝ) (i : Fin 3) :
    volume (highCell d h i) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (show volume stdTriangle.set ≠ ⊤ from ?_)
    (measure_mono Set.inter_subset_left)
  rw [Proofs.Quant.volume_stdTriangle]
  exact ENNReal.ofReal_ne_top

private theorem mem_wedge_div (A B p q t : ℝ) (ht : 0 < t) (x : ℝ × ℝ) :
    x ∈ wedge (A / t) (B / t) p q ↔
      0 ≤ x.1 ∧ 0 ≤ x.2 - p - q * x.1 ∧
        B * x.1 + t * (x.2 - p - q * x.1) ≤ A := by
  have he : B / t * x.1 + (x.2 - p - q * x.1) =
      (B * x.1 + t * (x.2 - p - q * x.1)) / t := by
    field_simp [ht.ne']
  simp only [wedge, mem_ofPred_eq, he, div_le_div_iff_of_pos_right ht]

private theorem volume_wedge_div (A B p q t : ℝ) (ht : 0 < t) (hB : 0 < B) :
    volume (wedge (A / t) (B / t) p q) =
      ENNReal.ofReal ((max 0 A) ^ 2 / (2 * t * B)) := by
  rw [volume_wedge _ _ _ _ (div_pos hB ht)]
  have hm : max 0 (A / t) = max 0 A / t := by
    simpa only [zero_div] using max_div_div_right ht.le 0 A
  rw [hm]
  congr 1
  field_simp [ht.ne', hB.ne']

private theorem lowCell_area_ge_of_levels (d l : ℝ)
    (hd : 0 < d ∧ d < 1) (hl : (2 - d) * l ≤ 1)
    (hL : 0 ≤ (1 + d) * l - d) :
    (((1 + d) * l - d) ^ 2 / (d * (1 - d + d ^ 2)) -
      (max 0 (l - d)) ^ 2 / (d * (1 - d))) / 2 ≤
        (volume (lowCell d l 0)).toReal := by
  let E := 1 - d + d ^ 2
  let L := (1 + d) * l - d
  let R := wedge (L / d) (E / d) (1 - l) (d - 1)
  let K := wedge ((l - d) / d) ((1 - d) / d) 1 (-1)
  have hE : 0 < E := add_pos_of_pos_of_nonneg (sub_pos.mpr hd.2) (sq_nonneg d)
  have hd' : 0 < 1 - d := sub_pos.mpr hd.2
  have hcover : R ⊆ lowCell d l 0 ∪ K := by
    intro x hx
    rcases (mem_wedge_div L E (1 - l) (d - 1) d hd.1 x).mp hx with
      ⟨hx, hlow, hupper⟩
    have hlo : 1 - (1 - d) * x.1 - x.2 ≤ l := by linarith only [hlow]
    have hup : x.1 + d * x.2 ≤ l := by
      dsimp [E, L] at hupper
      nlinarith only [hupper]
    have hy : 0 ≤ x.2 := by
      have hm := mul_le_mul_of_nonneg_left hup hd'.le
      have hEy : 0 ≤ E * x.2 := by
        dsimp [E]
        nlinarith only [hlo, hm, hl]
      exact nonneg_of_mul_nonneg_right hEy hE
    by_cases hT : x.1 + x.2 ≤ 1
    · left
      refine ⟨?_, ?_⟩
      · rw [Proofs.Quant.stdTriangle_set_eq]
        exact ⟨hx, hy, hT⟩
      · change 1 - (1 - d) * x.1 - x.2 ≤ l ∧ x.1 + d * x.2 ≤ l
        exact ⟨hlo, hup⟩
    · right
      apply (mem_wedge_div (l - d) (1 - d) 1 (-1) d hd.1 x).mpr
      exact ⟨hx, by linarith only [hT], by nlinarith only [hup]⟩
  have hR : volume R = ENNReal.ofReal (L ^ 2 / (2 * d * E)) := by
    rw [volume_wedge_div L E (1 - l) (d - 1) d hd.1 hE, max_eq_right hL]
  have hK : volume K =
      ENNReal.ofReal ((max 0 (l - d)) ^ 2 / (2 * d * (1 - d))) :=
    volume_wedge_div (l - d) (1 - d) 1 (-1) d hd.1 hd'
  have hKfin : volume K ≠ ⊤ := by rw [hK]; exact ENNReal.ofReal_ne_top
  have hbound := (measure_mono (μ := volume) hcover).trans (measure_union_le _ _)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨volume_lowCell_ne_top d l 0, hKfin⟩) hbound
  rw [ENNReal.toReal_add (volume_lowCell_ne_top d l 0) hKfin, hR, hK,
    ENNReal.toReal_ofReal (div_nonneg (sq_nonneg L)
      (mul_nonneg (mul_nonneg (by norm_num) hd.1.le) hE.le)),
    ENNReal.toReal_ofReal (div_nonneg (sq_nonneg (max 0 (l - d)))
      (mul_nonneg (mul_nonneg (by norm_num) hd.1.le) hd'.le))]
    at hreal
  change (L ^ 2 / (d * E) - (max 0 (l - d)) ^ 2 / (d * (1 - d))) / 2 ≤ _
  have he : (L ^ 2 / (d * E) - (max 0 (l - d)) ^ 2 / (d * (1 - d))) / 2 =
      L ^ 2 / (2 * d * E) - (max 0 (l - d)) ^ 2 / (2 * d * (1 - d)) := by
    field_simp [hd.1.ne', hd'.ne', hE.ne']
  rw [he]
  linarith only [hreal]

/-- The retained low cell pays its full wedge area minus the possible cap
outside the original triangle. The interval endpoints are included. -/
theorem lowCell_area_ge (d r : ℝ) (hd : 0 < d ∧ d ≤ 1 / 2)
    (hr : 0 ≤ r ∧ r ≤ 1 / 3) :
    let l := (1 + d) / 3 - r / 2
    let E := 1 - d + d ^ 2
    (((1 + d) * l - d) ^ 2 / (d * E) -
      (max 0 (l - d)) ^ 2 / (d * (1 - d))) / 2 ≤
        (volume (lowCell d l 0)).toReal := by
  dsimp only
  have hd1 : d < 1 := by linarith [hd.2]
  have hE : 0 < 1 - d + d ^ 2 :=
    add_pos_of_pos_of_nonneg (sub_pos.mpr hd1) (sq_nonneg d)
  apply lowCell_area_ge_of_levels d _ ⟨hd.1, hd1⟩
  · have hp := mul_nonneg (show 0 ≤ 2 - d by linarith [hd.2]) hr.1
    nlinarith only [hp, hE.le]
  · have hp := mul_nonneg (show 0 ≤ 1 - d by linarith [hd.2])
      (show 0 ≤ 1 - 2 * d by linarith [hd.2])
    have hq := mul_le_mul_of_nonneg_left hr.2 (show 0 ≤ 1 + d by linarith [hd.1])
    nlinarith only [hp, hq]

private theorem highCell_eq_swap_wedge (d h : ℝ)
    (hd : 0 < d ∧ d < 1) (hh : d ≤ h) :
    highCell d h 0 = Proofs.Symmetry.swapMap ⁻¹'
      wedge ((1 - (2 - d) * h) / (1 - d))
        ((1 - d + d ^ 2) / (1 - d)) h (-d) := by
  have hd' : 0 < 1 - d := sub_pos.mpr hd.2
  have hE : 0 < 1 - d + d ^ 2 :=
    add_pos_of_pos_of_nonneg hd' (sq_nonneg d)
  ext x
  rw [Set.mem_preimage, mem_wedge_div _ _ _ _ _ hd']
  change (x ∈ stdTriangle.set ∧
    h ≤ 1 - (1 - d) * x.1 - x.2 ∧ h ≤ x.1 + d * x.2) ↔
    (0 ≤ x.2 ∧ 0 ≤ x.1 - h - -d * x.2 ∧
      (1 - d + d ^ 2) * x.2 + (1 - d) * (x.1 - h - -d * x.2) ≤
        1 - (2 - d) * h)
  constructor
  · rintro ⟨hxT, h0, h1⟩
    rw [Proofs.Quant.stdTriangle_set_eq] at hxT
    exact ⟨hxT.2.1, by linarith only [h1], by nlinarith only [h0]⟩
  · rintro ⟨hy, hlow, hupper⟩
    have h0 : h ≤ 1 - (1 - d) * x.1 - x.2 := by nlinarith only [hupper]
    have h1 : h ≤ x.1 + d * x.2 := by linarith only [hlow]
    refine ⟨?_, h0, h1⟩
    rw [Proofs.Quant.stdTriangle_set_eq]
    have hx : 0 ≤ x.1 := by
      have hm := mul_le_mul_of_nonneg_left h0 hd.1.le
      have hdh := mul_nonneg hd.1.le (hd.1.le.trans hh)
      have hEx : 0 ≤ (1 - d + d ^ 2) * x.1 := by
        nlinarith only [hm, h1, hh, hdh]
      exact nonneg_of_mul_nonneg_right hEx hE
    have hsum : x.1 + x.2 ≤ 1 := by
      have hm := mul_nonneg hd.1.le hy
      have ht : (1 - d) * (x.1 + x.2) ≤ (1 - d) * 1 := by
        nlinarith only [h0, hh, hm]
      exact le_of_mul_le_mul_left ht hd'
    exact ⟨hx, hy, hsum⟩

/-- The high cell is the complete affine wedge. The positive part accounts
for both its empty and degenerate regimes without a position split. -/
theorem volume_highCell (d r : ℝ) (hd : 0 < d ∧ d ≤ 1 / 2)
    (hr : 0 ≤ r ∧ r ≤ 1 / 3) :
    let h := (1 + d) / 3 + r / 2
    let E := 1 - d + d ^ 2
    volume (highCell d h 0) =
      ENNReal.ofReal ((max 0 (1 - (2 - d) * h)) ^ 2 / (2 * (1 - d) * E)) := by
  dsimp only
  have hd1 : d < 1 := by linarith [hd.2]
  have hh : d ≤ (1 + d) / 3 + r / 2 := by linarith [hd.2, hr.1]
  rw [highCell_eq_swap_wedge d _ ⟨hd.1, hd1⟩ hh,
    Proofs.Symmetry.volume_preimage_swapMap]
  exact volume_wedge_div _ _ _ _ _ (sub_pos.mpr hd1)
    (add_pos_of_pos_of_nonneg (sub_pos.mpr hd1) (sq_nonneg d))

/-- The low-cell estimate for a general level. The positive part includes
levels at which the putative low wedge has vanished. -/
theorem lowCell_posPart_area_ge (d l : ℝ) (hd : 0 < d ∧ d < 1)
    (hl : (2 - d) * l ≤ 1) :
    ((max 0 ((1 + d) * l - d)) ^ 2 / (d * (1 - d + d ^ 2)) -
      (max 0 (l - d)) ^ 2 / (d * (1 - d))) / 2 ≤
        (volume (lowCell d l 0)).toReal := by
  by_cases hL : 0 ≤ (1 + d) * l - d
  · rw [max_eq_right hL]
    exact lowCell_area_ge_of_levels d l hd hl hL
  · have hld : l ≤ d := by
      by_contra hn
      have hp := mul_nonneg hd.1.le (hd.1.le.trans (le_of_not_ge hn))
      nlinarith only [hp, lt_of_not_ge hn, le_of_not_ge hL]
    rw [max_eq_left (le_of_not_ge hL), max_eq_left (sub_nonpos.mpr hld)]
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_self] using
      (show 0 ≤ (volume (lowCell d l 0)).toReal from ENNReal.toReal_nonneg)

/-- General high-cell level formula; only the position needed for wedge
containment is assumed, independently of any common window or width. -/
theorem volume_highCell_of_level (d h : ℝ) (hd : 0 < d ∧ d < 1) (hh : d ≤ h) :
    volume (highCell d h 0) =
      ENNReal.ofReal ((max 0 (1 - (2 - d) * h)) ^ 2 /
        (2 * (1 - d) * (1 - d + d ^ 2))) := by
  rw [highCell_eq_swap_wedge d h hd hh, Proofs.Symmetry.volume_preimage_swapMap]
  exact volume_wedge_div _ _ _ _ _ (sub_pos.mpr hd.2)
    (add_pos_of_pos_of_nonneg (sub_pos.mpr hd.2) (sq_nonneg d))

end Quant.CyclicCenteredGeometry
