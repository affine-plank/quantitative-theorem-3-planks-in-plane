/-
# The one-plank calibration: `d(p) ≥ 0`

Port of `Dim2N3/KPlankCalibration.lean` onto the `Plank` vocabulary.
The theorem: **no plank of relative width `w ≤ 1` covers more than
`(2w − w²)·|D|` of the triangle** (`plankDeficit_nonneg`).  The width
hypothesis is necessary: a plank of relative width `> 1` can swallow
all of `D`, and `|D| > |D|(2w − w²)` there.

The proof has three layers.

*The corner areas* (§1–§2).  The area cut off a triangle by a line is
an affine copy of a triangle; instead of the ancestor's per-corner
Fubini computations, one Fubini lemma (`volume_cornerTriangle`, the
area under a linear ceiling) plus affine preimages (translations and
the flip `(x, y) ↦ (x, 1 − x − y)`) give every corner formula.

*The two profiles* (§3–§4).  Sorting the normal's three vertex values
`0, u₁, u₂` leaves two shapes: the **tent** `(a₁, 1)` with
`0 < a₁ < 1`, whose projected CDF `Φ` glues the two corner parabolas at
the peak, and the **ramp** `(1, 0)` (edge-parallel), whose CDF is
`Φₑ(t) = t − t²/2`.  The increment bound `Φ(hi) − Φ(lo) ≤ w − w²/2` is
the analytic heart; in the straddling position it is the keystone
inequality `x²/m + y²/(1−m) ≥ (x+y)²`, and the ramp case's certificate
`lo·(hi − lo) ≥ 0` shows the calibrated ramp placement is flush with
the *edge*, not the opposite vertex.

*The transport* (§5).  Negating or positively rescaling a plank does
not change its set; pulling back along the triangle's rotation and
reflection preserves area by `Proofs.Symmetry`'s charts.  These four
moves sort any normal's vertex values, reducing `d(p) ≥ 0` to the two
profiles (§6).

§7 records the **CAL-w** equality theory: `d(p) = 0` is a genuine
extremal condition, and on the tent family it pins the window
position uniquely (`calibrated_position_tent`).
-/
module

public import Plank.Proofs.Quant.Ledger

@[expose] public section


noncomputable section

open MeasureTheory Set Proofs.Quant Proofs.Symmetry Proofs.Transport Proofs.GapCells

namespace Quant

/-! ## §1  The corner-triangle area, and affine preimages -/

/-- **The area under a linear ceiling**: the triangle
`x, y ≥ 0`, `αx + y ≤ β` has area `β²/(2α)`.  Fubini: the slice at `x`
is the segment `[0, β − αx]`. -/
theorem volume_cornerTriangle {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    volume {P : ℝ × ℝ | 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ α * P.1 + P.2 ≤ β}
      = ENNReal.ofReal (β ^ 2 / (2 * α)) := by
  have hmeas : MeasurableSet {P : ℝ × ℝ | 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ α * P.1 + P.2 ≤ β} := by
    refine ((isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le ((continuous_const.mul continuous_fst).add continuous_snd)
          continuous_const))).measurableSet
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  have hslice : ∀ x : ℝ,
      volume (Prod.mk x ⁻¹' {P : ℝ × ℝ | 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ α * P.1 + P.2 ≤ β})
        = Set.indicator (Set.Icc (0:ℝ) (β / α))
            (fun t => ENNReal.ofReal (β - α * t)) x := by
    intro x
    rcases lt_or_ge x 0 with hx | hx
    · have he : Prod.mk x ⁻¹' {P : ℝ × ℝ | 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ α * P.1 + P.2 ≤ β} = ∅ := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro h; linarith
      have hnot : x ∉ Set.Icc (0:ℝ) (β / α) := by
        simp only [Set.mem_Icc, not_and, not_le]
        intro h; linarith
      rw [he, measure_empty, Set.indicator_of_notMem hnot]
    · have he : Prod.mk x ⁻¹' {P : ℝ × ℝ | 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ α * P.1 + P.2 ≤ β}
          = Set.Icc 0 (β - α * x) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · rintro ⟨-, h1, h2⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨hx, h1, by linarith⟩
      rw [he, Real.volume_Icc]
      rcases le_or_gt x (β / α) with hx1 | hx1
      · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hx, hx1⟩), sub_zero]
      · have hnot : x ∉ Set.Icc (0:ℝ) (β / α) := by
          simp only [Set.mem_Icc, not_and, not_le]
          intro _; linarith
        rw [Set.indicator_of_notMem hnot, sub_zero]
        refine ENNReal.ofReal_eq_zero.mpr ?_
        rw [div_lt_iff₀ hα] at hx1
        nlinarith
  simp only [hslice]
  have hβα : 0 ≤ β / α := div_nonneg hβ hα.le
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous fun t : ℝ => β - α * t).integrableOn_Icc
        (a := 0) (b := β / α))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        simp only [Pi.zero_apply]
        have h2 := ht.2
        rw [le_div_iff₀ hα] at h2
        nlinarith)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hβα,
    intervalIntegral.integral_sub intervalIntegrable_const
      ((intervalIntegral.intervalIntegrable_id).const_mul α),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  have hα' : α ≠ 0 := ne_of_gt hα
  simp only [smul_eq_mul]
  field_simp
  ring

/-- The volume of an affine preimage `P ↦ c + L P` scales by
`|det L|⁻¹`, for every set. -/
theorem volume_affinePreimage {L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)}
    (hL : LinearMap.det L ≠ 0) (c : ℝ × ℝ) (s : Set (ℝ × ℝ)) :
    volume ((fun P => c + L P) ⁻¹' s)
      = ENNReal.ofReal |(LinearMap.det L)⁻¹| * volume s := by
  have h : (fun P : ℝ × ℝ => c + L P) ⁻¹' s = ⇑L ⁻¹' ((fun q : ℝ × ℝ => c + q) ⁻¹' s) := by
    ext P; simp only [Set.mem_preimage]
  rw [h, Measure.addHaar_preimage_linearMap volume hL, measure_preimage_add]

/-- The linear map `(x, y) ↦ (a x + b y, c x + d y)`. -/
def lin2 (a b c d : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun P := (a * P.1 + b * P.2, c * P.1 + d * P.2)
  map_add' P Q := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> ring
  map_smul' r P := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    constructor <;> ring

private theorem det_lin2 (a b c d : ℝ) : LinearMap.det (lin2 a b c d) = a * d - b * c := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, lin2, Module.Basis.finTwoProd]

/-! ## §2  The three corners

Sublevel and superlevel corners of the tent functional `⟪·, (a₁, 1)⟫`,
and the superlevel corner of the edge functional `⟪·, (1, 0)⟫`, each
as an area formula on `stdTriangle`. -/

/-- Below-peak sublevel corner of the tent: for `0 ≤ t ≤ a₁ ≤ 1` the
constraint `x + y ≤ 1` is redundant and the sublevel set *is* a corner
triangle. -/
theorem volume_tent_low {a1 t : ℝ} (ha : 0 < a1) (ha1 : a1 ≤ 1) (ht0 : 0 ≤ t)
    (hta : t ≤ a1) :
    volume {P | P ∈ stdTriangle.set ∧ dot (a1, 1) P ≤ t}
      = ENNReal.ofReal (t ^ 2 / (2 * a1)) := by
  have hset : {P | P ∈ stdTriangle.set ∧ dot (a1, 1) P ≤ t}
      = {P : ℝ × ℝ | 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ a1 * P.1 + P.2 ≤ t} := by
    ext P
    simp only [stdTriangle_set_eq, Set.mem_setOf_eq, dot]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2, ?_⟩, by linarith⟩
      nlinarith
  rw [hset, volume_cornerTriangle ha ht0]

/-- Superlevel corner of the tent: for `a₁ ≤ t ≤ 1` the flip
`(x, y) ↦ (x, 1 − x − y)` carries it to a corner triangle with ceiling
slope `1 − a₁` and height `1 − t`. -/
theorem volume_tent_high {a1 t : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) (hat : a1 ≤ t)
    (ht1 : t ≤ 1) :
    volume {P | P ∈ stdTriangle.set ∧ t ≤ dot (a1, 1) P}
      = ENNReal.ofReal ((1 - t) ^ 2 / (2 * (1 - a1))) := by
  have hdet : LinearMap.det (lin2 1 0 (-1) (-1)) ≠ 0 := by
    rw [det_lin2]; norm_num
  have hset : {P | P ∈ stdTriangle.set ∧ t ≤ dot (a1, 1) P}
      = (fun P => ((0:ℝ), (1:ℝ)) + lin2 1 0 (-1) (-1) P) ⁻¹'
          {P : ℝ × ℝ | 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ (1 - a1) * P.1 + P.2 ≤ 1 - t} := by
    ext P
    simp only [stdTriangle_set_eq, Set.mem_setOf_eq, Set.mem_preimage, lin2, dot,
      LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_add_mk]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨by linarith, by linarith, by nlinarith⟩
    · rintro ⟨h1, h2, h3⟩
      have hx : 0 ≤ P.1 := by linarith
      have hxy : P.1 + P.2 ≤ 1 := by linarith
      refine ⟨⟨hx, ?_, hxy⟩, by nlinarith⟩
      -- `0 ≤ y`: from the transported ceiling, using `a₁ ≤ t`
      nlinarith
  rw [hset, volume_affinePreimage hdet,
    volume_cornerTriangle (by linarith) (by linarith), det_lin2]
  rw [← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- Superlevel corner of the edge functional: for `0 ≤ t ≤ 1`,
translating by `(−t, 0)` gives a corner triangle with unit slope. -/
theorem volume_edge_high {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    volume {P | P ∈ stdTriangle.set ∧ t ≤ dot (1, 0) P}
      = ENNReal.ofReal ((1 - t) ^ 2 / 2) := by
  have hset : {P | P ∈ stdTriangle.set ∧ t ≤ dot (1, 0) P}
      = (fun P : ℝ × ℝ => (-t, 0) + P) ⁻¹'
          {P : ℝ × ℝ | 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ 1 * P.1 + P.2 ≤ 1 - t} := by
    ext P
    simp only [stdTriangle_set_eq, Set.mem_setOf_eq, Set.mem_preimage, dot,
      Prod.fst_add, Prod.snd_add]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by linarith, by linarith, by linarith⟩, by linarith⟩
  rw [hset, measure_preimage_add, volume_cornerTriangle (by norm_num) (by linarith)]
  norm_num

/-! ## §3  The tent profile -/

/-- The **projected CDF** of the triangle along the tent normal
`(a₁, 1)`: the two corner parabolas, glued at the peak `a₁`. -/
def Phi (a1 t : ℝ) : ℝ :=
  if t ≤ a1 then t ^ 2 / (2 * a1) else 1 / 2 - (1 - t) ^ 2 / (2 * (1 - a1))

theorem Phi_zero {a1 : ℝ} (ha : 0 < a1) : Phi a1 0 = 0 := by
  rw [Phi, if_pos ha.le]; norm_num

theorem Phi_one {a1 : ℝ} (ha1 : a1 < 1) : Phi a1 1 = 1 / 2 := by
  rw [Phi, if_neg (by linarith)]; norm_num

theorem Phi_lower {a1 t : ℝ} (h : t ≤ a1) : Phi a1 t = t ^ 2 / (2 * a1) := by
  rw [Phi, if_pos h]

/-- Above the peak `Φ` is the upper-corner formula; at `t = a₁` the two
branches agree, so the formula holds on the closed half. -/
theorem Phi_upper {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) {t : ℝ} (h : a1 ≤ t) :
    Phi a1 t = 1 / 2 - (1 - t) ^ 2 / (2 * (1 - a1)) := by
  rcases eq_or_lt_of_le h with h' | h'
  · rw [Phi, if_pos (by linarith), ← h']
    have h1 : a1 ≠ 0 := ne_of_gt ha
    have h2 : (1:ℝ) - a1 ≠ 0 := by linarith
    field_simp
    ring
  · rw [Phi, if_neg (by linarith)]

/-- The sublevel set of the tent functional inside the triangle. -/
def subLev (a1 t : ℝ) : Set (ℝ × ℝ) :=
  {P | P ∈ stdTriangle.set ∧ dot (a1, 1) P ≤ t}

private theorem subLev_subset (a1 t : ℝ) : subLev a1 t ⊆ stdTriangle.set :=
  fun _ hP => hP.1

private theorem measurableSet_subLev (a1 t : ℝ) : MeasurableSet (subLev a1 t) :=
  measurableSet_stdTriangle.inter
    ((isClosed_le (continuous_dot _) continuous_const).measurableSet)

/-- The tent's level lines are null. -/
private theorem tent_line_null (a1 t : ℝ) :
    volume {P : ℝ × ℝ | dot (a1, 1) P = t} = 0 :=
  volume_line_eq_zero (by simp [Prod.ext_iff]) t

/-- `|{⟪·,(a₁,1)⟫ ≤ t} ∩ D| = Φ(t)` on `0 ≤ t ≤ 1`. -/
theorem area_subLev {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : area (subLev a1 t) = Phi a1 t := by
  rcases le_or_gt t a1 with h | h
  · rw [Phi_lower h, area, subLev, volume_tent_low ha ha1.le ht0 h,
      ENNReal.toReal_ofReal (by positivity)]
  · rw [Phi, if_neg (not_le.mpr h)]
    -- complement: `|{f ≤ t}| + |{t ≤ f}| = |D| + |{f = t}|`, and the level line is null
    have hup : MeasurableSet {P | P ∈ stdTriangle.set ∧ t ≤ dot (a1, 1) P} :=
      measurableSet_stdTriangle.inter
        ((isClosed_le continuous_const (continuous_dot _)).measurableSet)
    have hunion : subLev a1 t ∪ {P | P ∈ stdTriangle.set ∧ t ≤ dot (a1, 1) P}
        = stdTriangle.set := by
      ext P
      simp only [subLev, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (⟨hP, -⟩ | ⟨hP, -⟩) <;> exact hP
      · intro hP
        rcases le_total (dot (a1, 1) P) t with h' | h'
        · exact Or.inl ⟨hP, h'⟩
        · exact Or.inr ⟨hP, h'⟩
    have hinter : volume (subLev a1 t ∩ {P | P ∈ stdTriangle.set ∧ t ≤ dot (a1, 1) P})
        = 0 := by
      refine measure_mono_null ?_ (tent_line_null a1 t)
      rintro P ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
      exact le_antisymm h1 h2
    have hkey := measure_union_add_inter (μ := volume) (subLev a1 t) hup
    rw [hunion, hinter, add_zero, Proofs.Quant.volume_stdTriangle,
      volume_tent_high ha ha1 h.le ht1] at hkey
    have hfin : volume (subLev a1 t) ≠ ⊤ :=
      volume_ne_top_of_subset_std (subLev_subset a1 t)
    have h2 := congrArg ENNReal.toReal hkey
    rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 / 2 by norm_num),
      ENNReal.toReal_ofReal
        (show (0:ℝ) ≤ (1 - t) ^ 2 / (2 * (1 - a1)) from
          div_nonneg (sq_nonneg _) (by linarith))] at h2
    unfold area
    linarith

/-- The band of the tent functional between two levels inside `D`. -/
def calibBand (a1 lo hi : ℝ) : Set (ℝ × ℝ) :=
  {P | P ∈ stdTriangle.set ∧ lo ≤ dot (a1, 1) P ∧ dot (a1, 1) P ≤ hi}

private theorem band_subset (a1 lo hi : ℝ) : calibBand a1 lo hi ⊆ stdTriangle.set :=
  fun _ hP => hP.1

private theorem measurableSet_band (a1 lo hi : ℝ) : MeasurableSet (calibBand a1 lo hi) :=
  measurableSet_stdTriangle.inter
    (((isClosed_le continuous_const (continuous_dot _)).inter
      (isClosed_le (continuous_dot _) continuous_const)).measurableSet)

/-- `|calibBand| = Φ(hi) − Φ(lo)` for a calibBand inside the functional's range. -/
theorem area_band {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) :
    area (calibBand a1 lo hi) = Phi a1 hi - Phi a1 lo := by
  have hunion : subLev a1 lo ∪ calibBand a1 lo hi = subLev a1 hi := by
    ext P
    simp only [subLev, calibBand, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (⟨hP, h'⟩ | ⟨hP, -, h'⟩)
      · exact ⟨hP, by linarith⟩
      · exact ⟨hP, h'⟩
    · rintro ⟨hP, h'⟩
      rcases le_total (dot (a1, 1) P) lo with h'' | h''
      · exact Or.inl ⟨hP, h''⟩
      · exact Or.inr ⟨hP, h'', h'⟩
  have hinter : volume (subLev a1 lo ∩ calibBand a1 lo hi) = 0 := by
    refine measure_mono_null ?_ (tent_line_null a1 lo)
    rintro P ⟨⟨-, h1⟩, ⟨-, h2, -⟩⟩
    exact le_antisymm h1 h2
  have hkey := measure_union_add_inter (μ := volume) (subLev a1 lo)
    (measurableSet_band a1 lo hi)
  rw [hunion, hinter, add_zero] at hkey
  have h1 : volume (subLev a1 lo) ≠ ⊤ :=
    volume_ne_top_of_subset_std (subLev_subset a1 lo)
  have h2 : volume (calibBand a1 lo hi) ≠ ⊤ :=
    volume_ne_top_of_subset_std (band_subset a1 lo hi)
  have h3 := congrArg ENNReal.toReal hkey
  rw [ENNReal.toReal_add h1 h2] at h3
  have e1 : area (subLev a1 hi) = Phi a1 hi := area_subLev ha ha1 (by linarith) hhi
  have e2 : area (subLev a1 lo) = Phi a1 lo := area_subLev ha ha1 hlo (by linarith)
  unfold area at *
  linarith

/-! ## §4  The analytic heart -/

/-- **The keystone identity** `x²/m + y²/(1−m) = (x+y)² + r²/(m(1−m))`
with remainder `r = x − m(x+y)`; hence the keystone inequality. -/
theorem keystone {m : ℝ} (hm : 0 < m) (hm1 : m < 1) (x y : ℝ) :
    x ^ 2 / m + y ^ 2 / (1 - m)
      = (x + y) ^ 2 + (x - m * (x + y)) ^ 2 / (m * (1 - m)) := by
  have h1 : m ≠ 0 := ne_of_gt hm
  have h2 : (1:ℝ) - m ≠ 0 := by linarith
  field_simp
  ring

theorem keystone_le {m : ℝ} (hm : 0 < m) (hm1 : m < 1) (x y : ℝ) :
    (x + y) ^ 2 ≤ x ^ 2 / m + y ^ 2 / (1 - m) := by
  rw [keystone hm hm1]
  have : 0 ≤ (x - m * (x + y)) ^ 2 / (m * (1 - m)) :=
    div_nonneg (sq_nonneg _) (by nlinarith)
  linarith

/-- **The increment bound.**  A calibBand of width `w` inside `[0,1]`
captures at most `w − w²/2` of the tent's mass, in all three positions
relative to the peak. -/
theorem Phi_increment_le {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) {lo hi : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) :
    Phi a1 hi - Phi a1 lo ≤ (hi - lo) - (hi - lo) ^ 2 / 2 := by
  rcases le_or_gt hi a1 with hcase | hcase
  · -- both levels below the peak
    rw [Phi_lower hcase, Phi_lower (by linarith)]
    rw [div_sub_div_same, div_le_iff₀ (by linarith : (0:ℝ) < 2 * a1)]
    nlinarith [sq_nonneg (hi - lo), sq_nonneg lo, mul_nonneg hlo (sub_nonneg.mpr hlohi)]
  rcases le_or_gt lo a1 with hcase' | hcase'
  · -- straddling: the keystone
    rw [Phi_upper ha ha1 (by linarith), Phi_lower hcase']
    have hkey := keystone_le ha ha1 lo (1 - hi)
    have e1 : lo ^ 2 / a1 = 2 * (lo ^ 2 / (2 * a1)) := by field_simp
    have e2 : (1 - hi) ^ 2 / (1 - a1) = 2 * ((1 - hi) ^ 2 / (2 * (1 - a1))) := by
      field_simp
    rw [e1, e2] at hkey
    nlinarith [hkey]
  · -- both levels above the peak
    rw [Phi_upper ha ha1 hcase.le, Phi_upper ha ha1 (by linarith)]
    have hd : (0:ℝ) < 2 * (1 - a1) := by linarith
    rw [show 1 / 2 - (1 - hi) ^ 2 / (2 * (1 - a1)) - (1 / 2 - (1 - lo) ^ 2 / (2 * (1 - a1)))
        = ((1 - lo) ^ 2 - (1 - hi) ^ 2) / (2 * (1 - a1)) by ring,
      div_le_iff₀ hd]
    nlinarith [sq_nonneg (hi - lo), sq_nonneg (1 - hi),
      mul_nonneg (sub_nonneg.mpr hhi) (sub_nonneg.mpr hlohi)]

/-- **The equality case**: a calibBand of positive width attains `w − w²/2`
only at the CAL-w position `lo = a₁(1 − w)`.  In the two off-peak
positions equality forces the calibBand across the peak, a contradiction;
in the straddling position the keystone remainder must vanish. -/
theorem Phi_increment_eq {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) {lo hi : ℝ}
    (hlohi : lo < hi)
    (heq : Phi a1 hi - Phi a1 lo = (hi - lo) - (hi - lo) ^ 2 / 2) :
    lo = a1 * (1 - (hi - lo)) := by
  have hw : 0 < hi - lo := by linarith
  have ha' : (0:ℝ) < 1 - a1 := by linarith
  rcases le_or_gt hi a1 with hcase | hcase
  · exfalso
    rw [Phi_lower hcase, Phi_lower (by linarith)] at heq
    have key : hi ^ 2 - lo ^ 2 = a1 * (2 * (hi - lo) - (hi - lo) ^ 2) := by
      field_simp at heq; linarith
    have hcancel : hi + lo = a1 * (2 - (hi - lo)) := by
      have hfac : (hi - lo) * (hi + lo) = (hi - lo) * (a1 * (2 - (hi - lo))) := by
        nlinarith [key]
      exact mul_left_cancel₀ (ne_of_gt hw) hfac
    nlinarith [mul_pos hw ha']
  rcases le_or_gt lo a1 with hcase' | hcase'
  · rw [Phi_upper ha ha1 (by linarith), Phi_lower hcase'] at heq
    have hsum : lo ^ 2 / a1 + (1 - hi) ^ 2 / (1 - a1) = (lo + (1 - hi)) ^ 2 := by
      have e : lo + (1 - hi) = 1 - (hi - lo) := by ring
      rw [e]
      field_simp at heq ⊢
      nlinarith [heq]
    have hk := keystone ha ha1 lo (1 - hi)
    rw [hsum] at hk
    have hz : (lo - a1 * (lo + (1 - hi))) ^ 2 = 0 := by
      have hpos : 0 < a1 * (1 - a1) := mul_pos ha ha'
      have hrem : (lo - a1 * (lo + (1 - hi))) ^ 2 / (a1 * (1 - a1)) = 0 := by linarith
      field_simp at hrem
      linarith [hrem]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    nlinarith [this]
  · exfalso
    rw [Phi_upper ha ha1 hcase.le, Phi_upper ha ha1 (by linarith)] at heq
    have key : (1 - lo) ^ 2 - (1 - hi) ^ 2
        = (1 - a1) * (2 * (hi - lo) - (hi - lo) ^ 2) := by
      field_simp at heq; linarith
    have hcancel : 2 - lo - hi = (1 - a1) * (2 - (hi - lo)) := by
      have hfac : (hi - lo) * (2 - lo - hi)
          = (hi - lo) * ((1 - a1) * (2 - (hi - lo))) := by nlinarith [key]
      exact mul_left_cancel₀ (ne_of_gt hw) hfac
    nlinarith [mul_pos hw ha]

/-! ## §5  The four moves on a single plank

Negation and positive rescaling do not change the plank's *set*;
pulling back along the triangle's rotation and reflection preserves
areas by the `Proofs.Symmetry` charts.  All four preserve the relative
width, hence the deficit. -/

/-- Reflection `B ↔ C`: swap the normal's coordinates. -/
def swapP (p : Plank) : Plank :=
  ⟨(p.u.2, p.u.1), p.lo, p.hi,
    fun h => p.u_ne_zero (Prod.ext_iff.mpr
      ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩),
    p.lo_le_hi⟩

/-- Rotation `A ↦ B ↦ C ↦ A`: the normal maps by the transpose, the
window shifts by the translation part. -/
def rotP (p : Plank) : Plank :=
  ⟨(p.u.2 - p.u.1, -p.u.1), p.lo - p.u.1, p.hi - p.u.1,
    by
      intro h
      have h1 : p.u.2 - p.u.1 = 0 := congrArg Prod.fst h
      have h2 : -p.u.1 = 0 := congrArg Prod.snd h
      exact p.u_ne_zero (Prod.ext_iff.mpr
        ⟨by simp only [Prod.fst_zero]; linarith,
          by simp only [Prod.snd_zero]; linarith⟩),
    sub_le_sub_right p.lo_le_hi _⟩

/-- Negate the normal, swapping and negating the window. -/
def flipP (p : Plank) : Plank :=
  ⟨-p.u, -p.hi, -p.lo, neg_ne_zero.mpr p.u_ne_zero, neg_le_neg p.lo_le_hi⟩

/-- Rescale the normal and window by a positive factor. -/
def scaleP (c : ℝ) (hc : 0 < c) (p : Plank) : Plank :=
  ⟨c • p.u, c * p.lo, c * p.hi, smul_ne_zero (ne_of_gt hc) p.u_ne_zero,
    mul_le_mul_of_nonneg_left p.lo_le_hi hc.le⟩

private theorem set_flipP (p : Plank) : (flipP p).set = p.set := by
  ext P
  simp only [Plank.set, Membership.mem, flipP, dot, Prod.fst_neg,
    Prod.snd_neg]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

private theorem set_scaleP {c : ℝ} (hc : 0 < c) (p : Plank) :
    (scaleP c hc p).set = p.set := by
  ext P
  simp only [Plank.set, Membership.mem, scaleP, dot, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_of_mul_le_mul_left (by nlinarith) hc, le_of_mul_le_mul_left (by nlinarith) hc⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-- The rotated plank is the pullback of the plank along `rotMap`. -/
private theorem set_rotP (p : Plank) : (rotP p).set = rotMap ⁻¹' p.set := by
  ext P
  show (p.lo - p.u.1 ≤ dot (p.u.2 - p.u.1, -p.u.1) P ∧
        dot (p.u.2 - p.u.1, -p.u.1) P ≤ p.hi - p.u.1)
      ↔ (p.lo ≤ dot p.u (rotMap P) ∧ dot p.u (rotMap P) ≤ p.hi)
  have hd : dot p.u (rotMap P) = dot (p.u.2 - p.u.1, -p.u.1) P + p.u.1 := by
    show p.u.1 * (1 - P.1 - P.2) + p.u.2 * P.1
        = ((p.u.2 - p.u.1) * P.1 + -p.u.1 * P.2) + p.u.1
    ring
  rw [hd]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

private theorem set_swapP (p : Plank) : (swapP p).set = swapMap ⁻¹' p.set := by
  ext P
  show (p.lo ≤ dot (p.u.2, p.u.1) P ∧ dot (p.u.2, p.u.1) P ≤ p.hi)
      ↔ (p.lo ≤ dot p.u (swapMap P) ∧ dot p.u (swapMap P) ≤ p.hi)
  have hd : dot p.u (swapMap P) = dot (p.u.2, p.u.1) P := by
    show p.u.1 * P.2 + p.u.2 * P.1 = p.u.2 * P.1 + p.u.1 * P.2
    ring
  rw [hd]

private theorem relWidth_swapP (p : Plank) :
    (swapP p).relWidth stdTriangle = p.relWidth stdTriangle := by
  show (p.hi - p.lo) / stdTriangle.width (p.u.2, p.u.1)
      = (p.hi - p.lo) / stdTriangle.width p.u
  rw [width_swap]

private theorem relWidth_rotP (p : Plank) :
    (rotP p).relWidth stdTriangle = p.relWidth stdTriangle := by
  show (p.hi - p.u.1 - (p.lo - p.u.1)) / stdTriangle.width (p.u.2 - p.u.1, -p.u.1)
      = (p.hi - p.lo) / stdTriangle.width p.u
  rw [width_rot]
  ring_nf

private theorem relWidth_flipP (p : Plank) :
    (flipP p).relWidth stdTriangle = p.relWidth stdTriangle := by
  show (-p.lo - -p.hi) / stdTriangle.width (-p.u)
      = (p.hi - p.lo) / stdTriangle.width p.u
  rw [width_neg]
  ring_nf

private theorem relWidth_scaleP {c : ℝ} (hc : 0 < c) (p : Plank) :
    (scaleP c hc p).relWidth stdTriangle = p.relWidth stdTriangle := by
  show (c * p.hi - c * p.lo) / stdTriangle.width (c • p.u)
      = (p.hi - p.lo) / stdTriangle.width p.u
  rw [width_smul, abs_of_pos hc,
    show c * p.hi - c * p.lo = c * (p.hi - p.lo) by ring,
    mul_div_mul_left _ _ (ne_of_gt hc)]

private theorem plankCap_flipP (p : Plank) : plankCap (flipP p) = plankCap p := by
  simp only [plankCap, set_flipP]

private theorem plankCap_scaleP {c : ℝ} (hc : 0 < c) (p : Plank) :
    plankCap (scaleP c hc p) = plankCap p := by
  simp only [plankCap, set_scaleP hc]

private theorem plankCap_rotP (p : Plank) : plankCap (rotP p) = plankCap p := by
  simp only [plankCap, set_rotP]
  have hpre : rotMap ⁻¹' p.set ∩ stdTriangle.set
      = rotMap ⁻¹' (p.set ∩ stdTriangle.set) := by
    ext P
    simp only [Set.mem_inter_iff, Set.mem_preimage, Triangle.set, Set.mem_setOf_eq]
    have h := rotMap_mem_iff P
    tauto
  rw [hpre]
  simp only [area]
  rw [volume_preimage_rotMap]

private theorem plankCap_swapP (p : Plank) : plankCap (swapP p) = plankCap p := by
  simp only [plankCap, set_swapP]
  have hpre : swapMap ⁻¹' p.set ∩ stdTriangle.set
      = swapMap ⁻¹' (p.set ∩ stdTriangle.set) := by
    ext P
    simp only [Set.mem_inter_iff, Set.mem_preimage, Triangle.set, Set.mem_setOf_eq]
    have h := swapMap_mem_iff P
    tauto
  rw [hpre]
  simp only [area]
  rw [volume_preimage_swapMap]

private theorem plankDeficit_swapP (p : Plank) :
    plankDeficit (swapP p) = plankDeficit p := by
  rw [plankDeficit, plankDeficit, plankCap_swapP, relWidth_swapP]

private theorem plankDeficit_rotP (p : Plank) :
    plankDeficit (rotP p) = plankDeficit p := by
  rw [plankDeficit, plankDeficit, plankCap_rotP, relWidth_rotP]

private theorem plankDeficit_flipP (p : Plank) :
    plankDeficit (flipP p) = plankDeficit p := by
  rw [plankDeficit, plankDeficit, plankCap_flipP, relWidth_flipP]

private theorem plankDeficit_scaleP {c : ℝ} (hc : 0 < c) (p : Plank) :
    plankDeficit (scaleP c hc p) = plankDeficit p := by
  rw [plankDeficit, plankDeficit, plankCap_scaleP, relWidth_scaleP]

/-! ## §6  The two profiles close, and the sectors sort -/

/-- The tent normal has unit width. -/
theorem width_tent {a1 : ℝ} (ha0 : 0 ≤ a1) (ha1 : a1 ≤ 1) :
    stdTriangle.width ((a1 : ℝ), (1 : ℝ)) = 1 := by
  rw [stdTriangle_width_eq]
  show max 0 (max a1 1) - min 0 (min a1 1) = 1
  rw [max_eq_right ha1, max_eq_right (by norm_num : (0:ℝ) ≤ 1), min_eq_left ha1,
    min_eq_left ha0]
  ring

/-- The edge normal has unit width. -/
theorem width_edge : stdTriangle.width ((1 : ℝ), (0 : ℝ)) = 1 := by
  rw [stdTriangle_width_eq]
  show max 0 (max 1 0) - min 0 (min 1 0) = 1
  norm_num

/-- The plank's cap is the *clipped* calibBand: levels outside `[0, 1]`
never meet the triangle, for the tent normal. -/
private theorem cap_eq_band_tent {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) (p : Plank)
    (hu : p.u = ((a1 : ℝ), (1 : ℝ))) :
    p.set ∩ stdTriangle.set = calibBand a1 (max p.lo 0) (min p.hi 1) := by
  ext P
  simp only [Plank.set, Membership.mem, calibBand, hu, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, hP⟩
    have hrange : 0 ≤ dot (a1, 1) P ∧ dot (a1, 1) P ≤ 1 := by
      have hP' := hP
      rw [stdTriangle_set_eq] at hP'
      obtain ⟨hx, hy, hxy⟩ := hP'
      constructor <;> simp only [dot] <;> nlinarith
    exact ⟨hP, ⟨h1, hrange.1⟩, h2, hrange.2⟩
  · rintro ⟨hP, ⟨h1, -⟩, h2, -⟩
    exact ⟨⟨h1, h2⟩, hP⟩

/-- **The tent case.** -/
private theorem plankDeficit_nonneg_tent {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1)
    (p : Plank) (hu : p.u = ((a1 : ℝ), (1 : ℝ)))
    (hw : p.relWidth stdTriangle ≤ 1) : 0 ≤ plankDeficit p := by
  have hwidth : p.relWidth stdTriangle = p.hi - p.lo := by
    rw [Plank.relWidth, hu, width_tent ha.le ha1.le, div_one]
  rw [plankDeficit, hwidth, plankCap, cap_eq_band_tent ha ha1 p hu]
  rw [hwidth] at hw
  set lo' := max p.lo 0 with hlo'
  set hi' := min p.hi 1 with hhi'
  have hlo'le : p.lo ≤ lo' := le_max_left _ _
  have hhi'le : hi' ≤ p.hi := min_le_left _ _
  rcases le_or_gt lo' hi' with hle | hlt
  · have hlo0 : 0 ≤ lo' := le_max_right _ _
    have hhi1 : hi' ≤ 1 := min_le_right _ _
    have hbound := area_band ha ha1 hlo0 hle hhi1
    have hinc := Phi_increment_le ha ha1 hlo0 hle hhi1
    have hmono : (hi' - lo') - (hi' - lo') ^ 2 / 2
        ≤ (p.hi - p.lo) - (p.hi - p.lo) ^ 2 / 2 := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (p.hi - p.lo) - (hi' - lo') by linarith)
        (show (0:ℝ) ≤ 2 - (hi' - lo') - (p.hi - p.lo) by linarith)]
    rw [hbound]
    linarith
  · -- the clipped calibBand is empty
    have hempty : calibBand a1 lo' hi' = ∅ := by
      ext P
      simp only [calibBand, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h1 h2
      linarith
    rw [hempty, area, measure_empty, ENNReal.toReal_zero]
    have hlolehi := p.lo_le_hi
    nlinarith

/-- **The ramp case** `u = (1, 0)`: the edge-parallel profile
`Φₑ(t) = t − t²/2`, whose increment bound has certificate
`lo·w ≥ 0` — the calibrated ramp hugs the edge `x = 0`. -/
private theorem plankDeficit_nonneg_edge (p : Plank)
    (hu : p.u = ((1 : ℝ), (0 : ℝ))) (hw : p.relWidth stdTriangle ≤ 1) :
    0 ≤ plankDeficit p := by
  have hwidth : p.relWidth stdTriangle = p.hi - p.lo := by
    rw [Plank.relWidth, hu, width_edge, div_one]
  -- the edge sublevel area, by the same complement bookkeeping
  have harea : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      area {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ t} = t - t ^ 2 / 2 := by
    intro t ht0 ht1
    have hup : MeasurableSet {P | P ∈ stdTriangle.set ∧ t ≤ dot ((1:ℝ), (0:ℝ)) P} :=
      measurableSet_stdTriangle.inter
        ((isClosed_le continuous_const (continuous_dot _)).measurableSet)
    have hlow : {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ t}
        ⊆ stdTriangle.set := fun _ hP => hP.1
    have hunion : {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ t}
        ∪ {P | P ∈ stdTriangle.set ∧ t ≤ dot ((1:ℝ), (0:ℝ)) P} = stdTriangle.set := by
      ext P
      simp only [Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro (⟨hP, -⟩ | ⟨hP, -⟩) <;> exact hP
      · intro hP
        rcases le_total (dot ((1:ℝ), (0:ℝ)) P) t with h' | h'
        · exact Or.inl ⟨hP, h'⟩
        · exact Or.inr ⟨hP, h'⟩
    have hline : volume {P : ℝ × ℝ | dot ((1:ℝ), (0:ℝ)) P = t} = 0 :=
      volume_line_eq_zero (by simp [Prod.ext_iff]) t
    have hinter : volume ({P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ t}
        ∩ {P | P ∈ stdTriangle.set ∧ t ≤ dot ((1:ℝ), (0:ℝ)) P}) = 0 := by
      refine measure_mono_null ?_ hline
      rintro P ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
      exact le_antisymm h1 h2
    have hkey := measure_union_add_inter (μ := volume)
      {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ t} hup
    rw [hunion, hinter, add_zero, Proofs.Quant.volume_stdTriangle,
      volume_edge_high ht0 ht1] at hkey
    have hfin : volume {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ t} ≠ ⊤ :=
      volume_ne_top_of_subset_std hlow
    have h2 := congrArg ENNReal.toReal hkey
    rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (show (0:ℝ) ≤ 1 / 2 by norm_num),
      ENNReal.toReal_ofReal (show (0:ℝ) ≤ (1 - t) ^ 2 / 2 from
        div_nonneg (sq_nonneg _) (by norm_num))] at h2
    unfold area
    nlinarith [h2]
  -- clip the window and run the increment bound for the ramp
  have hcap : p.set ∩ stdTriangle.set
      = {P | P ∈ stdTriangle.set ∧ max p.lo 0 ≤ dot ((1:ℝ), (0:ℝ)) P ∧
          dot ((1:ℝ), (0:ℝ)) P ≤ min p.hi 1} := by
    ext P
    simp only [Plank.set, Membership.mem, hu, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, hP⟩
      have hrange : 0 ≤ dot ((1:ℝ), (0:ℝ)) P ∧ dot ((1:ℝ), (0:ℝ)) P ≤ 1 := by
        have hP' := hP
        rw [stdTriangle_set_eq] at hP'
        obtain ⟨hx, hy, hxy⟩ := hP'
        constructor <;> simp only [dot] <;> nlinarith
      exact ⟨hP, ⟨h1, hrange.1⟩, h2, hrange.2⟩
    · rintro ⟨hP, ⟨h1, -⟩, h2, -⟩
      exact ⟨⟨h1, h2⟩, hP⟩
  rw [plankDeficit, hwidth, plankCap, hcap]
  rw [hwidth] at hw
  set lo' := max p.lo 0 with hlo'
  set hi' := min p.hi 1 with hhi'
  have hlo'le : p.lo ≤ lo' := le_max_left _ _
  have hhi'le : hi' ≤ p.hi := min_le_left _ _
  rcases le_or_gt lo' hi' with hle | hlt
  · have hlo0 : 0 ≤ lo' := le_max_right _ _
    have hhi1 : hi' ≤ 1 := min_le_right _ _
    -- the calibBand area is the CDF increment
    have hband : area {P | P ∈ stdTriangle.set ∧ lo' ≤ dot ((1:ℝ), (0:ℝ)) P ∧
        dot ((1:ℝ), (0:ℝ)) P ≤ hi'}
        = (hi' - hi' ^ 2 / 2) - (lo' - lo' ^ 2 / 2) := by
      have hunion : {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ lo'}
          ∪ {P | P ∈ stdTriangle.set ∧ lo' ≤ dot ((1:ℝ), (0:ℝ)) P ∧
              dot ((1:ℝ), (0:ℝ)) P ≤ hi'}
          = {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ hi'} := by
        ext P
        simp only [Set.mem_union, Set.mem_setOf_eq]
        constructor
        · rintro (⟨hP, h'⟩ | ⟨hP, -, h'⟩)
          · exact ⟨hP, by linarith⟩
          · exact ⟨hP, h'⟩
        · rintro ⟨hP, h'⟩
          rcases le_total (dot ((1:ℝ), (0:ℝ)) P) lo' with h'' | h''
          · exact Or.inl ⟨hP, h''⟩
          · exact Or.inr ⟨hP, h'', h'⟩
      have hline : volume {P : ℝ × ℝ | dot ((1:ℝ), (0:ℝ)) P = lo'} = 0 :=
        volume_line_eq_zero (by simp [Prod.ext_iff]) lo'
      have hinter : volume ({P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ lo'}
          ∩ {P | P ∈ stdTriangle.set ∧ lo' ≤ dot ((1:ℝ), (0:ℝ)) P ∧
              dot ((1:ℝ), (0:ℝ)) P ≤ hi'}) = 0 := by
        refine measure_mono_null ?_ hline
        rintro P ⟨⟨-, h1⟩, ⟨-, h2, -⟩⟩
        exact le_antisymm h1 h2
      have hbm : MeasurableSet {P | P ∈ stdTriangle.set ∧ lo' ≤ dot ((1:ℝ), (0:ℝ)) P ∧
          dot ((1:ℝ), (0:ℝ)) P ≤ hi'} :=
        measurableSet_stdTriangle.inter
          (((isClosed_le continuous_const (continuous_dot _)).inter
            (isClosed_le (continuous_dot _) continuous_const)).measurableSet)
      have hkey := measure_union_add_inter (μ := volume)
        {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ lo'} hbm
      rw [hunion, hinter, add_zero] at hkey
      have h1 : volume {P | P ∈ stdTriangle.set ∧ dot ((1:ℝ), (0:ℝ)) P ≤ lo'} ≠ ⊤ :=
        volume_ne_top_of_subset_std (fun _ hP => hP.1)
      have h2 : volume {P | P ∈ stdTriangle.set ∧ lo' ≤ dot ((1:ℝ), (0:ℝ)) P ∧
          dot ((1:ℝ), (0:ℝ)) P ≤ hi'} ≠ ⊤ :=
        volume_ne_top_of_subset_std (fun _ hP => hP.1)
      have h3 := congrArg ENNReal.toReal hkey
      rw [ENNReal.toReal_add h1 h2] at h3
      have e1 := harea hi' (by linarith) hhi1
      have e2 := harea lo' hlo0 (by linarith)
      unfold area at *
      linarith
    rw [hband]
    -- the ramp increment bound, with the monotone extension to the unclipped width
    have hinc : (hi' - hi' ^ 2 / 2) - (lo' - lo' ^ 2 / 2)
        ≤ (hi' - lo') - (hi' - lo') ^ 2 / 2 := by
      nlinarith [mul_nonneg hlo0 (sub_nonneg.mpr hle)]
    have hmono : (hi' - lo') - (hi' - lo') ^ 2 / 2
        ≤ (p.hi - p.lo) - (p.hi - p.lo) ^ 2 / 2 := by
      nlinarith [mul_nonneg (show (0:ℝ) ≤ (p.hi - p.lo) - (hi' - lo') by linarith)
        (show (0:ℝ) ≤ 2 - (hi' - lo') - (p.hi - p.lo) by linarith)]
    linarith
  · have hempty : {P | P ∈ stdTriangle.set ∧ lo' ≤ dot ((1:ℝ), (0:ℝ)) P ∧
        dot ((1:ℝ), (0:ℝ)) P ≤ min p.hi 1} = ∅ := by
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h1 h2
      simp only [hhi'] at hlt
      linarith
    rw [hempty, area, measure_empty, ENNReal.toReal_zero]
    have hlolehi := p.lo_le_hi
    nlinarith

/-- The transported property: every plank with this normal and
relative width `≤ 1` has nonnegative deficit. -/
def OK (n : ℝ × ℝ) : Prop :=
  ∀ p : Plank, p.u = n → p.relWidth stdTriangle ≤ 1 → 0 ≤ plankDeficit p

private theorem OK_of_swap {n : ℝ × ℝ} (H : OK (n.2, n.1)) : OK n := by
  intro p hpu hw
  rw [← plankDeficit_swapP]
  exact H (swapP p) (by simp only [swapP, hpu]) (by rwa [relWidth_swapP])

private theorem OK_of_rot {n : ℝ × ℝ} (H : OK (n.2 - n.1, -n.1)) : OK n := by
  intro p hpu hw
  rw [← plankDeficit_rotP]
  exact H (rotP p) (by simp only [rotP, hpu]) (by rwa [relWidth_rotP])

private theorem OK_of_flip {n : ℝ × ℝ} (H : OK (-n)) : OK n := by
  intro p hpu hw
  rw [← plankDeficit_flipP]
  exact H (flipP p) (by simp only [flipP, hpu]) (by rwa [relWidth_flipP])

private theorem OK_of_scale {n : ℝ × ℝ} {c : ℝ} (hc : 0 < c) (H : OK (c • n)) :
    OK n := by
  intro p hpu hw
  rw [← plankDeficit_scaleP hc]
  exact H (scaleP c hc p) (by simp only [scaleP, hpu]) (by rwa [relWidth_scaleP])

private theorem OK_tent {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) :
    OK ((a1 : ℝ), (1 : ℝ)) :=
  fun p hpu hw => plankDeficit_nonneg_tent ha ha1 p hpu hw

private theorem OK_edge : OK ((1 : ℝ), (0 : ℝ)) :=
  fun p hpu hw => plankDeficit_nonneg_edge p hpu hw

/-- The sorted non-degenerate sector `0 < a < b` rescales to the tent. -/
private theorem OK_sorted {a b : ℝ} (ha : 0 < a) (hab : a < b) : OK ((a : ℝ), (b : ℝ)) := by
  have hb : 0 < b := ha.trans hab
  refine OK_of_scale (c := b⁻¹) (by positivity) ?_
  have he : b⁻¹ • ((a : ℝ), (b : ℝ)) = ((b⁻¹ * a : ℝ), (1 : ℝ)) := by
    rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, inv_mul_cancel₀ hb.ne']
  rw [he]
  exact OK_tent (by positivity) (by rw [inv_mul_eq_div, div_lt_one hb]; exact hab)

/-- Every normal with vanishing second coordinate is edge-parallel. -/
private theorem OK_snd_zero {a : ℝ} (ha : a ≠ 0) : OK ((a : ℝ), (0 : ℝ)) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · refine OK_of_flip ?_
    have hna : (0:ℝ) < -a := by linarith
    refine OK_of_scale (c := (-a)⁻¹) (inv_pos.mpr hna) ?_
    have he : (-a)⁻¹ • -((a : ℝ), (0 : ℝ)) = ((1 : ℝ), (0 : ℝ)) := by
      rw [Prod.neg_mk, Prod.smul_mk, smul_eq_mul, smul_eq_mul, neg_zero, mul_zero,
        inv_mul_cancel₀ (ne_of_gt hna)]
    rw [he]
    exact OK_edge
  · refine OK_of_scale (c := a⁻¹) (by positivity) ?_
    have he : a⁻¹ • ((a : ℝ), (0 : ℝ)) = ((1 : ℝ), (0 : ℝ)) := by
      rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_zero,
        inv_mul_cancel₀ (ne_of_gt hpos)]
    rw [he]
    exact OK_edge

/-- **`d(p) ≥ 0`.**  For every plank of relative width at most `1`, the
one-plank deficit is nonnegative: no placement covers more than the
calibrated maximum `(2w − w²)·|D|`. -/
theorem plankDeficit_nonneg (p : Plank) (hw : p.relWidth stdTriangle ≤ 1) :
    0 ≤ plankDeficit p := by
  suffices H : ∀ a b : ℝ, ¬(a = 0 ∧ b = 0) → OK ((a : ℝ), (b : ℝ)) by
    have hne : ¬(p.u.1 = 0 ∧ p.u.2 = 0) := by
      rintro ⟨h1, h2⟩
      exact p.u_ne_zero (Prod.ext_iff.mpr ⟨h1, h2⟩)
    exact H p.u.1 p.u.2 hne p rfl hw
  intro a b hab
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    exact OK_snd_zero (fun h => hab ⟨h, rfl⟩)
  rcases eq_or_ne a 0 with hazero | ha
  · -- `(0, b)`: swap to `(b, 0)`
    subst hazero
    exact OK_of_swap (OK_snd_zero hb)
  rcases eq_or_ne a b with hEq | hne
  · -- `a = b`: rotate–reflect to `(−a, 0)`
    subst hEq
    refine OK_of_rot (OK_of_swap ?_)
    simp only [sub_self]
    exact OK_snd_zero (neg_ne_zero.mpr ha)
  -- six sectors on the strict ordering of `0, a, b`
  rcases lt_or_gt_of_ne ha with ha' | ha'
  · rcases lt_or_gt_of_ne hb with hb' | hb'
    · -- `a, b < 0`: negate into the positive quadrant
      refine OK_of_flip ?_
      rw [Prod.neg_mk]
      rcases lt_or_gt_of_ne (fun h : -a = -b => hne (by linarith)) with h | h
      · exact OK_sorted (by linarith) h
      · exact OK_of_swap (OK_sorted (by linarith) h)
    · -- `a < 0 < b`: rotate–reflect to `(−a, b − a)`, already sorted
      exact OK_of_rot (OK_of_swap
        (OK_sorted (by linarith : (0:ℝ) < -a) (by linarith : -a < b - a)))
  · rcases lt_or_gt_of_ne hb with hb' | hb'
    · -- `b < 0 < a`: swap, then the previous sector
      exact OK_of_swap (OK_of_rot (OK_of_swap
        (OK_sorted (by linarith : (0:ℝ) < -b) (by linarith : -b < a - b))))
    · -- `0 < a, b`, distinct: sort by a swap if needed
      rcases lt_or_gt_of_ne hne with h | h
      · exact OK_sorted ha' h
      · exact OK_of_swap (OK_sorted hb' h)

/-- The `Config`-indexed form consumed by the residue analysis. -/
theorem dDef_nonneg (C : Config) (i : Fin 3) (hw : C.relW i ≤ 1) :
    0 ≤ dDef C i := by
  rw [dDef_eq]
  exact plankDeficit_nonneg (C.plank i) hw

/-- The one-plank square bound: a plank of relative width `w ≤ 1`
leaves at least `(1 − w)²·|D|` of the triangle uncovered. -/
theorem plankGap_ge (p : Plank) (hw : p.relWidth stdTriangle ≤ 1) :
    (1 - p.relWidth stdTriangle) ^ 2 * (1 / 2) ≤ plankGap p :=
  (ledger1_nonneg_iff p).mpr (plankDeficit_nonneg p hw)

/-! ## §7  CAL-w: the own-optimum calibration

`Calibrated p` says the plank sits at its *own* single-plank optimum
(`d(p) = 0`).  This is CAL-w, not the total-deficit calibration CAL-δ
(`lo = m·δ` with `δ = 1 − Σw`); the two coincide only at `k = 1`.  On
the tent family the calibrated position is unique. -/

/-- A plank is **CAL-w calibrated** when its single deficit vanishes. -/
def Calibrated (p : Plank) : Prop := plankDeficit p = 0

/-- Calibration says the coverage attains the calibrated maximum. -/
theorem calibrated_iff_coverage (p : Plank) :
    Calibrated p
      ↔ plankCap p
          = 1 / 2 * (2 * p.relWidth stdTriangle - p.relWidth stdTriangle ^ 2) := by
  unfold Calibrated plankDeficit
  constructor <;> intro h <;> linarith

/-- Equivalently, the one-plank gap attains `(1 − w)²·|D|`. -/
theorem calibrated_iff_gap (p : Plank) :
    Calibrated p ↔ plankGap p = (1 - p.relWidth stdTriangle) ^ 2 * (1 / 2) := by
  have h := ledger1 p
  unfold Calibrated
  constructor <;> intro hyp <;> linarith

/-- For width `≤ 1` calibration is exactly the minimum of the deficit. -/
theorem calibrated_iff_le_zero (p : Plank) (hw : p.relWidth stdTriangle ≤ 1) :
    Calibrated p ↔ plankDeficit p ≤ 0 := by
  have h := plankDeficit_nonneg p hw
  unfold Calibrated
  constructor <;> intro hyp <;> linarith

/-- **The positionless lemma.**  On the tent family a plank of positive
relative width is calibrated **iff** it sits at the unique CAL-w
position; in particular `d(p) = 0` pins the window inside the range and
determines `lo` outright. -/
theorem calibrated_position_tent {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) (p : Plank)
    (hu : p.u = ((a1 : ℝ), (1 : ℝ))) (hlohi : p.lo < p.hi) (hw : p.hi - p.lo ≤ 1)
    (hcal : Calibrated p) :
    0 ≤ p.lo ∧ p.hi ≤ 1 ∧ p.lo = a1 * (1 - (p.hi - p.lo)) := by
  have hwidth : p.relWidth stdTriangle = p.hi - p.lo := by
    rw [Plank.relWidth, hu, width_tent ha.le ha1.le, div_one]
  have hwpos : 0 < p.hi - p.lo := by linarith
  have hcov : plankCap p = (p.hi - p.lo) - (p.hi - p.lo) ^ 2 / 2 := by
    have h := (calibrated_iff_coverage p).mp hcal
    rw [hwidth] at h
    linarith
  rw [plankCap, cap_eq_band_tent ha ha1 p hu] at hcov
  set lo' := max p.lo 0 with hlo'
  set hi' := min p.hi 1 with hhi'
  have hlo'le : p.lo ≤ lo' := le_max_left _ _
  have hhi'le : hi' ≤ p.hi := min_le_left _ _
  have hlo0 : 0 ≤ lo' := le_max_right _ _
  have hhi1 : hi' ≤ 1 := min_le_right _ _
  -- the clipped calibBand cannot be empty
  have hle : lo' ≤ hi' := by
    by_contra hcon
    push_neg at hcon
    have hempty : calibBand a1 lo' hi' = ∅ := by
      ext P
      simp only [calibBand, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ h1 h2
      linarith
    rw [hempty, area, measure_empty, ENNReal.toReal_zero] at hcov
    nlinarith [hcov]
  have hbound := area_band ha ha1 hlo0 hle hhi1
  have hinc := Phi_increment_le ha ha1 hlo0 hle hhi1
  rw [hbound] at hcov
  -- no clipping happened: the clipped width matches the original
  have hwidth' : hi' - lo' = p.hi - p.lo := by
    by_contra hcon
    have hlt : hi' - lo' < p.hi - p.lo := lt_of_le_of_ne (by linarith) hcon
    have h1 : hi' - lo' < 1 := by linarith
    nlinarith [hinc, hcov]
  have hlo_eq : lo' = p.lo := by linarith
  have hhi_eq : hi' = p.hi := by linarith
  refine ⟨by linarith, by linarith, ?_⟩
  rw [hlo_eq, hhi_eq] at hcov
  exact Phi_increment_eq ha ha1 hlohi hcov

/-- The converse: the CAL-w position really is calibrated. -/
theorem calibrated_of_position_tent {a1 : ℝ} (ha : 0 < a1) (ha1 : a1 < 1) (p : Plank)
    (hu : p.u = ((a1 : ℝ), (1 : ℝ))) (hw : p.hi - p.lo ≤ 1)
    (hpos : p.lo = a1 * (1 - (p.hi - p.lo))) : Calibrated p := by
  have hwidth : p.relWidth stdTriangle = p.hi - p.lo := by
    rw [Plank.relWidth, hu, width_tent ha.le ha1.le, div_one]
  have ha' : (0:ℝ) < 1 - a1 := by linarith
  have hlohi := p.lo_le_hi
  have hwpos : 0 ≤ p.hi - p.lo := by linarith
  have hlo0 : 0 ≤ p.lo := by rw [hpos]; nlinarith
  have hhi1 : p.hi ≤ 1 := by nlinarith [hpos]
  have hloa : p.lo ≤ a1 := by rw [hpos]; nlinarith
  have hahi : a1 ≤ p.hi := by nlinarith [hpos]
  -- the keystone remainder vanishes at this position
  have hk := keystone ha ha1 p.lo (1 - p.hi)
  have hz : (p.lo - a1 * (p.lo + (1 - p.hi))) ^ 2 = 0 := by
    have e : p.lo + (1 - p.hi) = 1 - (p.hi - p.lo) := by ring
    rw [e, ← hpos]
    ring
  rw [hz, zero_div, add_zero] at hk
  have hinc : Phi a1 p.hi - Phi a1 p.lo = (p.hi - p.lo) - (p.hi - p.lo) ^ 2 / 2 := by
    rw [Phi_upper ha ha1 hahi, Phi_lower hloa]
    have e : p.lo + (1 - p.hi) = 1 - (p.hi - p.lo) := by ring
    rw [e] at hk
    field_simp at hk ⊢
    nlinarith [hk]
  rw [calibrated_iff_coverage, hwidth, plankCap, cap_eq_band_tent ha ha1 p hu,
    show max p.lo 0 = p.lo from max_eq_left hlo0,
    show min p.hi 1 = p.hi from min_eq_left hhi1,
    area_band ha ha1 hlo0 hlohi hhi1, hinc]
  ring

end Quant

end
