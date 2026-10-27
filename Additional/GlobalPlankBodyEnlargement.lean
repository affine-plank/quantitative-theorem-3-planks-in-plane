/- A global quantitative minimum controls every convex enlargement.
Widths may increase: the resulting budget decrease only strengthens the bound. -/
module

public import GlobalPlankBodyMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalPlankBodyEnlargement

open Set MeasureTheory PrunedPlankCounterexample
open GlobalPlankBodyMinimum (IsGlobalMinimum)

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

omit [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
theorem width_mono {K C : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hC : IsCompact C) (hKC : K⊆C) (f : E →ᵃ[ℝ] ℝ) :
    Body.width K f≤Body.width C f := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne f.continuous_of_finiteDimensional
  rw [Body.width_eq_of_realisers ha hb hmax hmin]
  exact Body.sub_le_width hC f.continuous_of_finiteDimensional (hKC ha) (hKC hb)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Enlarging the body decreases every nonnegative relative plank width. -/
theorem budget_antitone {K C : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hC : IsCompact C) (hKC : K⊆C) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i, lo i≤hi i) (hW : ∀ i, 0<Body.width K (f i)) :
    budget C f lo hi≤budget K f lo hi := by
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr (horder i)) (hW i)
    (width_mono hK hne hC hKC (f i))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Exact volume of the newly uncovered region, with no boundary regularity. -/
theorem added_gap (μ : Measure E) {K C U : Set E} (hC : μ C≠⊤)
    (hK : MeasurableSet K) (hU : MeasurableSet U) (hKC : K⊆C) :
    μ.real ((C\K)\U)=μ.real (C\U)-μ.real (K\U) := by
  have he : (C\K)\U=(C\U)\(K\U) := by
    ext x
    simp only [mem_sdiff]
    tauto
  rw [he]
  exact measureReal_sdiff (sdiff_subset_sdiff_left hKC) (hK.diff hU)
    (measure_ne_top_of_subset sdiff_subset hC)

private theorem measurable_covered (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    MeasurableSet (covered f lo hi) := by
  apply MeasurableSet.iUnion
  intro i
  exact ((isClosed_le continuous_const (f i).continuous_of_finiteDimensional).inter
    (isClosed_le (f i).continuous_of_finiteDimensional continuous_const)).measurableSet

/-- A necessary lower bound on the uncovered volume added by ANY compact
convex enlargement. The extra deficit-power term records the favorable
budget decrease. Neither width preservation, negative margin, positive gap,
nor an upper bound on B is assumed. -/
theorem added_gap_ge_with_budget (μ : Measure E) [μ.IsAddHaarMeasure]
    {K C : Set E} (hK : IsCompact K) (hV : 0<μ.real K)
    (hC : IsCompact C) (hCc : Convex ℝ C) (hKC : K⊆C)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i, lo i≤hi i) (hW : ∀ i, 0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B) :
    μ.real (K\covered f lo hi)/μ.real K*μ.real (C\K)+
        μ.real C*((B-budget C f lo hi)^d-(B-budget K f lo hi)^d)≤
      μ.real ((C\K)\covered f lo hi) := by
  have hne : K.Nonempty := by
    by_contra h
    simp [not_nonempty_iff_eq_empty.mp h,Measure.real] at hV
  have hCV : 0<μ.real C := hV.trans_le (measureReal_mono hKC hC.measure_ne_top)
  have hb := budget_antitone hK hne hC hKC f lo hi horder hW
  have hm := hglobal C f lo hi hC hCc hCV
    (fun i => (hW i).trans_le (width_mono hK hne hC hKC (f i))) horder (hb.trans hbudget)
  unfold GlobalPlankBodyMinimum.margin at hm
  have hh : μ.real (K\covered f lo hi)/μ.real K+
      ((B-budget C f lo hi)^d-(B-budget K f lo hi)^d)≤
        μ.real (C\covered f lo hi)/μ.real C := by linarith only [hm]
  have hmul := (le_div_iff₀ hCV).mp hh
  rw [measureReal_sdiff hKC hK.measurableSet hC.measure_ne_top,
    added_gap μ hC.measure_ne_top hK.measurableSet (measurable_covered f lo hi) hKC]
  have he : μ.real (K\covered f lo hi)/μ.real K*μ.real K=
      μ.real (K\covered f lo hi) := div_mul_cancel₀ _ hV.ne'
  nlinarith only [hmul,he]

/-- Every added region must have at least the original body's uncovered
volume fraction. Width growth is allowed and can only strengthen this test. -/
theorem added_gap_ge (μ : Measure E) [μ.IsAddHaarMeasure]
    {K C : Set E} (hK : IsCompact K) (hV : 0<μ.real K)
    (hC : IsCompact C) (hCc : Convex ℝ C) (hKC : K⊆C)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i, lo i≤hi i) (hW : ∀ i, 0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B) :
    μ.real (K\covered f lo hi)/μ.real K*μ.real (C\K)≤
      μ.real ((C\K)\covered f lo hi) := by
  have hne : K.Nonempty := by
    by_contra h
    simp [not_nonempty_iff_eq_empty.mp h,Measure.real] at hV
  have hb := budget_antitone hK hne hC hKC f lo hi horder hW
  have hp : (B-budget K f lo hi)^d≤(B-budget C f lo hi)^d :=
    pow_le_pow_left₀ (sub_nonneg.mpr hbudget) (sub_le_sub_left hb B) d
  have hn := mul_nonneg (show 0≤μ.real C from measureReal_nonneg) (sub_nonneg.mpr hp)
  have hh := added_gap_ge_with_budget μ hK hV hC hCc hKC f lo hi horder hW d hbudget hglobal
  linarith only [hh,hn]

/-- Apply the enlargement test to an actual cap with linear volume growth
and quadratic uncovered-volume growth. Only geometric inclusion is needed;
the widths of the enlarged body are free to increase. -/
theorem no_linear_quadratic_enlargement (μ : Measure E) [μ.IsAddHaarMeasure]
    {K C : Set E} (hK : IsCompact K) (hV : 0<μ.real K)
    (hC : IsCompact C) (hCc : Convex ℝ C) (hKC : K⊆C)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i, lo i≤hi i) (hW : ∀ i, 0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (α β ε : ℝ) (hε : 0<ε)
    (hvol : α*ε≤μ.real (C\K))
    (hgap : μ.real ((C\K)\covered f lo hi)≤β*ε^2)
    (hsmall : β*ε<μ.real (K\covered f lo hi)/μ.real K*α) : False := by
  have hq : 0≤μ.real (K\covered f lo hi)/μ.real K := div_nonneg measureReal_nonneg hV.le
  have hlow := (mul_le_mul_of_nonneg_left hvol hq).trans
    (added_gap_ge μ hK hV hC hCc hKC f lo hi horder hW d hbudget hglobal)
  have hstrict := mul_lt_mul_of_pos_right hsmall hε
  nlinarith only [hlow,hgap,hstrict]

/-- Positive-gap global minima admit no proper convex enlargement with
nonincreasing gap volume, even without any support-width restriction. -/
theorem eq_of_gap_volume_le (μ : Measure E) [μ.IsAddHaarMeasure]
    {K C : Set E} (hK : IsCompact K) (hV : 0<μ.real K)
    (hC : IsCompact C) (hCc : Convex ℝ C) (hKC : K⊆C)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i, lo i≤hi i) (hW : ∀ i, 0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi))
    (hle : μ.real (C\covered f lo hi)≤μ.real (K\covered f lo hi)) : C=K := by
  have hh := added_gap_ge μ hK hV hC hCc hKC f lo hi horder hW d hbudget hglobal
  rw [measureReal_sdiff hKC hK.measurableSet hC.measure_ne_top,
    added_gap μ hC.measure_ne_top hK.measurableSet (measurable_covered f lo hi) hKC] at hh
  have hq : 0<μ.real (K\covered f lo hi)/μ.real K := div_pos hgap hV
  have hvol := measureReal_mono (μ := μ) hKC hC.measure_ne_top
  have he : μ.real K=μ.real C := by nlinarith only [hh,hq,hvol,hle]
  have hCV := hV.trans_le hvol
  exact (ConvexMeasureRigidity.eq_of_full_measure μ hCc hK.isClosed hKC
    (ENNReal.toReal_pos_iff.mp hCV).1 hC.measure_ne_top
    ((ENNReal.toReal_eq_toReal_iff' hK.measure_ne_top hC.measure_ne_top).mp he)).symm

end Plank.GlobalPlankBodyEnlargement
