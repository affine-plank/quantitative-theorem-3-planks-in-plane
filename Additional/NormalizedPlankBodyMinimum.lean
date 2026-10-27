/- An actual quantitative minimum over normalized convex bodies and planks.
Affine normalization of every competitor is still needed before this becomes
a minimum over all bodies. No qualitative plank theorem is used. -/
module

public import MovingConvexBodyGap
public import GlobalPlankBodyMinimum
public import Plank.Proofs.Quant.ConvexExposedSections
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.NormalizedPlankBodyMinimum

open Set TopologicalSpace Metric MeasureTheory
open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]

abbrev Body (r R : ℝ) := {K : NonemptyCompacts E |
  Convex ℝ (K : Set E) ∧ closedBall (0 : E) r ⊆ K ∧ (K : Set E) ⊆ closedBall 0 R}

instance bodyCompact (r R : ℝ) : CompactSpace (Body (E := E) r R) :=
  isCompact_iff_compactSpace.mp (CompactConvexBodyDomain.isCompact_sandwich
    (closedBall 0 r) (closedBall (0 : E) R) (isCompact_closedBall _ _))

abbrev Direction := sphere (0 : E →L[ℝ] ℝ) 1

instance directionCompact : CompactSpace (Direction (E := E)) := inferInstance

abbrev Endpoints := (ι → ℝ) × (ι → ℝ)
abbrev Data (r R : ℝ) := Body (E := E) r R × (ι → Direction (E := E)) × Endpoints (ι := ι)

variable {r R : ℝ}

def body (q : Data (E := E) (ι := ι) r R) : NonemptyCompacts E := q.1.1
def form (q : Data (E := E) (ι := ι) r R) (i : ι) : E →ᵃ[ℝ] ℝ :=
  (q.2.1 i).1.toLinearMap.toAffineMap
def lower (q : Data (E := E) (ι := ι) r R) (i : ι) : ℝ :=
  sInf (form q i '' (body q : Set E))
def span (q : Data (E := E) (ι := ι) r R) (i : ι) : ℝ :=
  Plank.Body.width (body q : Set E) (form q i)
def lo (q : Data (E := E) (ι := ι) r R) (i : ι) : ℝ := lower q i + q.2.2.1 i * span q i
def hi (q : Data (E := E) (ι := ι) r R) (i : ι) : ℝ := lower q i + q.2.2.2 i * span q i
def total (p : Endpoints (ι := ι)) : ℝ := ∑ i, (p.2 i - p.1 i)
def windowDomain (B : ℝ) : Set (Endpoints (ι := ι)) :=
  {p | (∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1) ∧ total p ≤ B}
def domain (B : ℝ) : Set (Data (E := E) (ι := ι) r R) :=
  univ ×ˢ (univ ×ˢ windowDomain B)

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem continuous_body :
    Continuous (fun q : Data (E := E) (ι := ι) r R => body q) := by unfold body; fun_prop

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem continuous_form (i : ι) :
    Continuous (fun p : Data (E := E) (ι := ι) r R × E => form p.1 i p.2) := by
  have hc : Continuous (fun p : Data (E := E) (ι := ι) r R × E =>
      (p.1.2.1 i).1) := by fun_prop
  exact hc.clm_apply continuous_snd

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem continuous_lower (i : ι) :
    Continuous (fun q : Data (E := E) (ι := ι) r R => lower q i) :=
  CompactConvexBodyDomain.continuous_lower_support continuous_body (continuous_form i)

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem continuous_span (i : ι) :
    Continuous (fun q : Data (E := E) (ι := ι) r R => span q i) :=
  (CompactConvexBodyDomain.continuous_support continuous_body (continuous_form i)).sub
    (continuous_lower i)

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem continuous_lo (i : ι) :
    Continuous (fun q : Data (E := E) (ι := ι) r R => lo q i) := by
  have hc : Continuous (fun q : Data (E := E) (ι := ι) r R => q.2.2.1 i) := by fun_prop
  exact (continuous_lower i).add (hc.mul (continuous_span i))

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem continuous_hi (i : ι) :
    Continuous (fun q : Data (E := E) (ι := ι) r R => hi q i) := by
  have hc : Continuous (fun q : Data (E := E) (ι := ι) r R => q.2.2.2 i) := by fun_prop
  exact (continuous_lower i).add (hc.mul (continuous_span i))

theorem continuous_total : Continuous (@total ι _) := by unfold total; fun_prop

theorem isCompact_windowDomain (B : ℝ) : IsCompact (windowDomain (ι := ι) B) := by
  have hc : IsClosed (windowDomain (ι := ι) B) := by
    simp only [windowDomain, Set.ofPred_and, Set.ofPred_forall]
    exact (isClosed_iInter fun i =>
      (_root_.isClosed_le continuous_const (by fun_prop)).inter
        ((_root_.isClosed_le (by fun_prop) (by fun_prop)).inter
          (_root_.isClosed_le (by fun_prop) continuous_const))).inter
      (_root_.isClosed_le continuous_total continuous_const)
  apply (isCompact_Icc : IsCompact (Icc (0 : Endpoints (ι := ι)) 1)).of_isClosed_subset hc
  intro p hp
  exact ⟨⟨fun i => (hp.1 i).1, fun i => (hp.1 i).1.trans (hp.1 i).2.1⟩,
    ⟨fun i => (hp.1 i).2.1.trans (hp.1 i).2.2, fun i => (hp.1 i).2.2⟩⟩

theorem isCompact_domain (B : ℝ) : IsCompact (domain (E := E) (ι := ι) (r := r) (R := R) B) :=
  isCompact_univ.prod (isCompact_univ.prod (isCompact_windowDomain B))

omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem form_linear_ne_zero (q : Data (E := E) (ι := ι) r R) (i : ι) :
    (form q i).linear ≠ 0 := by
  intro h
  have hz : (q.2.1 i).1 = 0 := by
    ext x
    exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) h
  have hs := (q.2.1 i).property
  simp [hz] at hs

section Measure

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [Fintype ι] [BorelSpace E] in
theorem volume_pos (hr : 0 < r) (q : Data (E := E) (ι := ι) r R) :
    0 < μ.real (body q : Set E) := by
  apply ENNReal.toReal_pos
  · exact ((isOpen_ball.measure_pos μ (nonempty_ball.mpr hr)).trans_le
      (measure_mono (ball_subset_closedBall.trans q.1.2.2.1))).ne'
  · exact (body q).isCompact.measure_ne_top

include μ in
omit [Fintype ι] in
theorem span_pos (hr : 0 < r) (q : Data (E := E) (ι := ι) r R) (i : ι) :
    0 < span q i := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Plank.Body.exists_realisers
    (body q).isCompact (body q).nonempty (form q i).continuous_of_finiteDimensional
  have hw : span q i = form q i a - form q i b :=
    Plank.Body.width_eq_of_realisers ha hb hmax hmin
  by_contra! hn
  have hz : μ (body q : Set E) = 0 := measure_mono_null (by
    intro x hx
    change form q i x = form q i b
    have h1 := hmax x hx
    have h2 := hmin x hx
    linarith only [hn,hw,h1,h2])
    (ConvexExposedSections.measure_affine_level_eq_zero μ (form q i)
      (form_linear_ne_zero q i) (form q i b))
  have hv := volume_pos μ hr q
  simp [Measure.real,hz] at hv

include μ in
theorem budget_eq_total (hr : 0 < r) (q : Data (E := E) (ι := ι) r R) :
    PrunedPlankCounterexample.budget (body q : Set E) (form q) (lo q) (hi q) = total q.2.2 := by
  unfold PrunedPlankCounterexample.budget total
  apply Finset.sum_congr rfl
  intro i _
  change (lower q i + q.2.2.2 i * span q i -
    (lower q i + q.2.2.1 i * span q i)) / span q i = q.2.2.2 i - q.2.2.1 i
  field_simp [(span_pos μ hr q i).ne']
  ring

def gap (q : Data (E := E) (ι := ι) r R) : ℝ :=
  μ.real (FiniteBandContinuity.uncovered (body q : Set E) (fun i => form q i) (lo q,hi q))

def margin (d : ℕ) (B : ℝ) (q : Data (E := E) (ι := ι) r R) : ℝ :=
  gap μ q / μ.real (body q : Set E) - (B-total q.2.2)^d

theorem margin_eq_physical (hr : 0 < r) (q : Data (E := E) (ι := ι) r R) (d : ℕ) (B : ℝ) :
    margin μ d B q = GlobalPlankBodyMinimum.margin μ
      (body q : Set E) (form q) (lo q) (hi q) d B := by
  unfold GlobalPlankBodyMinimum.margin margin
  rw [budget_eq_total μ hr q]
  rfl

theorem continuous_gap (hr : 0 < r) :
    Continuous (fun q : Data (E := E) (ι := ι) r R => gap μ q) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact MovingConvexBodyGap.continuousAt_area_uncovered μ body continuous_body.continuousAt
    (fun q => q.1.2.1) hr (fun q => q.1.2.2.1) (isCompact_closedBall _ _)
    (fun q => q.1.2.2.2) (fun q i => form q i) lo hi
    (fun q i => (form q i).continuous_of_finiteDimensional.measurable)
    (fun i x => ((continuous_form i).comp (continuous_id.prodMk continuous_const)).continuousAt)
    (fun i => (continuous_lo i).continuousAt) (fun i => (continuous_hi i).continuousAt)
    (fun i s => ConvexExposedSections.measure_affine_level_eq_zero μ (form p i)
      (form_linear_ne_zero p i) s)

theorem continuous_volume (hr : 0 < r) :
    Continuous (fun q : Data (E := E) (ι := ι) r R => μ.real (body q : Set E)) := by
  rw [continuous_iff_continuousAt]
  intro p
  exact MovingConvexBodyGap.continuousAt_volume μ body continuous_body.continuousAt
    (fun q => q.1.2.1) hr (fun q => q.1.2.2.1) (isCompact_closedBall _ _)
    (fun q => q.1.2.2.2)

theorem continuous_margin (hr : 0 < r) (d : ℕ) (B : ℝ) :
    Continuous (fun q : Data (E := E) (ι := ι) r R => margin μ d B q) :=
  ((continuous_gap μ hr).div (continuous_volume μ hr) (fun q => (volume_pos μ hr q).ne')).sub
    ((continuous_const.sub (continuous_total.comp (by fun_prop))).pow d)

/-- A strict counterexample already in the normalized family yields an actual
negative minimum over all bodies, all directions and all admissible windows
in that family. The plank count and exponent are arbitrary. -/
theorem exists_negative_minimum (hr : 0 < r) (d : ℕ) (B : ℝ)
    {q₀ : Data (E := E) (ι := ι) r R} (hq₀ : q₀ ∈ domain B) (hbad : margin μ d B q₀ < 0) :
    ∃ q : Data (E := E) (ι := ι) r R,
      q ∈ domain B ∧ margin μ d B q < 0 ∧ IsMinOn (margin μ d B) (domain B) q := by
  obtain ⟨q,hq,hm⟩ := (isCompact_domain B).exists_isMinOn ⟨q₀,hq₀⟩
    (continuous_margin μ hr d B).continuousOn
  exact ⟨q,hq,(hm hq₀).trans_lt hbad,hm⟩

end Measure

end Plank.NormalizedPlankBodyMinimum
