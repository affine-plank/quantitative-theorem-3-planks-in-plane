/- Actual areas of polygonal half-plane intersections by vertical slabs. -/
module

public import Plank.Proofs.Quant.PlanarStatement
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose
import Mathlib.Data.Finset.Max

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPolygonSlabs

open Set MeasureTheory

/-- Vertical sections are closed; horizontal sections are half-open so
adjacent slabs are exactly disjoint. -/
def between (a b : ℝ) (l u : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioc a b ∧ p.2 ∈ Icc (l p.1) (u p.1)}

theorem measurableSet_between (a b : ℝ) {l u : ℝ → ℝ}
    (hl : Measurable l) (hu : Measurable u) : MeasurableSet (between a b l u) :=
  measurableSet_region_between_cc hl hu measurableSet_Ioc

/-- Fubini computes the area of the actual set, including empty and
zero-height vertical sections. No ordering of the graphs is assumed. -/
theorem measure_between (a b : ℝ) {l u : ℝ → ℝ}
    (hl : Measurable l) (hu : Measurable u) :
    volume (between a b l u) = ∫⁻ x in Ioc a b, ENNReal.ofReal (u x-l x) := by
  classical
  rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_between a b hl hu)]
  have hsections : (fun x : ℝ => volume (Prod.mk x ⁻¹' between a b l u)) =
      (Ioc a b).indicator (fun x => ENNReal.ofReal (u x-l x)) := by
    funext x
    by_cases hx : a < x ∧ x ≤ b <;> simp [between, Set.preimage, hx]
    exact Real.volume_Icc
  rw [hsections, lintegral_indicator measurableSet_Ioc]

/-- An affine inequality on a closed interval follows from its two endpoint
inequalities. This includes intervals with equal endpoints. -/
theorem affine_le_on_Icc {a b s t v w : ℝ}
    (ha : s*a+t ≤ v*a+w) (hb : s*b+t ≤ v*b+w)
    {x : ℝ} (hx : x ∈ Icc a b) : s*x+t ≤ v*x+w := by
  by_cases hs : s ≤ v
  · nlinarith only [ha, mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hx.1)]
  · nlinarith only [hb, mul_nonneg (sub_nonneg.mpr (le_of_not_ge hs))
      (sub_nonneg.mpr hx.2)]

/-- Actual trapezoid area, proved from vertical sections and the integral of
an affine function. Boundary lines and degenerate trapezoids are included. -/
theorem measure_affine_between {a b : ℝ} (hab : a ≤ b) (s t v w : ℝ)
    (ha : s*a+t ≤ v*a+w) (hb : s*b+t ≤ v*b+w) :
    volume (between a b (fun x => s*x+t) (fun x => v*x+w)) =
      ENNReal.ofReal ((b-a)*((v-s)*(a+b)+2*(w-t))/2) := by
  have hint : IntegrableOn (fun x : ℝ => (v*x+w)-(s*x+t)) (Ioc a b) volume :=
    ((by fun_prop : Continuous (fun x : ℝ => (v*x+w)-(s*x+t))).continuousOn.integrableOn_Icc).mono_set
      Ioc_subset_Icc_self
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc a b)]
      (fun x : ℝ => (v*x+w)-(s*x+t)) := by
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    exact Filter.Eventually.of_forall fun x hx =>
      sub_nonneg.mpr (affine_le_on_Icc ha hb (Ioc_subset_Icc_self hx))
  rw [measure_between a b (by fun_prop) (by fun_prop),
    ← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ← intervalIntegral.integral_of_le hab]
  congr 1
  have heq : (fun x : ℝ => (v*x+w)-(s*x+t)) = fun x => (v-s)*x+(w-t) := by
    funext x
    ring
  rw [heq, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ => (v-s)*x)).intervalIntegrable a b)
    intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
    smul_eq_mul]
  ring

theorem measure_affine_between_zero {a b s t v w : ℝ}
    (ha : v*a+w ≤ s*a+t) (hb : v*b+w ≤ s*b+t) :
    volume (between a b (fun x => s*x+t) (fun x => v*x+w)) = 0 := by
  rw [measure_between a b (by fun_prop) (by fun_prop)]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  exact Filter.Eventually.of_forall fun x hx => ENNReal.ofReal_eq_zero.mpr
    (sub_nonpos.mpr (affine_le_on_Icc ha hb (Ioc_subset_Icc_self hx)))

/-- The actual intersection of fixed-slope lower and upper half-planes in
one vertical slab. The intercepts can subsequently depend on plank endpoints. -/
def slab {ι κ : Type*} (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioc a b ∧ (∀ i, ls i*p.1+lc i ≤ p.2) ∧
    ∀ j, p.2 ≤ us j*p.1+uc j}

theorem measurableSet_slab {ι κ : Type*} [Countable ι] [Countable κ]
    (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    MeasurableSet (slab a b ls lc us uc) := by
  unfold slab
  simp only [Set.ofPred_and, Set.ofPred_forall]
  exact (measurable_fst measurableSet_Ioc).inter
    ((MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_snd).inter
      (MeasurableSet.iInter fun j => measurableSet_le measurable_snd (by fun_prop)))

/-- Endpoint comparisons identify the active lower and upper facets on the
whole slab. This is set equality, proved before computing any area. -/
theorem slab_eq_between {ι κ : Type*} {a b : ℝ}
    (ls lc : ι → ℝ) (us uc : κ → ℝ) (i : ι) (j : κ)
    (hl : ∀ k, ls k*a+lc k ≤ ls i*a+lc i ∧ ls k*b+lc k ≤ ls i*b+lc i)
    (hu : ∀ k, us j*a+uc j ≤ us k*a+uc k ∧ us j*b+uc j ≤ us k*b+uc k) :
    slab a b ls lc us uc = between a b (fun x => ls i*x+lc i) (fun x => us j*x+uc j) := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.1, hp.2.1 i, hp.2.2 j⟩
  · intro hp
    refine ⟨hp.1, fun k => ?_, fun k => ?_⟩
    · exact (affine_le_on_Icc (hl k).1 (hl k).2 (Ioc_subset_Icc_self hp.1)).trans hp.2.1
    · exact hp.2.2.trans (affine_le_on_Icc (hu k).1 (hu k).2 (Ioc_subset_Icc_self hp.1))

/-- Actual area of a polygon slab from finitely checkable facet comparisons.
The caller supplies geometric inequalities, not an assumed area polynomial. -/
theorem measure_slab_of_active {ι κ : Type*} {a b : ℝ} (hab : a ≤ b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) (i : ι) (j : κ)
    (hl : ∀ k, ls k*a+lc k ≤ ls i*a+lc i ∧ ls k*b+lc k ≤ ls i*b+lc i)
    (hu : ∀ k, us j*a+uc j ≤ us k*a+uc k ∧ us j*b+uc j ≤ us k*b+uc k)
    (ha : ls i*a+lc i ≤ us j*a+uc j) (hb : ls i*b+lc i ≤ us j*b+uc j) :
    volume (slab a b ls lc us uc) =
      ENNReal.ofReal ((b-a)*((us j-ls i)*(a+b)+2*(uc j-lc i))/2) := by
  rw [slab_eq_between ls lc us uc i j hl hu]
  exact measure_affine_between hab _ _ _ _ ha hb

theorem measure_slab_zero {ι κ : Type*} {a b : ℝ}
    (ls lc : ι → ℝ) (us uc : κ → ℝ) (i : ι) (j : κ)
    (ha : us j*a+uc j ≤ ls i*a+lc i) (hb : us j*b+uc j ≤ ls i*b+lc i) :
    volume (slab a b ls lc us uc) = 0 := by
  apply measure_mono_null (t := between a b (fun x => ls i*x+lc i) (fun x => us j*x+uc j))
  · exact fun p hp => ⟨hp.1, hp.2.1 i, hp.2.2 j⟩
  · exact measure_affine_between_zero ha hb

/-- The vertical half-open convention gives exact disjointness of adjacent
pieces, including when some partition endpoints coincide. -/
theorem measure_slab_add {ι κ : Type*} [Countable ι] [Countable κ]
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    volume (slab a c ls lc us uc) =
      volume (slab a b ls lc us uc) + volume (slab b c ls lc us uc) := by
  have hunion : slab a b ls lc us uc ∪ slab b c ls lc us uc = slab a c ls lc us uc := by
    ext p
    simp only [slab, mem_union, mem_ofPred_eq]
    rw [← or_and_right, ← mem_union, Ioc_union_Ioc_eq_Ioc hab hbc]
  have hdisjoint : Disjoint (slab a b ls lc us uc) (slab b c ls lc us uc) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge hp.1.2) hq.1.1
  rw [← hunion, measure_union hdisjoint (measurableSet_slab b c ls lc us uc)]

/-- The area of the actual full half-plane intersection is the sum of its
vertical polygon slabs along any ordered finite partition. -/
theorem measure_slab_sum {ι κ : Type*} [Countable ι] [Countable κ]
    (a : ℕ → ℝ) (ha : Monotone a) (ls lc : ι → ℝ) (us uc : κ → ℝ) (n : ℕ) :
    volume (slab (a 0) (a n) ls lc us uc) =
      ∑ k ∈ Finset.range n, volume (slab (a k) (a (k+1)) ls lc us uc) := by
  induction n with
  | zero => simp [slab]
  | succ n ih =>
    rw [measure_slab_add (ha (Nat.zero_le n)) (ha (Nat.le_succ n)), ih,
      Finset.sum_range_succ]

/-- The geometric certificate for the active lower and upper facets of one
nonnegative-height slab. All comparisons concern actual line values. -/
structure ActiveFacets {ι κ : Type*} (a b : ℝ)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) (i : ι) (j : κ) : Prop where
  ordered : a ≤ b
  lower : ∀ k, ls k*a+lc k ≤ ls i*a+lc i ∧ ls k*b+lc k ≤ ls i*b+lc i
  upper : ∀ k, us j*a+uc j ≤ us k*a+uc k ∧ us j*b+uc j ≤ us k*b+uc k
  left_height : ls i*a+lc i ≤ us j*a+uc j
  right_height : ls i*b+lc i ≤ us j*b+uc j

theorem trapezoid_nonneg {a b s t v w : ℝ} (hab : a ≤ b)
    (ha : s*a+t ≤ v*a+w) (hb : s*b+t ≤ v*b+w) :
    0 ≤ (b-a)*((v-s)*(a+b)+2*(w-t))/2 := by
  apply div_nonneg (mul_nonneg (sub_nonneg.mpr hab) ?_) (by norm_num)
  nlinarith only [ha, hb]

/-- If the same geometric facets remain active while intercepts and slab
endpoints move affinely, the actual area is a quadratic polynomial. The
polynomial and its nonnegativity are conclusions, not chart assumptions. -/
theorem measure_slab_affine_motion {ι κ : Type*} {J : Set ℝ}
    (a₀ a₁ b₀ b₁ : ℝ) (ls l₀ l₁ : ι → ℝ) (us u₀ u₁ : κ → ℝ) (i : ι) (j : κ)
    (hfacets : ∀ t ∈ J, ActiveFacets (a₀+a₁*t) (b₀+b₁*t)
      ls (fun k => l₀ k+l₁ k*t) us (fun k => u₀ k+u₁ k*t) i j) :
    ∃ A g H : ℝ, ∀ t ∈ J,
      volume (slab (a₀+a₁*t) (b₀+b₁*t)
        ls (fun k => l₀ k+l₁ k*t) us (fun k => u₀ k+u₁ k*t)) =
          ENNReal.ofReal (A+g*t+(H/2)*t^2) ∧ 0 ≤ A+g*t+(H/2)*t^2 := by
  let c₀ := (us j-ls i)*(a₀+b₀)+2*(u₀ j-l₀ i)
  let c₁ := (us j-ls i)*(a₁+b₁)+2*(u₁ j-l₁ i)
  let d₀ := b₀-a₀
  let d₁ := b₁-a₁
  refine ⟨d₀*c₀/2, (d₁*c₀+d₀*c₁)/2, d₁*c₁, ?_⟩
  intro t ht
  have hf := hfacets t ht
  have heq :
      ((b₀+b₁*t)-(a₀+a₁*t))*
          ((us j-ls i)*((a₀+a₁*t)+(b₀+b₁*t))+2*((u₀ j+u₁ j*t)-(l₀ i+l₁ i*t)))/2 =
        d₀*c₀/2+(d₁*c₀+d₀*c₁)/2*t+(d₁*c₁/2)*t^2 := by
    dsimp [c₀, c₁, d₀, d₁]
    ring
  constructor
  · rw [measure_slab_of_active hf.ordered ls _ us _ i j hf.lower hf.upper
      hf.left_height hf.right_height, heq]
  · rw [← heq]
    exact trapezoid_nonneg hf.ordered hf.left_height hf.right_height

/-- A finite collection of active or empty geometric slabs gives a quadratic
formula for the actual area of the entire intersection. The affine partition
and facet comparisons are explicit geometric inputs; no area identity is. -/
theorem area_slab_partition_affine_motion {ι κ : Type*} [Countable ι] [Countable κ]
    {J : Set ℝ} (n : ℕ) (a₀ a₁ : ℕ → ℝ)
    (ls l₀ l₁ : ι → ℝ) (us u₀ u₁ : κ → ℝ) (i : ℕ → ι) (j : ℕ → κ)
    (hmono : ∀ t ∈ J, Monotone (fun k => a₀ k+a₁ k*t))
    (hcharts : ∀ k < n,
      (∀ t ∈ J, ActiveFacets (a₀ k+a₁ k*t) (a₀ (k+1)+a₁ (k+1)*t)
        ls (fun r => l₀ r+l₁ r*t) us (fun r => u₀ r+u₁ r*t) (i k) (j k)) ∨
      (∀ t ∈ J,
        us (j k)*(a₀ k+a₁ k*t)+(u₀ (j k)+u₁ (j k)*t) ≤
          ls (i k)*(a₀ k+a₁ k*t)+(l₀ (i k)+l₁ (i k)*t) ∧
        us (j k)*(a₀ (k+1)+a₁ (k+1)*t)+(u₀ (j k)+u₁ (j k)*t) ≤
          ls (i k)*(a₀ (k+1)+a₁ (k+1)*t)+(l₀ (i k)+l₁ (i k)*t))) :
    ∃ A g H : ℝ, ∀ t ∈ J,
      (volume (slab (a₀ 0+a₁ 0*t) (a₀ n+a₁ n*t)
        ls (fun r => l₀ r+l₁ r*t) us (fun r => u₀ r+u₁ r*t))).toReal =
          A+g*t+(H/2)*t^2 := by
  classical
  have hex (k : ℕ) : ∃ A g H : ℝ, k < n → ∀ t ∈ J,
      volume (slab (a₀ k+a₁ k*t) (a₀ (k+1)+a₁ (k+1)*t)
        ls (fun r => l₀ r+l₁ r*t) us (fun r => u₀ r+u₁ r*t)) =
          ENNReal.ofReal (A+g*t+(H/2)*t^2) ∧ 0 ≤ A+g*t+(H/2)*t^2 := by
    by_cases hk : k < n
    · rcases hcharts k hk with hactive | hempty
      · obtain ⟨A, g, H, hcert⟩ := measure_slab_affine_motion
          (a₀ k) (a₁ k) (a₀ (k+1)) (a₁ (k+1)) ls l₀ l₁ us u₀ u₁ (i k) (j k) hactive
        exact ⟨A, g, H, fun _ => hcert⟩
      · refine ⟨0, 0, 0, fun _ t ht => ?_⟩
        have hzero := measure_slab_zero ls (fun r => l₀ r+l₁ r*t)
          us (fun r => u₀ r+u₁ r*t) (i k) (j k) (hempty t ht).1 (hempty t ht).2
        simpa only [zero_mul, zero_add, zero_div, ENNReal.ofReal_zero] using
          And.intro hzero (le_refl (0 : ℝ))
    · exact ⟨0, 0, 0, fun h => (hk h).elim⟩
  choose A g H hcert using hex
  refine ⟨∑ k ∈ Finset.range n, A k, ∑ k ∈ Finset.range n, g k,
    ∑ k ∈ Finset.range n, H k, ?_⟩
  intro t ht
  have hc (k : ℕ) (hk : k ∈ Finset.range n) := hcert k (Finset.mem_range.mp hk) t ht
  rw [measure_slab_sum _ (hmono t ht)]
  rw [ENNReal.toReal_sum (fun k hk => by rw [(hc k hk).1]; exact ENNReal.ofReal_ne_top)]
  calc
    _ = ∑ k ∈ Finset.range n, (A k+g k*t+(H k/2)*t^2) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [(hc k hk).1, ENNReal.toReal_ofReal (hc k hk).2]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]

/-- The same actual set in the coordinate convention of `SharpPlanarBound`.
The product-plane calculations therefore use exactly the target's area. -/
def coordinateSlab {ι κ : Type*} (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    Set PlanarQuantitative.Point := {x | (x 0, x 1) ∈ slab a b ls lc us uc}

theorem measure_coordinateSlab {ι κ : Type*}
    (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    volume (coordinateSlab a b ls lc us uc) = volume (slab a b ls lc us uc) := by
  exact (volume_preserving_finTwoArrow ℝ).measure_preimage_equiv (slab a b ls lc us uc)

/-- Without an interior crossing, the order of two affine graphs at the
midpoint determines their order at both slab endpoints. Parallel graphs,
coincident graphs and zero-length slabs are allowed. -/
theorem affine_endpoint_order_of_no_crossing {a b s t v w : ℝ} (hab : a ≤ b)
    (hmid : s*((a+b)/2)+t ≤ v*((a+b)/2)+w)
    (hno : s ≠ v → (w-t)/(s-v) ∉ Ioo a b) :
    s*a+t ≤ v*a+w ∧ s*b+t ≤ v*b+w := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · have ham : a < (a+b)/2 := by linarith only [hab]
    have hmb : (a+b)/2 < b := by linarith only [hab]
    by_cases hsv : s = v
    · subst v
      constructor <;> nlinarith only [hmid]
    rcases lt_or_gt_of_ne (sub_ne_zero.mpr hsv) with hneg | hpos
    · constructor
      · by_contra hn
        have hbad := lt_of_not_ge hn
        have hleft : a < (w-t)/(s-v) := (lt_div_iff_of_neg hneg).mpr (by
          nlinarith only [hbad])
        have hright : (w-t)/(s-v) ≤ (a+b)/2 := (div_le_iff_of_neg hneg).mpr (by
          nlinarith only [hmid])
        exact hno hsv ⟨hleft, hright.trans_lt hmb⟩
      · have hmul := mul_nonpos_of_nonpos_of_nonneg hneg.le (sub_nonneg.mpr hmb.le)
        nlinarith only [hmid, hmul]
    · constructor
      · have hmul := mul_nonneg hpos.le (sub_nonneg.mpr ham.le)
        nlinarith only [hmid, hmul]
      · by_contra hn
        have hbad := lt_of_not_ge hn
        have hleft : (a+b)/2 ≤ (w-t)/(s-v) := (le_div_iff₀ hpos).mpr (by
          nlinarith only [hmid])
        have hright : (w-t)/(s-v) < b := (div_lt_iff₀ hpos).mpr (by
          nlinarith only [hbad])
        exact hno hsv ⟨ham.trans_le hleft, hright⟩
  · constructor <;> nlinarith only [hmid]

/-- The vertical projections of all nonparallel boundary intersections lie
outside the slab interior. The family contains both lower and upper lines. -/
def NoCrossing {ι κ : Type*} (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) : Prop :=
  ∀ p q : ι ⊕ κ, Sum.elim ls us p ≠ Sum.elim ls us q →
    (Sum.elim lc uc q-Sum.elim lc uc p)/(Sum.elim ls us p-Sum.elim ls us q) ∉ Ioo a b

/-- Cutting at every boundary intersection is enough to obtain the geometric
certificate used by the area formula. Active facets are selected from the
actual finite families, rather than assumed to exist. -/
theorem exists_active_or_empty {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] {a b : ℝ} (hab : a ≤ b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) (hno : NoCrossing a b ls lc us uc) :
    ∃ (i : ι) (j : κ), ActiveFacets a b ls lc us uc i j ∨
      (us j*a+uc j ≤ ls i*a+lc i ∧ us j*b+uc j ≤ ls i*b+lc i) := by
  classical
  obtain ⟨i, _, hli⟩ := Finset.exists_max_image Finset.univ
    (fun k => ls k*((a+b)/2)+lc k) Finset.univ_nonempty
  obtain ⟨j, _, huj⟩ := Finset.exists_min_image Finset.univ
    (fun k => us k*((a+b)/2)+uc k) Finset.univ_nonempty
  have hl (k : ι) : ls k*a+lc k ≤ ls i*a+lc i ∧ ls k*b+lc k ≤ ls i*b+lc i :=
    affine_endpoint_order_of_no_crossing hab (hli k (Finset.mem_univ _))
      (hno (Sum.inl k) (Sum.inl i))
  have hu (k : κ) : us j*a+uc j ≤ us k*a+uc k ∧ us j*b+uc j ≤ us k*b+uc k :=
    affine_endpoint_order_of_no_crossing hab (huj k (Finset.mem_univ _))
      (hno (Sum.inr j) (Sum.inr k))
  refine ⟨i, j, ?_⟩
  by_cases hm : ls i*((a+b)/2)+lc i ≤ us j*((a+b)/2)+uc j
  · have hh := affine_endpoint_order_of_no_crossing hab hm (hno (Sum.inl i) (Sum.inr j))
    exact Or.inl ⟨hab, hl, hu, hh.1, hh.2⟩
  · exact Or.inr (affine_endpoint_order_of_no_crossing hab (le_of_not_ge hm)
      (hno (Sum.inr j) (Sum.inl i)))

end Plank.PlanarPolygonSlabs
