/- Ordered-stack necessity in the shared-extremal-segment triangle chart. -/
module

public import Plank.Proofs.Quant.CommonMiddleNecessity
public import Mathlib.Analysis.Convex.Topology

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CommonMiddleNecessity

open Set MeasureTheory Function CommonVertex
open Plank.Convex.AffineSlabNormalization
open scoped BigOperators

/-- The triangle above the horizontal level `d`. -/
def upperTriangle (d : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ d ≤ z.2 ∧ z.1 + z.2 ≤ 1}

theorem convex_upperTriangle (d : ℝ) : Convex ℝ (upperTriangle d) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a*x.1+b*y.1 ∧ d ≤ a*x.2+b*y.2 ∧
    (a*x.1+b*y.1)+(a*x.2+b*y.2) ≤ 1
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_, ?_⟩
  · have hs := add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ha)
      (mul_le_mul_of_nonneg_left hy.2.1 hb)
    rwa [← add_mul, hab, one_mul] at hs
  · have hs := add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
      (mul_le_mul_of_nonneg_left hy.2.2 hb)
    nlinarith only [hs, hab]

theorem isClosed_upperTriangle (d : ℝ) : IsClosed (upperTriangle d) :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

theorem upperTriangle_interior_nonempty (d : ℝ) (hd : d < 1) :
    (interior (upperTriangle d)).Nonempty := by
  let O : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ d < z.2 ∧ z.1 + z.2 < 1}
  have hO : IsOpen O := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hsub : O ⊆ upperTriangle d := fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩
  refine ⟨((1-d)/4, d+(1-d)/4), interior_maximal hsub hO ?_⟩
  change 0 < (1-d)/4 ∧ d < d+(1-d)/4 ∧ (1-d)/4+(d+(1-d)/4) < 1
  exact ⟨by linarith, by linarith, by linarith⟩

/-- A closed cover holding almost everywhere on a full-dimensional closed
convex set holds at every point, including its boundary. -/
theorem subset_of_null_sdiff {K H : Set (ℝ × ℝ)} (hK : IsClosed K)
    (hc : Convex ℝ K) (hint : (interior K).Nonempty) (hH : IsClosed H)
    (hnull : volume (K \ H) = 0) : K ⊆ H := by
  by_contra hn
  obtain ⟨z, hz, hmiss⟩ := not_subset.mp hn
  have hcl : closure (interior K) = K :=
    (hc.closure_interior_eq_closure_of_nonempty_interior hint).trans hK.closure_eq
  have hmeet : (interior K ∩ Hᶜ).Nonempty :=
    (closure_inter_open_nonempty_iff hH.isOpen_compl).mp (by
      rw [hcl]
      exact ⟨z, hz, hmiss⟩)
  have hp := (isOpen_interior.inter hH.isOpen_compl).measure_pos volume hmeet
  have hm : volume (interior K ∩ Hᶜ) ≤ volume (K \ H) :=
    measure_mono (fun _ hx => ⟨interior_subset hx.1, hx.2⟩)
  rw [hnull] at hm
  exact (not_lt_of_ge hm) hp

/-- Quantitative equality forces an actual cover of the upper homothetic
triangle. No positive-width assumption is needed for this step. -/
theorem upperTriangle_covered (C : Config) (b : Fin 3 → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hu : ∀ i, (C.plank i).u = (1, b i))
    (hR : 0 < C.sumRelW) (hR1 : C.sumRelW < 1)
    (he : TriangleEqualityReductions.Equality C) :
    upperTriangle C.deficit ⊆ ⋃ i, (C.plank i).set := by
  have hδ : 0 < C.deficit := sub_pos.mpr hR1
  have hδ1 : C.deficit < 1 := by dsimp [Config.deficit]; linarith
  apply subset_of_null_sdiff (isClosed_upperTriangle _)
    (convex_upperTriangle _) (upperTriangle_interior_nonempty _ hδ1)
    (isClosed_iUnion_of_finite fun i => Proofs.Quant.isClosed_plank_set (C.plank i))
  have hline := (measure_eq_zero_iff_ae_notMem).mp
    (volume_line_zero (u := (0,1)) (by simp [Prod.ext_iff]) C.deficit)
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [gap_below C b hb hu hδ he, hline] with z hz hline hmiss
  have hT : z ∈ stdTriangle.set := by
    rw [Proofs.Quant.stdTriangle_set_eq]
    exact ⟨hmiss.1.1, hδ.le.trans hmiss.1.2.1, hmiss.1.2.2⟩
  have hle := hz ⟨hT, hmiss.2⟩
  apply hline
  simpa [dot] using le_antisymm hle hmiss.1.2.1

/-- The elementary interval-cover lower bound, for arbitrary endpoints. -/
theorem interval_cover_budget {ι : Type*} [Fintype ι] (lo hi : ι → ℝ)
    (ho : ∀ i, lo i ≤ hi i)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i, lo i ≤ t ∧ t ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) := by
  have hsub : Icc (0 : ℝ) 1 ⊆ ⋃ i, Icc (lo i) (hi i) := by
    intro t ht
    obtain ⟨i, hi⟩ := hcover t ht
    exact mem_iUnion.mpr ⟨i, hi⟩
  have h := (measure_mono hsub).trans (RowDeletion.interval_union_budget lo hi ho)
  rw [Real.volume_Icc, sub_zero] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (ho i))).mp h

/-- A tight positive interval cover has no endpoint outside its segment. -/
theorem interval_cover_no_waste {ι : Type*} [Fintype ι] (lo hi : ι → ℝ)
    (ho : ∀ i, lo i < hi i)
    (hcover : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i, lo i ≤ t ∧ t ≤ hi i)
    (hsum : (∑ i, (hi i - lo i)) = 1) : ∀ i, 0 ≤ lo i ∧ hi i ≤ 1 := by
  have hle (i : ι) := clamp_sub_le (lo i) (hi i) (ho i).le
  have hcov : ∀ t ∈ Icc (0 : ℝ) 1,
      ∃ i, clamp (lo i) ≤ t ∧ t ≤ clamp (hi i) := by
    intro t ht
    obtain ⟨i, hi⟩ := hcover t ht
    exact ⟨i, clamp_interval _ _ _ ht hi⟩
  have hlower := interval_cover_budget (fun i => clamp (lo i)) (fun i => clamp (hi i))
    (fun i => clamp_mono (ho i).le) hcov
  have heq : (∑ i, (clamp (hi i) - clamp (lo i))) = ∑ i, (hi i - lo i) :=
    le_antisymm (Finset.sum_le_sum (fun i _ => hle i)) (hsum.le.trans hlower)
  intro i
  have heqi := (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp heq i (Finset.mem_univ i)
  have hpos := ho i
  dsimp [clamp] at heqi
  constructor <;> by_contra! hbad <;>
    simp only [max_def, min_def] at heqi <;> split_ifs at heqi <;> linarith

/-- Normalize the common extremal segment of the upper triangle. -/
def upperForm (d R b : ℝ) : (ℝ × ℝ) →ᵃ[ℝ] ℝ :=
  R⁻¹ • ((LinearMap.fst ℝ ℝ ℝ + b • LinearMap.snd ℝ ℝ ℝ).toAffineMap -
    AffineMap.const ℝ (ℝ × ℝ) (d*b))

theorem upperForm_apply (d R b : ℝ) (z : ℝ × ℝ) :
    upperForm d R b z = (z.1 + b*z.2 - d*b)/R := by
  change R⁻¹ * (z.1 + b*z.2 - d*b) = _
  ring

/-- The three windows form an ordered stack, with their offsets contracted
towards the corresponding middle-vertex values by the common deficit. -/
def OrderedStack (C : Config) (b : Fin 3 → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), b (σ 0) ≤ b (σ 1) ∧ b (σ 1) ≤ b (σ 2) ∧
    (C.plank (σ 0)).lo = C.deficit*b (σ 0) ∧
    (C.plank (σ 0)).hi = C.deficit*b (σ 0) + C.relW (σ 0) ∧
    (C.plank (σ 1)).lo = C.deficit*b (σ 1) + C.relW (σ 0) ∧
    (C.plank (σ 1)).hi = C.deficit*b (σ 1) + C.relW (σ 0) + C.relW (σ 1) ∧
    (C.plank (σ 2)).lo = C.deficit*b (σ 2) + C.relW (σ 0) + C.relW (σ 1) ∧
    (C.plank (σ 2)).hi = C.deficit*b (σ 2) + C.sumRelW

/-- Exhaustive necessity in the common minimum/maximum triangle chart, for
positive widths and a subcritical total budget. Repeated and boundary
directions are included. The chart restriction is an explicit hypothesis. -/
theorem orderedStack_of_equality (C : Config) (b : Fin 3 → ℝ)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hu : ∀ i, (C.plank i).u = (1, b i))
    (hw : ∀ i, 0 < C.relW i) (hR : 0 < C.sumRelW) (hR1 : C.sumRelW < 1)
    (he : TriangleEqualityReductions.Equality C) : OrderedStack C b := by
  let R := C.sumRelW
  let d := C.deficit
  let g : Fin 3 → (ℝ × ℝ) →ᵃ[ℝ] ℝ := fun i => upperForm d R (b i)
  let lo : Fin 3 → ℝ := fun i => ((C.plank i).lo - d*b i)/R
  let hi : Fin 3 → ℝ := fun i => ((C.plank i).hi - d*b i)/R
  have hRp : 0 < R := hR
  have hRn : R ≠ 0 := ne_of_gt hRp
  have hdR : d + R = 1 := by dsimp [d, R, Config.deficit]; ring
  have hd1 : d < 1 := by linarith only [hdR, hRp]
  have hA : (0,d) ∈ upperTriangle d := ⟨le_rfl, le_rfl, by dsimp; linarith only [hd1]⟩
  have hB : (R,d) ∈ upperTriangle d := ⟨hRp.le, le_rfl, by dsimp; linarith only [hdR]⟩
  have htop : (0,1) ∈ upperTriangle d := ⟨le_rfl, hd1.le, by norm_num⟩
  have hgA (i : Fin 3) : g i (0,d) = 0 := by
    rw [upperForm_apply]
    ring
  have hgB (i : Fin 3) : g i (R,d) = 1 := by
    rw [upperForm_apply]
    apply (div_eq_iff hRn).mpr
    ring
  have hgtop (i : Fin 3) : g i (0,1) = b i := by
    rw [upperForm_apply]
    apply (div_eq_iff hRn).mpr
    rw [show R = 1-d by linarith only [hdR]]
    ring
  have hbox : ∀ z ∈ upperTriangle d, ∀ i, 0 ≤ g i z ∧ g i z ≤ 1 := by
    intro z hz i
    rw [upperForm_apply]
    have hy : 0 ≤ z.2-d := sub_nonneg.mpr hz.2.1
    have hnonneg := mul_nonneg (hb i).1 hy
    have hle := mul_le_mul_of_nonneg_right (hb i).2 hy
    constructor
    · apply div_nonneg _ hRp.le
      nlinarith only [hz.1, hnonneg]
    · apply (div_le_one hRp).mpr
      nlinarith only [hle, hz.2.2, hdR]
  have hwidth (i : Fin 3) : hi i - lo i = C.relW i/R := by
    rw [relative_width C b hb hu]
    dsimp [hi, lo]
    ring
  have hpositive (i : Fin 3) : lo i < hi i :=
    sub_pos.mp (by rw [hwidth]; exact div_pos (hw i) hRp)
  have hsum : (∑ i, (hi i - lo i)) = 1 := by
    simp_rw [hwidth]
    rw [← Finset.sum_div]
    exact div_self hRn
  have hcover : ∀ z ∈ upperTriangle d, ∃ i, lo i ≤ g i z ∧ g i z ≤ hi i := by
    intro z hz
    obtain ⟨i, hil, hih⟩ := mem_iUnion.mp (upperTriangle_covered C b hb hu hR hR1 he hz)
    change (C.plank i).lo ≤ dot (C.plank i).u z at hil
    change dot (C.plank i).u z ≤ (C.plank i).hi at hih
    simp only [hu, dot, one_mul] at hil hih
    refine ⟨i, ?_⟩
    rw [upperForm_apply]
    exact ⟨(div_le_div_iff_of_pos_right hRp).mpr (sub_le_sub_right hil _),
      (div_le_div_iff_of_pos_right hRp).mpr (sub_le_sub_right hih _)⟩
  have hinterval : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i, lo i ≤ t ∧ t ≤ hi i := by
    intro t ht
    have hz := (convex_upperTriangle d).lineMap_mem hA hB ht
    obtain ⟨i, hil, hih⟩ := hcover _ hz
    have hg : g i (AffineMap.lineMap (0,d) (R,d) t) = t := by
      rw [(g i).apply_lineMap, AffineMap.lineMap_apply_ring, hgA, hgB]
      ring
    exact ⟨i, by simpa only [hg] using And.intro hil hih⟩
  have hnoWaste := interval_cover_no_waste lo hi hpositive hinterval hsum
  obtain ⟨σ, r, s, hr, hrs, hs, hl0, hh0, hl1, hh1, hl2, hh2, hord⟩ :=
    (Plank.Convex.PlanarTight.CommonChordClassification.tight_iff
      (upperTriangle d) (convex_upperTriangle d) g (0,d) (R,d) hA hB hgA hgB hbox
      lo hi (fun i => (hnoWaste i).1) (fun i => (hnoWaste i).2) hpositive).mp ⟨hsum, hcover⟩
  have hbOrder := hord (0,1) htop
  simp only [hgtop] at hbOrder
  have h0l := (div_eq_iff hRn).mp hl0
  have h0h := (div_eq_iff hRn).mp hh0
  have h1l := (div_eq_iff hRn).mp hl1
  have h1h := (div_eq_iff hRn).mp hh1
  have h2l := (div_eq_iff hRn).mp hl2
  have h2h := (div_eq_iff hRn).mp hh2
  have hw0 := relative_width C b hb hu (σ 0)
  have hw1 := relative_width C b hb hu (σ 1)
  dsimp only [d, R] at h0l h0h h1l h1h h2l h2h
  refine ⟨σ, hbOrder.1, hbOrder.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith only [h0l]
  · linarith only [h0l, hw0]
  · linarith only [h0l, h0h, h1l, hw0]
  · linarith only [h0l, h0h, h1l, hw0, hw1]
  · linarith only [h0l, h0h, h1l, h1h, h2l, hw0, hw1]
  · linarith only [h2h]

end Quant.CommonMiddleNecessity

/-- info: 'Quant.CommonMiddleNecessity.upperTriangle_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleNecessity.upperTriangle_covered

/-- info: 'Quant.CommonMiddleNecessity.orderedStack_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleNecessity.orderedStack_of_equality
