module
/- Existence of a genuine area minimizer and its strict Bad geometry. -/
public import Plank.Proofs.Quant.CyclicGapContinuity
public import Plank.Proofs.Quant.CyclicDescentSymmetry

@[expose] public section
noncomputable section

namespace Quant.CyclicGapMinimizer

open Set MeasureTheory CyclicBadThresholds CyclicWeightedThresholdGeometry
  CyclicThresholdCaps CyclicGapCancellation CyclicPairAreas

abbrev Levels := (Fin 3 → ℝ) × (Fin 3 → ℝ)

def levelDomain : Set Levels :=
  (Icc (0 : Fin 3 → ℝ) 1 ×ˢ Icc (0 : Fin 3 → ℝ) 1) ∩
    {p | ∀ i, p.1 i ≤ p.2 i}

def area (a b c : ℝ) (p : Levels) : ℝ :=
  (volume (CyclicExteriorAssembly.uncovered a b c p.1 p.2)).toReal

def actualMargin (a b c : ℝ) (p : Levels) : ℝ :=
  2*area a b c p-squarePos (SixTriangleResidual.deficit p.1 p.2)

theorem continuous_area (a b c : ℝ) : Continuous (area a b c) :=
  CyclicGapContinuity.continuous_uncovered_area a b c

theorem continuous_actualMargin (a b c : ℝ) : Continuous (actualMargin a b c) := by
  have hd : Continuous (fun p : Levels => SixTriangleResidual.deficit p.1 p.2) := by
    dsimp [SixTriangleResidual.deficit]
    fun_prop
  exact ((continuous_area a b c).const_mul 2).sub ((continuous_const.max hd).pow 2)

theorem isCompact_levelDomain : IsCompact levelDomain := by
  have hc : IsClosed {p : Levels | ∀ i, p.1 i ≤ p.2 i} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter (fun i : Fin 3 =>
      isClosed_le (by fun_prop : Continuous (fun p : Levels => p.1 i))
        (by fun_prop : Continuous (fun p : Levels => p.2 i)))
  exact (isCompact_Icc.prod isCompact_Icc).inter_right hc

theorem levelDomain_nonempty : levelDomain.Nonempty := by
  refine ⟨(0,0),?_⟩
  simp [levelDomain]

theorem exists_minimizer (a b c : ℝ) :
    ∃ p ∈ levelDomain, IsMinOn (actualMargin a b c) levelDomain p :=
  isCompact_levelDomain.exists_isMinOn levelDomain_nonempty (continuous_actualMargin a b c).continuousOn

def config (a b c : ℝ) (p : Levels) (hp : ∀ i, p.1 i ≤ p.2 i) : Config :=
  ⟨![⟨(1,b),p.1 1,p.2 1,by simp [Prod.ext_iff],hp 1⟩,
      ⟨(1-a,1),1-p.2 0,1-p.1 0,by simp [Prod.ext_iff],sub_le_sub_left (hp 0) 1⟩,
      ⟨(c,c-1),c-p.2 2,c-p.1 2,by
        intro he
        have h0 := congrArg Prod.fst he
        have h1 := congrArg Prod.snd he
        dsimp at h0 h1
        linarith,
        sub_le_sub_left (hp 2) c⟩]⟩

theorem lowerLevels_config (a b c : ℝ) (p : Levels) (hp : ∀ i, p.1 i ≤ p.2 i) :
    lowerLevels (config a b c p hp) c = p.1 := by
  ext i
  fin_cases i <;> dsimp [lowerLevels,config] <;> ring

theorem upperLevels_config (a b c : ℝ) (p : Levels) (hp : ∀ i, p.1 i ≤ p.2 i) :
    upperLevels (config a b c p hp) c = p.2 := by
  ext i
  fin_cases i <;> dsimp [upperLevels,config] <;> ring

theorem deficit_config (a b c : ℝ) (p : Levels) (hp : ∀ i, p.1 i ≤ p.2 i)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) :
    (config a b c p hp).deficit = SixTriangleResidual.deficit p.1 p.2 := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  rw [CyclicArea.deficit_eq (config a b c p hp) hb ha' hc rfl rfl rfl]
  dsimp [config,OrdinalArea.widths,SixTriangleResidual.deficit]
  ring

theorem gapArea_config (a b c : ℝ) (p : Levels) (hp : ∀ i, p.1 i ≤ p.2 i) :
    (config a b c p hp).gapArea = area a b c p := by
  rw [Config.gapArea,CyclicExteriorAssembly.configuration_uncovered (config a b c p hp) rfl rfl rfl,
    lowerLevels_config,upperLevels_config]
  have he : 1-(1-a) = a := by ring
  rw [he]
  rfl

theorem bad_seed_of_negative_margin (a b c : ℝ) (p : Levels)
    (hp : ∀ i, p.1 i ≤ p.2 i)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hneg : actualMargin a b c p < 0) :
    ∃ z ∈ RowDeletion.triangle (config a b c p hp).deficit,
      z ∈ CyclicArea.badSeeds (config a b c p hp) b (1-a) c := by
  classical
  by_contra hn
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hs := CyclicArea.sqPos_of_no_bad_seed (config a b c p hp) hb ha' hc rfl rfl rfl
    (fun z hz hbad => hn ⟨z,hz,hbad⟩)
  rw [Quant.SqPos,deficit_config a b c p hp ha hb hc,gapArea_config] at hs
  dsimp [actualMargin,squarePos] at hneg
  linarith only [hs,hneg]

/-- Negative true area margin forces strict physical and compatibility bounds.
This does not presume that the scalar formula holds on the entire compact box. -/
theorem strict_bounds_of_negative_margin (a b c : ℝ) (p : Levels)
    (hp : ∀ i, p.1 i ≤ p.2 i)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hneg : actualMargin a b c p < 0) :
    0 < SixTriangleResidual.deficit p.1 p.2 ∧
      (∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1) ∧
      (∀ i, 0 < (1-direction a b c (i+1))*p.1 i-direction a b c i*p.2 (i+1)+
        direction a b c i*direction a b c (i+1)) := by
  obtain ⟨z,hz,hbad⟩ := bad_seed_of_negative_margin a b c p hp ha hb hc hneg
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hlevels := levels_internal_of_bad (config a b c p hp) hb ha' hc rfl rfl rfl hz hbad
  have hwidth := CyclicGeometry.widths_pos_of_bad (config a b c p hp) hb ha' hc hbad
  have horder := CyclicExteriorAssembly.lowerLevels_lt_upperLevels (config a b c p hp) c
    (fun i => sub_pos.mp (hwidth i))
  have hcompat := endpoint_compatible_of_bad (config a b c p hp) hb ha' hc rfl rfl rfl hz hbad
  have he : 1-(1-a) = a := by ring
  rw [lowerLevels_config,upperLevels_config] at hlevels horder
  rw [lowerLevels_config,upperLevels_config,he] at hcompat
  refine ⟨?_,fun i => ⟨(hlevels i).1,horder i,(hlevels i).2⟩,hcompat⟩
  by_contra hn
  have hd : SixTriangleResidual.deficit p.1 p.2 ≤ 0 := le_of_not_gt hn
  have hnarea : 0 ≤ area a b c p := ENNReal.toReal_nonneg
  simp only [actualMargin,squarePos,max_eq_left hd,zero_pow (by decide : 2 ≠ 0),sub_zero] at hneg
  linarith only [hnarea,hneg]

/-- Any counterexample in the normalized endpoint box yields an attained
negative minimum with strict endpoint, width, deficit and compatibility bounds. -/
theorem exists_negative_minimizer (a b c : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (p : Levels) (hp : p ∈ levelDomain) (hneg : actualMargin a b c p < 0) :
    ∃ q ∈ levelDomain, IsMinOn (actualMargin a b c) levelDomain q ∧
      actualMargin a b c q < 0 ∧ 0 < SixTriangleResidual.deficit q.1 q.2 ∧
      (∀ i, 0 < q.1 i ∧ q.1 i < q.2 i ∧ q.2 i < 1) ∧
      (∀ i, 0 < (1-direction a b c (i+1))*q.1 i-direction a b c i*q.2 (i+1)+
        direction a b c i*direction a b c (i+1)) := by
  obtain ⟨q,hq,hmin⟩ := exists_minimizer a b c
  have hnq : actualMargin a b c q < 0 := (hmin hp).trans_lt hneg
  have hbnds := strict_bounds_of_negative_margin a b c q hq.2 ha hb hc hnq
  exact ⟨q,hq,hmin,hnq,hbnds⟩

theorem actualMargin_eq_scalar_of_negative (a b c : ℝ) (p : Levels)
    (hp : ∀ i, p.1 i ≤ p.2 i)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hneg : actualMargin a b c p < 0) :
    actualMargin a b c p = CyclicDescentSymmetry.jointMargin a b c p := by
  obtain ⟨z,hz,hbad⟩ := bad_seed_of_negative_margin a b c p hp ha hb hc hneg
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hs := twice_gapArea_eq_normalized_of_bad (config a b c p hp) hb ha' hc rfl rfl rfl hz hbad
  have he : 1-(1-a) = a := by ring
  rw [gapArea_config,lowerLevels_config,upperLevels_config,he] at hs
  have hd := (strict_bounds_of_negative_margin a b c p hp ha hb hc hneg).1
  dsimp [actualMargin,CyclicDescentSymmetry.jointMargin,CyclicVertexDescent.margin,squarePos]
  rw [max_eq_right hd.le,hs]

open Filter in
open scoped Topology in
theorem levelDomain_mem_nhds_of_strict (p : Levels)
    (hp : ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1) :
    levelDomain ∈ 𝓝 p := by
  have hi (i : Fin 3) : ∀ᶠ q : Levels in 𝓝 p,
      0 < q.1 i ∧ q.1 i < q.2 i ∧ q.2 i < 1 := by
    have hlo : ContinuousAt (fun q : Levels => q.1 i) p := by fun_prop
    have hhi : ContinuousAt (fun q : Levels => q.2 i) p := by fun_prop
    filter_upwards [hlo.eventually_const_lt (hp i).1,
      hlo.eventually_lt hhi (hp i).2.1,hhi.eventually_lt_const (hp i).2.2] with q h0 h1 h2
    exact ⟨h0,h1,h2⟩
  have hall : ∀ᶠ q : Levels in 𝓝 p, ∀ i, 0 < q.1 i ∧ q.1 i < q.2 i ∧ q.2 i < 1 :=
    eventually_all.mpr hi
  filter_upwards [hall] with q hq
  exact ⟨⟨⟨fun i => (hq i).1.le,fun i => ((hq i).2.1.trans (hq i).2.2).le⟩,
    ⟨fun i => ((hq i).1.trans (hq i).2.1).le,fun i => (hq i).2.2.le⟩⟩,
    fun i => (hq i).2.1.le⟩

open Filter in
open scoped Topology in
/-- A negative actual-area minimizer is an ambient local minimum of the exact
scalar expression. Continuity and Bad geometry justify the local identification. -/
theorem scalar_isLocalMin_of_actual_minimum (a b c : ℝ) (p : Levels)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hp : p ∈ levelDomain) (hmin : IsMinOn (actualMargin a b c) levelDomain p)
    (hneg : actualMargin a b c p < 0) :
    IsLocalMin (CyclicDescentSymmetry.jointMargin a b c) p := by
  have hbnds := strict_bounds_of_negative_margin a b c p hp.2 ha hb hc hneg
  have hdom := levelDomain_mem_nhds_of_strict p hbnds.2.1
  have hactual := hmin.isLocalMin hdom
  have hnear : ∀ᶠ q : Levels in 𝓝 p, actualMargin a b c q < 0 :=
    (continuous_actualMargin a b c).continuousAt.eventually_lt_const hneg
  have he0 := actualMargin_eq_scalar_of_negative a b c p hp.2 ha hb hc hneg
  change ∀ᶠ q : Levels in 𝓝 p,
    CyclicDescentSymmetry.jointMargin a b c p ≤ CyclicDescentSymmetry.jointMargin a b c q
  filter_upwards [hactual,hnear,hdom] with q hmq hnq hq
  rw [← he0,← actualMargin_eq_scalar_of_negative a b c q hq.2 ha hb hc hnq]
  exact hmq

/-- The compactness reduction preserves the full actual-area target and yields
strict geometric conditions at the scalar local minimum. -/
theorem exists_negative_scalar_localMin (a b c : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (p : Levels) (hp : p ∈ levelDomain) (hneg : actualMargin a b c p < 0) :
    ∃ q ∈ levelDomain, IsLocalMin (CyclicDescentSymmetry.jointMargin a b c) q ∧
      CyclicDescentSymmetry.jointMargin a b c q < 0 ∧
      0 < SixTriangleResidual.deficit q.1 q.2 ∧
      (∀ i, 0 < q.1 i ∧ q.1 i < q.2 i ∧ q.2 i < 1) ∧
      (∀ i, 0 < (1-direction a b c (i+1))*q.1 i-direction a b c i*q.2 (i+1)+
        direction a b c i*direction a b c (i+1)) := by
  obtain ⟨q,hq,hmin,hnq,hbnds⟩ := exists_negative_minimizer a b c ha hb hc p hp hneg
  have hlocal := scalar_isLocalMin_of_actual_minimum a b c q ha hb hc hq hmin hnq
  have he := actualMargin_eq_scalar_of_negative a b c q hq.2 ha hb hc hnq
  exact ⟨q,hq,hlocal,he ▸ hnq,hbnds⟩

theorem weighted_bounds_of_thresholdLoss_nonpos (a b c : ℝ) (l h : Fin 3 → ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hzero : thresholdLoss a b c l h ≤ 0) :
    ∀ i, weight a b c i*windowWidth l h i ≤ thresholdSlack a b c l ∧
      weight a b c i*windowWidth l h i ≤ -thresholdSlack a b c h := by
  obtain ⟨hk0,hk1,hk2⟩ := weights_pos ha hb hc
  have hd := mul_pos (mul_pos hk0 hk1) hk2
  have hs : (∑ i, (squarePos (weight a b c i*windowWidth l h i-thresholdSlack a b c l)+
      squarePos (weight a b c i*windowWidth l h i+thresholdSlack a b c h))) ≤ 0 := by
    simpa only [zero_mul] using (div_le_iff₀ hd).mp hzero
  intro i
  have hi := Finset.single_le_sum (f := fun i =>
    squarePos (weight a b c i*windowWidth l h i-thresholdSlack a b c l)+
      squarePos (weight a b c i*windowWidth l h i+thresholdSlack a b c h))
    (fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
  have hn := hi.trans hs
  have hleft : max 0 (weight a b c i*windowWidth l h i-thresholdSlack a b c l) = 0 := by
    apply sq_eq_zero_iff.mp
    dsimp only [squarePos] at hn
    nlinarith only [hn,sq_nonneg (max 0 (weight a b c i*windowWidth l h i+thresholdSlack a b c h)),
      sq_nonneg (max 0 (weight a b c i*windowWidth l h i-thresholdSlack a b c l))]
  have hright : max 0 (weight a b c i*windowWidth l h i+thresholdSlack a b c h) = 0 := by
    apply sq_eq_zero_iff.mp
    dsimp only [squarePos] at hn
    nlinarith only [hn,sq_nonneg (max 0 (weight a b c i*windowWidth l h i+thresholdSlack a b c h)),
      sq_nonneg (max 0 (weight a b c i*windowWidth l h i-thresholdSlack a b c l))]
  have hl := le_max_right 0 (weight a b c i*windowWidth l h i-thresholdSlack a b c l)
  have hh := le_max_right 0 (weight a b c i*windowWidth l h i+thresholdSlack a b c h)
  rw [hleft] at hl
  rw [hright] at hh
  constructor <;> linarith only [hl,hh]

/-- A negative scalar local minimum in the strict compatible box must have
positive threshold loss, even if its windows miss middle vertex levels. -/
theorem thresholdLoss_pos_at_negative_localMin (a b c : ℝ) (p : Levels)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hp : ∀ i, p.1 i ≤ p.2 i)
    (hcompat : ∀ i, 0 < (1-direction a b c (i+1))*p.1 i-direction a b c i*p.2 (i+1)+
      direction a b c i*direction a b c (i+1))
    (hmin : IsLocalMin (CyclicDescentSymmetry.jointMargin a b c) p)
    (hneg : CyclicDescentSymmetry.jointMargin a b c p < 0)
    (hd : 0 < SixTriangleResidual.deficit p.1 p.2) :
    0 < thresholdLoss a b c p.1 p.2 := by
  by_contra hn
  have hw := weighted_bounds_of_thresholdLoss_nonpos a b c p.1 p.2 ha hb hc (le_of_not_gt hn)
  have hargs := CyclicVertexDescent.refundArguments_neg_of_weighted_bounds a b c p.1 p.2 ha hb hc
    (fun t ht => CyclicVertexDescent.strictCompatible_of_endpoint_bounds a b c p.1 p.2 t
      ha hb hc hcompat ht) hp hw
  have hmiddle := CyclicDescentSymmetry.middle_windows_of_isLocalMin a b c p.1 p.2 ha hb hc hargs hmin
  have hs := CyclicSixTermCompensation.positive_part_of_no_losses a b c p.1 p.2 ha hb hc hmiddle hw
  change (max 0 (SixTriangleResidual.deficit p.1 p.2))^2 ≤ _ at hs
  rw [max_eq_right hd.le] at hs
  dsimp [CyclicDescentSymmetry.jointMargin,CyclicVertexDescent.margin] at hneg
  linarith only [hs,hneg]

/-- A counterexample to the original ABC area bound supplies a negative scalar
local minimum with positive threshold loss and strict physical/compatibility
inequalities. The reduction ranges over all positions and widths. -/
theorem critical_minimum_of_not_sqPos (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) (hfail : ¬ Quant.SqPos C) :
    ∃ p ∈ levelDomain, IsLocalMin (CyclicDescentSymmetry.jointMargin (1-a) b c) p ∧
      CyclicDescentSymmetry.jointMargin (1-a) b c p < 0 ∧
      0 < thresholdLoss (1-a) b c p.1 p.2 ∧
      0 < SixTriangleResidual.deficit p.1 p.2 ∧
      (∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1) ∧
      (∀ i, 0 < (1-direction (1-a) b c (i+1))*p.1 i-direction (1-a) b c i*p.2 (i+1)+
        direction (1-a) b c i*direction (1-a) b c (i+1)) := by
  classical
  have hbad : ∃ z ∈ RowDeletion.triangle C.deficit, z ∈ CyclicArea.badSeeds C b a c := by
    by_contra hn
    exact hfail (CyclicArea.sqPos_of_no_bad_seed C hb ha hc hu₀ hu₁ hu₂
      (fun z hz hh => hn ⟨z,hz,hh⟩))
  obtain ⟨z,hz,hzbad⟩ := hbad
  let p : Levels := (lowerLevels C c,upperLevels C c)
  have hlevels := levels_internal_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hzbad
  have hr := CyclicGeometry.widths_pos_of_bad C hb ha hc hzbad
  have horder := CyclicExteriorAssembly.lowerLevels_lt_upperLevels C c (fun i => sub_pos.mp (hr i))
  have hp : p ∈ levelDomain :=
    ⟨⟨⟨fun i => (hlevels i).1.le,fun i => ((horder i).trans (hlevels i).2).le⟩,
      ⟨fun i => ((hlevels i).1.trans (horder i)).le,fun i => (hlevels i).2.le⟩⟩,
      fun i => (horder i).le⟩
  have harea : area (1-a) b c p = C.gapArea := by
    rw [Config.gapArea,CyclicExteriorAssembly.configuration_uncovered C hu₀ hu₁ hu₂]
    rfl
  have hdef : SixTriangleResidual.deficit p.1 p.2 = C.deficit :=
    (CyclicSixTermCompensation.deficit_eq_window_deficit C hb ha hc hu₀ hu₁ hu₂).symm
  have hn : actualMargin (1-a) b c p < 0 := by
    have hh : C.gapArea < (max 0 C.deficit)^2*(1/2) := lt_of_not_ge hfail
    dsimp only [actualMargin]
    rw [harea,hdef]
    dsimp only [squarePos]
    linarith only [hh]
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  obtain ⟨q,hq,hmin,hneg,hdeficit,hstrict,hcompat⟩ :=
    exists_negative_scalar_localMin (1-a) b c ha' hb hc p hp hn
  have hloss := thresholdLoss_pos_at_negative_localMin (1-a) b c q ha' hb hc hq.2
    hcompat hmin hneg hdeficit
  exact ⟨q,hq,hmin,hneg,hloss,hdeficit,hstrict,hcompat⟩

end Quant.CyclicGapMinimizer
