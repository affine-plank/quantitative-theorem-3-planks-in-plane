module
/- The sharp actual-area bound for every strict ABC three-plank configuration. -/
public import Plank.Proofs.Quant.CyclicAnchorMinimum
public import Plank.Proofs.Quant.CyclicGapMinimizer

@[expose] public section
noncomputable section

namespace Quant.CyclicSharpArea

open CyclicGapCancellation CyclicVertexDescent CyclicThresholdCaps
  CyclicWeightedThresholdGeometry CyclicPairAreas CyclicBadThresholds CyclicGapMinimizer

/-- The actual uncovered-area margin is nonnegative throughout the compact
ordered endpoint box. No Bad, coherence, or middle-window premise is imposed
on the original endpoints. -/
theorem actualMargin_nonneg (a b c : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (p : Levels) (hp : p ∈ levelDomain) : 0 ≤ actualMargin a b c p := by
  by_contra hn
  have hneg : actualMargin a b c p < 0 := lt_of_not_ge hn
  obtain ⟨q,hq,hmin,hnq,hδ,hstrict,hcompat⟩ :=
    exists_negative_minimizer a b c ha hb hc p hp hneg
  have hlocal := scalar_isLocalMin_of_actual_minimum a b c q ha hb hc hq hmin hnq
  obtain ⟨z,hz,hbad⟩ := bad_seed_of_negative_margin a b c q hq.2 ha hb hc hnq
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hcoh := CyclicPaidLossGeometry.coherent_refund_exclusions_of_bad
    (config a b c q hq.2) hb ha' hc rfl rfl rfl hz hbad
  have he : 1-(1-a) = a := by ring
  rw [lowerLevels_config,upperLevels_config,he] at hcoh
  have hweak : (∀ i, refundArgument a b c q.1 q.2 i 0 ≤ 0 ∧
      refundArgument a b c q.1 q.2 i 3 ≤ 0) ∨
      (∀ i, refundArgument a b c q.1 q.2 i 1 ≤ 0 ∧
      refundArgument a b c q.1 q.2 i 2 ≤ 0) :=
    hcoh.imp (fun hh i => ⟨(hh i).1.le,(hh i).2.le⟩)
      (fun hh i => ⟨(hh i).1.le,(hh i).2.le⟩)
  have hm := CyclicAnchorMinimum.nonneg_at_localMin a b c q.1 q.2 ha hb hc
    hq.2 (fun i => (hstrict i).1.le) (fun i => (hstrict i).2.2.le)
    hcompat hweak hδ.le hlocal
  have hid := actualMargin_eq_scalar_of_negative a b c q hq.2 ha hb hc hnq
  change actualMargin a b c q = margin a b c q.1 q.2 at hid
  rw [← hid] at hm
  exact (not_lt_of_ge hm) hnq

/-- The full positive-part-square bound for strict ABC directions, with
arbitrary plank widths and positions. -/
theorem sqPos_of_abc (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) : Quant.SqPos C := by
  classical
  by_contra hfail
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
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hn := actualMargin_nonneg (1-a) b c ha' hb hc p hp
  dsimp only [actualMargin] at hn
  rw [harea,hdef] at hn
  apply hfail
  dsimp [Quant.SqPos,squarePos] at hn ⊢
  linarith only [hn]

end Quant.CyclicSharpArea
