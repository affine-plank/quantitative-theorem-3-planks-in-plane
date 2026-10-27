/- Positive-deficit equality cannot occur in either open cyclic obstruction
box. The actual-area/local-minimum bridge is proved on an open geometric
region; no local-minimum hypothesis is imposed on the final configuration. -/
module

public import Plank.Proofs.Quant.CyclicSharpArea
public import Plank.Proofs.Quant.SixTriangleEquality
public import Plank.Proofs.Quant.TriangleEqualityReductions

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CyclicEqualityObstruction

open MeasureTheory CyclicGapMinimizer CyclicGapCancellation CyclicVertexDescent
  CyclicThresholdCaps CyclicWeightedThresholdGeometry CyclicPairAreas
  CyclicBadThresholds CyclicExactGap CyclicAnchorRemainder

/-- The open region where the exact scalar formula holds locally, without
requiring that any vertex penalty or threshold loss vanish. -/
structure StrictRegion (a b c : ℝ) (p : Levels) : Prop where
  physical : ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1
  compatible_endpoints : ∀ i,
    0 < (1-direction a b c (i+1))*p.1 i-direction a b c i*p.2 (i+1)+
      direction a b c i*direction a b c (i+1)
  lower_slack : 0 < thresholdSlack a b c p.1
  upper_slack : thresholdSlack a b c p.2 < 0
  deficit_pos : 0 < SixTriangleResidual.deficit p.1 p.2

theorem StrictRegion.mem_domain {a b c : ℝ} {p : Levels}
    (H : StrictRegion a b c p) : p ∈ levelDomain :=
  ⟨⟨⟨fun i => (H.physical i).1.le,
    fun i => ((H.physical i).2.1.trans (H.physical i).2.2).le⟩,
    ⟨fun i => ((H.physical i).1.trans (H.physical i).2.1).le,
    fun i => (H.physical i).2.2.le⟩⟩,fun i => (H.physical i).2.1.le⟩

open Filter in
open scoped Topology in
theorem StrictRegion.eventually {a b c : ℝ} {p : Levels}
    (H : StrictRegion a b c p) : ∀ᶠ q : Levels in 𝓝 p, StrictRegion a b c q := by
  have hp (i : Fin 3) : ∀ᶠ q : Levels in 𝓝 p,
      0 < q.1 i ∧ q.1 i < q.2 i ∧ q.2 i < 1 := by
    have hl : ContinuousAt (fun q : Levels => q.1 i) p := by fun_prop
    have hh : ContinuousAt (fun q : Levels => q.2 i) p := by fun_prop
    filter_upwards [hl.eventually_const_lt (H.physical i).1,
      hl.eventually_lt hh (H.physical i).2.1,
      hh.eventually_lt_const (H.physical i).2.2] with q h0 h1 h2
    exact ⟨h0,h1,h2⟩
  have he (i : Fin 3) : ∀ᶠ q : Levels in 𝓝 p,
      0 < (1-direction a b c (i+1))*q.1 i-direction a b c i*q.2 (i+1)+
        direction a b c i*direction a b c (i+1) := by
    have ht : ContinuousAt (fun q : Levels =>
        (1-direction a b c (i+1))*q.1 i-direction a b c i*q.2 (i+1)+
          direction a b c i*direction a b c (i+1)) p := by fun_prop
    exact ht.eventually_const_lt (H.compatible_endpoints i)
  have hl : ContinuousAt (fun q : Levels => thresholdSlack a b c q.1) p := by
    dsimp [thresholdSlack]; fun_prop
  have hh : ContinuousAt (fun q : Levels => thresholdSlack a b c q.2) p := by
    dsimp [thresholdSlack]; fun_prop
  have hd : ContinuousAt (fun q : Levels => SixTriangleResidual.deficit q.1 q.2) p := by
    dsimp [SixTriangleResidual.deficit]; fun_prop
  filter_upwards [eventually_all.mpr hp,eventually_all.mpr he,
    hl.eventually_const_lt H.lower_slack,hh.eventually_lt_const H.upper_slack,
    hd.eventually_const_lt H.deficit_pos] with q hq hcompat hql hqh hδ
  exact ⟨hq,hcompat,hql,hqh,hδ⟩

theorem actualMargin_eq_scalar {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (p : Levels) (H : StrictRegion a b c p) :
    actualMargin a b c p = CyclicDescentSymmetry.jointMargin a b c p := by
  have hwindow (t : Fin 3 → ℝ) (ht : ∀ i, p.1 i ≤ t i ∧ t i ≤ p.2 i) :
      compatible a b c t := by
    intro i
    have hl := mul_le_mul_of_nonneg_left (ht i).1
      (sub_nonneg.mpr (direction_bounds ha hb hc (i+1)).2.le)
    have hh := mul_le_mul_of_nonneg_left (ht (i+1)).2
      (direction_bounds ha hb hc i).1.le
    linarith only [H.compatible_endpoints i,hl,hh]
  have hl := hwindow p.1 (fun i => ⟨le_rfl,(H.physical i).2.1.le⟩)
  have hh := hwindow p.2 (fun i => ⟨(H.physical i).2.1.le,le_rfl⟩)
  have hg := uncovered_area_eq_expression a b c p.1 p.2 ha hb hc
    (fun i => (H.physical i).2.1) (fun i => (H.physical i).1.le)
    (fun i => (H.physical i).2.2.le) hwindow H.lower_slack H.upper_slack
  have he := gapExpression_cancellation a b c p.1 p.2
    (lowerCapSize_nonpos_of_slack_nonneg a b c p.1 ha hb hc hl H.lower_slack.le)
    (capSize_nonpos_of_slack_nonpos a b c p.2 ha hb hc hh H.upper_slack.le)
  dsimp [actualMargin,CyclicGapMinimizer.area,CyclicDescentSymmetry.jointMargin,margin,squarePos]
  rw [max_eq_right H.deficit_pos.le,hg,he]

open Filter in
open scoped Topology in
/-- Actual equality is an ambient scalar minimum here because the sharp
actual-area bound is already proved for every nearby ordered configuration. -/
theorem scalar_isLocalMin_of_equality {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (p : Levels) (H : StrictRegion a b c p) (he : actualMargin a b c p = 0) :
    IsLocalMin (CyclicDescentSymmetry.jointMargin a b c) p := by
  change ∀ᶠ q : Levels in 𝓝 p,
    CyclicDescentSymmetry.jointMargin a b c p ≤ CyclicDescentSymmetry.jointMargin a b c q
  filter_upwards [H.eventually] with q hq
  rw [← actualMargin_eq_scalar ha hb hc p H,he,
    ← actualMargin_eq_scalar ha hb hc q hq]
  exact CyclicSharpArea.actualMargin_nonneg a b c ha hb hc q hq.mem_domain

/-- Coherent open-region equality forces direction balance even when the
vertex and threshold penalties have not been shown to vanish. -/
theorem balanced_of_equality {a b c : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (p : Levels) (H : StrictRegion a b c p)
    (hcoh : (∀ i, refundArgument a b c p.1 p.2 i 0 ≤ 0 ∧
        refundArgument a b c p.1 p.2 i 3 ≤ 0) ∨
      (∀ i, refundArgument a b c p.1 p.2 i 1 ≤ 0 ∧
        refundArgument a b c p.1 p.2 i 2 ≤ 0))
    (he : actualMargin a b c p = 0) : a*b*c = (1-a)*(1-b)*(1-c) := by
  have hm := scalar_isLocalMin_of_equality ha hb hc p H he
  have hid := localMin_margin_eq ha hb hc p.1 p.2 hm
  have hr := CyclicAnchorMinimum.remainder_nonneg a b c p.1 p.2 ha hb hc
    (fun i => (H.physical i).2.1.le) (fun i => (H.physical i).1.le)
    (fun i => (H.physical i).2.2.le) H.compatible_endpoints hcoh
  have hI := SixTriangleAlgebra.imbalance_nonneg ha hb hc
  have he' := actualMargin_eq_scalar ha hb hc p H
  change actualMargin a b c p = margin a b c p.1 p.2 at he'
  have hI0 : SixTriangleAlgebra.imbalance a b c = 0 := by
    nlinarith only [he,he',hid,hr,hI,H.deficit_pos]
  exact (SixTriangleEquality.imbalance_eq_zero_iff ha hb hc).mp hI0

theorem not_bad_of_product_eq {p q r s t u x y z : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : 0 < s) (ht : 0 < t) (hu : 0 < u)
    (he : p*s*t = q*r*u) : ¬ CyclicAssignment.Bad p q r s t u x y z := by
  rintro (⟨hX,hY,hZ⟩ | ⟨hX,hY,hZ⟩)
  · have hqp : q < p := hX.1.trans hX.2
    have hrs : r < s := by linarith only [hY.1,hY.2]
    have hut : u < t := by linarith only [hZ.1,hZ.2]
    have hprod : q*r*u < p*s*t := calc
      _ < p*r*u := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hqp hr) hu
      _ < p*s*u := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hrs hp) hu
      _ < p*s*t := mul_lt_mul_of_pos_left hut (mul_pos hp hs)
    linarith only [he,hprod]
  · have hpq : p < q := hX.1.trans hX.2
    have hsr : s < r := by linarith only [hY.1,hY.2]
    have htu : t < u := by linarith only [hZ.1,hZ.2]
    have hprod : p*s*t < q*r*u := calc
      _ < q*s*t := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hpq hs) ht
      _ < q*r*t := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hsr hq) ht
      _ < q*r*u := mul_lt_mul_of_pos_left htu (mul_pos hq hr)
    linarith only [he,hprod]

theorem not_bad_seed_of_balance (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (he : (1-a)*b*c = a*(1-b)*(1-c)) (z : ℝ × ℝ) :
    z ∉ CyclicArea.badSeeds C b a c := by
  intro hz
  have hr := CyclicGeometry.widths_pos_of_bad C hb ha hc hz
  apply not_bad_of_product_eq (mul_pos hb.1 (hr 1))
    (mul_pos (sub_pos.mpr hb.2) (hr 2)) (mul_pos ha.1 (hr 0))
    (mul_pos (sub_pos.mpr ha.2) (hr 2)) (mul_pos hc.1 (hr 0))
    (mul_pos (sub_pos.mpr hc.2) (hr 1)) (x := CyclicArea.threshold C z 0)
    (y := CyclicArea.threshold C z 1) (z := CyclicArea.threshold C z 2) ?_ hz
  calc
    _ = ((1-a)*b*c)*(OrdinalArea.widths C 0*OrdinalArea.widths C 1*OrdinalArea.widths C 2) := by ring
    _ = (a*(1-b)*(1-c))*(OrdinalArea.widths C 0*OrdinalArea.widths C 1*OrdinalArea.widths C 2) := by rw [he]
    _ = _ := by ring

/-- Every positive-deficit equality configuration is unobstructed. This
excludes all actual Bad boxes, with no clipping or minimum assumptions. -/
theorem equality_has_no_bad_seed (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C) :
    ∀ z ∈ RowDeletion.triangle C.deficit, z ∉ CyclicArea.badSeeds C b a c := by
  intro z hz hbad
  let p : Levels := (lowerLevels C c,upperLevels C c)
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith [ha.1]⟩
  have hi := levels_internal_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hbad
  have hw := CyclicGeometry.widths_pos_of_bad C hb ha hc hbad
  have ho := CyclicExteriorAssembly.lowerLevels_lt_upperLevels C c (fun i => sub_pos.mp (hw i))
  have hq := thresholdSlack_separation_of_bad C hb ha hc hu₀ hu₁ hu₂ hbad
  have hd : SixTriangleResidual.deficit p.1 p.2 = C.deficit :=
    (CyclicSixTermCompensation.deficit_eq_window_deficit C hb ha hc hu₀ hu₁ hu₂).symm
  have H : StrictRegion (1-a) b c p :=
    ⟨fun i => ⟨(hi i).1,ho i,(hi i).2⟩,
      endpoint_compatible_of_bad C hb ha hc hu₀ hu₁ hu₂ hz hbad,
      hq.1,hq.2,hd.symm ▸ hδ⟩
  have hcoh := CyclicPaidLossGeometry.coherent_refund_exclusions_of_bad
    C hb ha hc hu₀ hu₁ hu₂ hz hbad
  have harea : CyclicGapMinimizer.area (1-a) b c p = C.gapArea := by
    rw [Config.gapArea,CyclicExteriorAssembly.configuration_uncovered C hu₀ hu₁ hu₂]
    rfl
  have he0 : actualMargin (1-a) b c p = 0 := by
    dsimp [actualMargin,squarePos]
    rw [harea,hd,he,max_eq_right hδ.le]
    ring
  have hbala := balanced_of_equality ha' hb hc p H
    (hcoh.imp (fun hh i => ⟨(hh i).1.le,(hh i).2.le⟩)
      (fun hh i => ⟨(hh i).1.le,(hh i).2.le⟩)) he0
  have hbal : (1-a)*b*c = a*(1-b)*(1-c) := by
    convert hbala using 1
    ring
  exact not_bad_seed_of_balance C hb ha hc hbal z hbad

/-- A bad deficit seed makes the actual quantitative bound strict. -/
theorem strict_gap_of_bad_seed (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu₀ : (C.plank 0).u = (1,b)) (hu₁ : (C.plank 1).u = (a,1))
    (hu₂ : (C.plank 2).u = (c,c-1)) (hδ : 0 < C.deficit)
    {z : ℝ × ℝ} (hz : z ∈ RowDeletion.triangle C.deficit)
    (hbad : z ∈ CyclicArea.badSeeds C b a c) :
    (max 0 C.deficit)^2*(1/2) < C.gapArea := by
  have hbnd := CyclicSharpArea.sqPos_of_abc C hb ha hc hu₀ hu₁ hu₂
  change (max 0 C.deficit)^2*(1/2) ≤ C.gapArea at hbnd
  apply lt_of_le_of_ne hbnd
  intro he
  exact equality_has_no_bad_seed C hb ha hc hu₀ hu₁ hu₂ hδ he.symm z hz hbad

end Quant.CyclicEqualityObstruction

/-- info: 'Quant.CyclicEqualityObstruction.equality_has_no_bad_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicEqualityObstruction.equality_has_no_bad_seed
/-- info: 'Quant.CyclicEqualityObstruction.strict_gap_of_bad_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicEqualityObstruction.strict_gap_of_bad_seed
