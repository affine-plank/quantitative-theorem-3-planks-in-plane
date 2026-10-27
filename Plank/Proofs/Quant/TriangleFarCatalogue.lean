/- Exhaustive families when a unique far-edge band meets mixed maxima. -/
module
public import Plank.Proofs.Quant.TriangleFarReduction
public import Plank.Proofs.Quant.TriangleMixedPairCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleFarCatalogue
open TriangleFarReduction CommonMiddleNullWindow

theorem rescaled_endpoint_iff (l b r t : ℝ) (ht : t < 1) :
    l/(1-t)=b*(1-r/(1-t)) ↔ l=b*(1-t-r) := by
  have hq := (sub_pos.mpr ht).ne'
  constructor
  · intro h
    have hh := congrArg (fun z : ℝ => z*(1-t)) h
    field_simp [hq] at hh
    nlinarith only [hh]
  · intro h
    rw [h]
    field_simp [hq]

/-- In the mixed-maxima common-minimum chart with one far-edge-parallel
band, the complete sharp family consists of that inward far-edge band,
one other inward edge band, and one calibrated transverse band. The
original locations are unrestricted; sharpness forces all displayed
positions. All three actual widths are positive and their sum is <1. -/
theorem equality_iff_families (C : Config) (a b : ℝ)
    (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(1,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔
      (C.plank 2).hi=1 ∧
        ((a=0 ∧ (C.plank 1).lo=0 ∧ (C.plank 0).lo=b*(1-C.relW 2-C.relW 0)) ∨
         (b=0 ∧ (C.plank 0).lo=0 ∧ (C.plank 1).lo=a*(1-C.relW 2-C.relW 1))) := by
  have hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2 := by
    intro i
    fin_cases i
    · change 0 ≤ (C.plank 0).u.1 ∧ 0 ≤ (C.plank 0).u.2
      simpa only [hu0] using And.intro (show (0:ℝ) ≤ 1 by norm_num) hb.1
    · change 0 ≤ (C.plank 1).u.1 ∧ 0 ≤ (C.plank 1).u.2
      simpa only [hu1] using And.intro ha.1 (show (0:ℝ) ≤ 1 by norm_num)
    · simp [hu2]
  have hm : ∀ i : Fin 2, max (C.plank i.castSucc).u.1 (C.plank i.castSucc).u.2=1 := by
    intro i
    fin_cases i
    · change max (C.plank 0).u.1 (C.plank 0).u.2=1
      simp [hu0,max_eq_left hb.2.le]
    · change max (C.plank 1).u.1 (C.plank 1).u.2=1
      simp [hu1,max_eq_right ha.2.le]
  have hn : ∀ i : Fin 2, (C.plank i.castSucc).u.1 ≠ (C.plank i.castSucc).u.2 := by
    intro i
    fin_cases i
    · change (C.plank 0).u.1 ≠ (C.plank 0).u.2
      simpa only [hu0] using ne_of_gt hb.2
    · change (C.plank 1).u.1 ≠ (C.plank 1).u.2
      simpa only [hu1] using ne_of_lt ha.2
  have hd : C.deficit=1-(C.relW 0+C.relW 1+C.relW 2) := by
    simp only [Config.deficit,Config.sumRelW,Fin.sum_univ_three]
  have ht : C.relW 2 < 1 := by linarith only [hδ,hd,hw 0,hw 1]
  have hq : 0 < 1-C.relW 2 := sub_pos.mpr ht
  let p := pulled (C.plank 0) (C.relW 2) ht
  let q := pulled (C.plank 1) (C.relW 2) ht
  have hpr : p.relWidth stdTriangle=C.relW 0/(1-C.relW 2) := pulled_width _ _ _
  have hqr : q.relWidth stdTriangle=C.relW 1/(1-C.relW 2) := pulled_width _ _ _
  have hpair := TriangleMixedPairCatalogue.equality_iff_families p q a b ha hb hu0 hu1
    (by rw [hpr]; exact div_pos (hw 0) hq)
    (by rw [hqr]; exact div_pos (hw 1) hq)
    (by rw [hpr,hqr,← add_div]; apply (div_lt_one hq).mpr; linarith only [hδ,hd])
  rw [hpr,hqr] at hpair
  change pairGap p q=(1-(C.relW 0/(1-C.relW 2)+C.relW 1/(1-C.relW 2)))^2*(1/2) ↔
    ((a=0 ∧ (C.plank 1).lo/(1-C.relW 2)=0 ∧
      (C.plank 0).lo/(1-C.relW 2)=b*(1-C.relW 0/(1-C.relW 2))) ∨
     (b=0 ∧ (C.plank 0).lo/(1-C.relW 2)=0 ∧
      (C.plank 1).lo/(1-C.relW 2)=a*(1-C.relW 1/(1-C.relW 2)))) at hpair
  rw [rescaled_endpoint_iff _ _ _ _ ht,rescaled_endpoint_iff _ _ _ _ ht] at hpair
  simp only [div_eq_zero_iff,hq.ne',or_false] at hpair
  constructor
  · intro he
    have hh := TriangleFarEndpoint.upper_eq_one C hu hu2 (hw 2) hn hδ he
    exact ⟨hh,hpair.mp ((TriangleFarReduction.equality_iff_pulled C
      (fun i => hu i.castSucc) hm hu2 hh hδ ht).mp he)⟩
  · rintro ⟨hh,hfam⟩
    exact (TriangleFarReduction.equality_iff_pulled C
      (fun i => hu i.castSucc) hm hu2 hh hδ ht).mpr (hpair.mpr hfam)

end Quant.TriangleFarCatalogue

/-- info: 'Quant.TriangleFarCatalogue.equality_iff_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleFarCatalogue.equality_iff_families
