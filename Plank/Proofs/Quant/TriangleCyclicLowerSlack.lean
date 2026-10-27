/- A nonpositive lower cyclic slack would duplicate an interior source region. -/
module
public import Plank.Proofs.Quant.TriangleCyclicCornerSurvivors
public import Plank.Proofs.Quant.TriangleCyclicMiddlePayments

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicLowerSlack
open Set CommonVertex OrdinalArea CyclicArea CyclicTranslationEquality
open TriangleEqualityReductions TriangleCyclicCornerAssignments TriangleCyclicCornerLimits
open CyclicBadThresholds CyclicPairAreas CyclicWeightedThresholdGeometry

theorem lower_slack_pos (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    0 < thresholdSlack (1-a) b c (lowerLevels C c) := by
  classical
  by_contra hn
  have hSle := le_of_not_gt hn
  obtain ⟨hc0,hc1,hc2⟩ := TriangleCyclicCalibrations.abc_calibration C hb ha hc
    hu0 hu1 hu2 hp hδ he
  have hr : ∀ i, 0 < widths C i := by
    intro i
    simpa only [Config.relW,Plank.relWidth,
      BalancedArea.abc_width_one C hb ha hc hu0 hu1 hu2,div_one,widths] using hp i
  have hd := CyclicArea.deficit_eq C hb ha hc hu0 hu1 hu2
  let k := 1-a*b
  let v := c+a*(1-c)
  let w := 1-c+b*c
  let D := a*(1-b)*(1-c)-(1-a)*b*c
  let S := thresholdSlack (1-a) b c (lowerLevels C c)
  let T := b*C.deficit+b*widths C 1-(1-b)*widths C 2
  have hk : 0 < k := by
    dsimp [k]
    nlinarith only [mul_lt_mul_of_pos_left hb.2 ha.1,ha.2]
  have hv : 0 < v := add_pos hc.1 (mul_pos ha.1 (sub_pos.mpr hc.2))
  have hw : 0 < w := add_pos (sub_pos.mpr hc.2) (mul_pos hb.1 hc.1)
  have hS : S=D*C.deficit+a*w*widths C 0+(1-c)*k*widths C 1+(1-b)*v*widths C 2 := by
    dsimp only [S,thresholdSlack,lowerLevels]
    rw [hc0.1,hc1.2,hc2.2,hd]
    dsimp [D,k,v,w,k0,k1,k2]
    ring
  have hT : T<C.deficit := by
    have hs := TriangleCyclicCornerSurvivors.upper_ab_switch C hb ha hc hu0 hu1 hu2 hp hδ he
    have hEq : T=(C.plank 0).lo-widths C 2 := by
      rw [hc0.1]
      dsimp [T]
      rw [hd]
      ring
    rwa [hEq]
  have hE : 0 < T-a*b*C.deficit := by
    have hid : S+v*(T-a*b*C.deficit)=
        a*(1-c)*k*C.deficit+a*w*widths C 0+(b*v+(1-c)*k)*widths C 1 := by
      rw [hS]
      dsimp [T,D,k,v,w]
      ring
    have hpos : 0 < a*(1-c)*k*C.deficit+a*w*widths C 0+(b*v+(1-c)*k)*widths C 1 :=
      add_pos (add_pos (mul_pos (mul_pos (mul_pos ha.1 (sub_pos.mpr hc.2)) hk) hδ)
        (mul_pos (mul_pos ha.1 hw) (hr 0)))
        (mul_pos (add_pos (mul_pos hb.1 hv) (mul_pos (sub_pos.mpr hc.2) hk)) (hr 1))
    have hprod : 0 < v*(T-a*b*C.deficit) := by linarith only [hid,hpos,hSle]
    exact pos_of_mul_pos_right hprod hv.le
  let z : ℝ × ℝ := ((T-a*b*C.deficit)/k,a*(C.deficit-T)/k)
  have hz0 : 0 < z.1 := div_pos hE hk
  have hz1 : 0 < z.2 := div_pos (mul_pos ha.1 (sub_pos.mpr hT)) hk
  have hzs : z.1+z.2<C.deficit := by
    have hid : C.deficit-z.1-z.2=(1-a)*(C.deficit-T)/k := by
      dsimp [z]
      field_simp [hk.ne']
      dsimp [k]
      ring
    have hh := div_pos (mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hT)) hk
    linarith only [hid,hh]
  have hxy : z.1+b*z.2=T := by
    dsimp [z]
    field_simp [hk.ne']
    dsimp [k]
    ring
  have hay : a*z.1+z.2=a*C.deficit := by
    dsimp [z]
    field_simp [hk.ne']
    dsimp [k]
    ring
  have hX : threshold C z 0=(1-b)*widths C 2 := by
    have hid : threshold C z 0=b*C.deficit+b*widths C 1-z.1-b*z.2 := by
      dsimp only [threshold,base]
      rw [hu0,hc0.1,hd]
      dsimp [dot]
      ring
    rw [hid]
    dsimp [T] at hxy
    linarith only [hxy]
  have hY : threshold C z 1=a*widths C 0-(1-a)*widths C 2 := by
    have hid : threshold C z 1=a*C.deficit+a*widths C 0-(1-a)*widths C 2-a*z.1-z.2 := by
      dsimp only [threshold,base]
      rw [hu1,hc1.1,hd]
      dsimp [dot]
      ring
    rw [hid]
    linarith only [hay]
  have hW : threshold C z 2= -c*z.1+(1-c)*z.2 := by
    dsimp only [threshold,base]
    rw [hu2,hc2.1]
    dsimp [dot]
    ring
  have hWlo : threshold C z 2 < -((1-c)*widths C 1) := by
    have hid : S=k*(threshold C z 2+(1-c)*widths C 1)+a*w*widths C 0+b*v*widths C 1 := by
      rw [hW,hS]
      dsimp [z]
      field_simp [hk.ne']
      dsimp [T,D,k,v,w]
      ring
    have hpos := add_pos (mul_pos (mul_pos ha.1 hw) (hr 0))
      (mul_pos (mul_pos hb.1 hv) (hr 1))
    have hprod : k*(threshold C z 2+(1-c)*widths C 1)<0 := by
      linarith only [hid,hpos,hSle]
    have hneg := neg_of_mul_neg_right hprod hk.le
    linarith only [hneg]
  have hw0 : threshold C z 2<0 := hWlo.trans (neg_neg_of_pos
    (mul_pos (sub_pos.mpr hc.2) (hr 1)))
  have hwt : threshold C z 2<c*widths C 0-(1-c)*widths C 1 := by
    have ht := mul_pos hc.1 (hr 0)
    linarith only [hWlo,ht]
  obtain ⟨e,j,he0,hex,hj0,hj1,hx,hy,hw'⟩ := inward_box ha hb hc hz0
    (x := (1-b)*widths C 2) (y := a*widths C 0-(1-a)*widths C 2)
    (w := threshold C z 2) (xl := (1-b)*widths C 2)
    (xu := b*widths C 1+(1-b)*widths C 2)
    (yl := -((1-a)*widths C 2)) (yu := a*widths C 0-(1-a)*widths C 2)
    (wl := threshold C z 2-1) (wu := min 0 (c*widths C 0-(1-c)*widths C 1))
    ⟨le_rfl,by have hp' := mul_pos hb.1 (hr 1); linarith only [hp']⟩
    ⟨by have hp' := mul_pos ha.1 (hr 0); linarith only [hp'],le_rfl⟩
    (by have hp' := mul_pos ha.1 (hr 0); linarith only [hp'])
    ⟨by linarith,lt_min hw0 hwt⟩
  let z' : ℝ × ℝ := (z.1-e,z.2+j*e)
  have hz' : 0 < z'.1 ∧ 0 < z'.2 ∧ z'.1+z'.2<C.deficit :=
    ⟨sub_pos.mpr hex,add_pos hz1 (mul_pos hj0 he0),by
      dsimp [z']
      nlinarith only [hzs,mul_pos (sub_pos.mpr hj1) he0]⟩
  have hx' : threshold C z' 0=(1-b)*widths C 2+(1-b*j)*e := by
    rw [← hX]
    dsimp only [threshold,base,z']
    rw [hu0]
    dsimp [dot]
    ring
  have hy' : threshold C z' 1=a*widths C 0-(1-a)*widths C 2+(a-j)*e := by
    rw [← hY]
    dsimp only [threshold,base,z']
    rw [hu1]
    dsimp [dot]
    ring
  have hw'' : threshold C z' 2=threshold C z 2+(c+(1-c)*j)*e := by
    dsimp only [threshold,base,z']
    rw [hu2]
    dsimp [dot]
    ring
  have hs : z'+translations C {2} ∈ exteriorCells C {2} := by
    apply (assignment_iff C b a c hu0 hu1 hu2 z' {2}).mpr
    intro i
    fin_cases i
    · simpa [offset,hx'] using hx.1
    · simpa [offset,hy'] using hy.1
    · simpa [offset,hw''] using hw'.2.trans_le (min_le_left _ _)
  have ht : z'+translations C {0,1,2} ∈ exteriorCells C {0,1,2} := by
    apply (assignment_iff C b a c hu0 hu1 hu2 z' {0,1,2}).mpr
    intro i
    fin_cases i
    · simpa [offset,hx'] using hx.2
    · simpa [offset,hy'] using hy.2
    · simpa [offset,hw''] using hw'.2.trans_le (min_le_right _ _)
  exact (by decide : ({2} : Finset (Fin 3)) ≠ {0,1,2})
    (unique_at_interior C hb ha hc hu0 hu1 hu2 hδ he hz' {2} {0,1,2} hs ht)

end Quant.TriangleCyclicLowerSlack

/-- info: 'Quant.TriangleCyclicLowerSlack.lower_slack_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicLowerSlack.lower_slack_pos
