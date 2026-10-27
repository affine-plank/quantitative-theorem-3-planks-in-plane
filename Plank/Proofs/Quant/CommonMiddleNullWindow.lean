/- Two common-extreme positive bands and an arbitrary null third line. -/
module
public import Plank.Proofs.Quant.CommonMiddleAffineTransport

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CommonMiddleNullWindow

open Set MeasureTheory CommonMiddleAffineTransport
open scoped BigOperators

def halfLo (p : Plank) : Plank :=
  ⟨p.u,p.lo,(p.lo+p.hi)/2,p.u_ne_zero,by linarith [p.lo_le_hi]⟩

def halfHi (p : Plank) : Plank :=
  ⟨p.u,(p.lo+p.hi)/2,p.hi,p.u_ne_zero,by linarith [p.lo_le_hi]⟩

def splitFamily (p q : Plank) : Fin 3 → Plank := ![halfLo p,halfHi p,q]

theorem halfLo_relWidth (T : Triangle) (p : Plank) :
    (halfLo p).relWidth T = p.relWidth T/2 := by
  unfold Plank.relWidth halfLo
  ring

theorem halfHi_relWidth (T : Triangle) (p : Plank) :
    (halfHi p).relWidth T = p.relWidth T/2 := by
  unfold Plank.relWidth halfHi
  ring

theorem split_sum (T : Triangle) (p q : Plank) :
    (∑ i, (splitFamily p q i).relWidth T) = p.relWidth T+q.relWidth T := by
  simp only [Fin.sum_univ_three,splitFamily,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,halfLo_relWidth,halfHi_relWidth]
  ring

theorem split_union (p q : Plank) :
    (⋃ i, (splitFamily p q i).set) = p.set ∪ q.set := by
  ext x
  constructor
  · intro hh
    obtain ⟨i,hx⟩ := mem_iUnion.mp hh
    fin_cases i
    · change p.lo ≤ dot p.u x ∧ dot p.u x ≤ (p.lo+p.hi)/2 at hx
      exact Or.inl ⟨hx.1, by linarith [hx.2,p.lo_le_hi]⟩
    · change (p.lo+p.hi)/2 ≤ dot p.u x ∧ dot p.u x ≤ p.hi at hx
      exact Or.inl ⟨by linarith [hx.1,p.lo_le_hi],hx.2⟩
    · exact Or.inr hx
  · rintro (hp | hq)
    · by_cases hm : dot p.u x ≤ (p.lo+p.hi)/2
      · exact mem_iUnion.mpr ⟨0,hp.1,hm⟩
      · exact mem_iUnion.mpr ⟨1,le_of_not_ge hm,hp.2⟩
    · exact mem_iUnion.mpr ⟨2,hq⟩

theorem upper_eq_lower_add_width (T : Triangle) (p : Plank) (hp : CommonExtremes T p) :
    upper T p = lower T p+p.relWidth T := by
  rw [upper,lower,Plank.relWidth,width_eq_span T p hp]
  ring

theorem upper_halfLo (T : Triangle) (p : Plank) :
    upper T (halfLo p) = (lower T p+upper T p)/2 := by
  unfold upper lower halfLo span
  ring

theorem lower_halfHi (T : Triangle) (p : Plank) :
    lower T (halfHi p) = (lower T p+upper T p)/2 := by
  unfold upper lower halfHi span
  ring

theorem lower_halfLo (T : Triangle) (p : Plank) : lower T (halfLo p) = lower T p := rfl

theorem upper_halfHi (T : Triangle) (p : Plank) : upper T (halfHi p) = upper T p := rfl

theorem slope_halfLo (T : Triangle) (p : Plank) : slope T (halfLo p) = slope T p := rfl

theorem slope_halfHi (T : Triangle) (p : Plank) : slope T (halfHi p) = slope T p := rfl

/-- The two active orders. Upper endpoints are lower plus relative width. -/
def PairOrderedStack (T : Triangle) (p q : Plank) : Prop :=
  (slope T p ≤ slope T q ∧
    lower T p = (1-(p.relWidth T+q.relWidth T))*slope T p ∧
    lower T q = (1-(p.relWidth T+q.relWidth T))*slope T q+p.relWidth T) ∨
  (slope T q ≤ slope T p ∧
    lower T q = (1-(p.relWidth T+q.relWidth T))*slope T q ∧
    lower T p = (1-(p.relWidth T+q.relWidth T))*slope T p+q.relWidth T)

/-- Splitting a positive band introduces no extra geometric ordering family. -/
theorem pairStack_of_splitStack (T : Triangle) (p q : Plank)
    (hp : CommonExtremes T p) (hrp : 0 < p.relWidth T) (hrq : 0 < q.relWidth T)
    (hs : OrderedStack T (splitFamily p q)) : PairOrderedStack T p q := by
  obtain ⟨σ,h01,h12,hl0,hh0,hl1,hh1,hl2,hh2⟩ := hs
  simp only [split_sum] at hl0 hh0 hl1 hh1 hl2 hh2
  have hu := upper_eq_lower_add_width T p hp
  have hn01 : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have hn02 : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hn12 : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have cases :
      (σ 0=0 ∧ σ 1=1 ∧ σ 2=2) ∨ (σ 0=0 ∧ σ 1=2 ∧ σ 2=1) ∨
      (σ 0=1 ∧ σ 1=0 ∧ σ 2=2) ∨ (σ 0=1 ∧ σ 1=2 ∧ σ 2=0) ∨
      (σ 0=2 ∧ σ 1=0 ∧ σ 2=1) ∨ (σ 0=2 ∧ σ 1=1 ∧ σ 2=0) := by omega
  unfold PairOrderedStack
  rcases cases with ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ |
    ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩
  all_goals
    simp only [h0,h1,h2,splitFamily,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,upper_halfLo,lower_halfHi,
      lower_halfLo,upper_halfHi,slope_halfLo,slope_halfHi,halfLo_relWidth,halfHi_relWidth]
      at h01 h12 hl0 hh0 hl1 hh1 hl2 hh2
    change slope T p ≤ slope T q ∧ _ ∧ _ ∨ slope T q ≤ slope T p ∧ _ ∧ _
  · exact Or.inl ⟨h12,hl0,by linarith only [hl2]⟩
  · exfalso
    linarith only [hu,hl0,hl2,hrq]
  · exfalso
    linarith only [hu,hl0,hl1,hrp]
  · exfalso
    linarith only [hu,hl0,hl2,hrp,hrq]
  · exact Or.inr ⟨h01,hl0,hl1⟩
  · exfalso
    linarith only [hu,hl1,hl2,hrp]

private def reverseOrder : Equiv.Perm (Fin 3) :=
  ⟨![2,0,1],![1,2,0],by intro i; fin_cases i <;> rfl,by intro i; fin_cases i <;> rfl⟩

theorem splitStack_of_pairStack (T : Triangle) (p q : Plank)
    (hp : CommonExtremes T p) (hq : CommonExtremes T q)
    (hs : PairOrderedStack T p q) : OrderedStack T (splitFamily p q) := by
  have hu := upper_eq_lower_add_width T p hp
  have hv := upper_eq_lower_add_width T q hq
  rcases hs with ⟨hord,hpl,hql⟩ | ⟨hord,hql,hpl⟩
  · refine ⟨Equiv.refl _,?_⟩
    simp only [Equiv.refl_apply,split_sum]
    simp only [splitFamily,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons,upper_halfLo,lower_halfHi,lower_halfLo,
      upper_halfHi,slope_halfLo,slope_halfHi,halfLo_relWidth,halfHi_relWidth]
    exact ⟨le_rfl,hord,hpl,by linarith,by linarith,by linarith,by linarith,by linarith⟩
  · refine ⟨reverseOrder,?_⟩
    simp only [split_sum]
    change slope T q ≤ slope T (halfLo p) ∧ slope T (halfLo p) ≤ slope T (halfHi p) ∧ _
    simp only [splitFamily,reverseOrder,Equiv.coe_fn_mk,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,upper_halfLo,lower_halfHi,
      lower_halfLo,upper_halfHi,slope_halfLo,slope_halfHi,halfLo_relWidth]
    exact ⟨hord,le_rfl,hql,by linarith,hpl,by linarith,by linarith,by linarith⟩

theorem null_relWidth (T : Triangle) (n : Plank) (hn : n.lo=n.hi) :
    n.relWidth T = 0 := by simp [Plank.relWidth,hn]

/-- The null line has arbitrary position and direction. -/
theorem area_remove_null (T : Triangle) (p q n : Plank) (hn : n.lo=n.hi) :
    (volume (T.set \ (p.set ∪ q.set ∪ n.set))).toReal =
      (volume (T.set \ (p.set ∪ q.set))).toReal := by
  have hs : T.set \ (p.set ∪ q.set ∪ n.set) = (T.set \ (p.set ∪ q.set)) \ n.set := by
    ext x
    simp only [mem_sdiff,mem_union]
    tauto
  rw [hs,measure_sdiff_null (volume_plank_set_of_degenerate hn)]

/-- Complete active-pair classification on an arbitrary triangle. The third
plank is any null line, with no common-extreme or endpoint-position premise. -/
theorem equality_iff_pairStack (T : Triangle) (p q n : Plank)
    (hp : CommonExtremes T p) (hq : CommonExtremes T q)
    (hrp : 0 < p.relWidth T) (hrq : 0 < q.relWidth T) (hn : n.lo=n.hi)
    (hR1 : p.relWidth T+q.relWidth T < 1) :
    ((volume (T.set \ (p.set ∪ q.set ∪ n.set))).toReal =
      (1-(p.relWidth T+q.relWidth T+n.relWidth T))^2*(volume T.set).toReal) ↔
      PairOrderedStack T p q := by
  have hc : ∀ i, CommonExtremes T (splitFamily p q i) := by
    intro i
    fin_cases i
    exacts [hp,hp,hq]
  have hw : ∀ i, 0 < (splitFamily p q i).relWidth T := by
    intro i
    fin_cases i
    · exact (halfLo_relWidth T p).symm ▸ half_pos hrp
    · exact (halfHi_relWidth T p).symm ▸ half_pos hrp
    · exact hrq
  have he := CommonMiddleAffineTransport.equality_iff_orderedStack T (splitFamily p q) hc hw
    (by rw [split_sum]; exact add_pos hrp hrq) (by rwa [split_sum])
  rw [split_union,split_sum] at he
  rw [area_remove_null T p q n hn,null_relWidth T n hn,add_zero]
  exact he.trans ⟨pairStack_of_splitStack T p q hp hrp hrq,splitStack_of_pairStack T p q hp hq⟩

end Quant.CommonMiddleNullWindow

/-- info: 'Quant.CommonMiddleNullWindow.equality_iff_pairStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CommonMiddleNullWindow.equality_iff_pairStack
