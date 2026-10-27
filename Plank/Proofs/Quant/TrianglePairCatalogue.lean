/- Two geometric families exhaust every normalized common-minimum pair. -/
module
public import Plank.Proofs.Quant.TriangleCommonExtremeExhaustion

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TrianglePairCatalogue
open Set MeasureTheory CommonMiddleNullWindow CommonMiddleAffineTransport
open TriangleStrictCommonMinimum
open scoped BigOperators

theorem split_gap (p q : Plank) : (⟨splitFamily p q⟩ : Config).gapArea=pairGap p q := by
  change (volume (stdTriangle.set \ ⋃ i, (splitFamily p q i).set)).toReal=pairGap p q
  rw [split_union]
  rfl

theorem swap_width (p : Plank) : (swapP p).relWidth stdTriangle=p.relWidth stdTriangle :=
  reflected_width (⟨fun _ => p⟩ : Config) 0

theorem swap_gap (p q : Plank) : pairGap (swapP p) (swapP q)=pairGap p q := by
  have hs : reflected (⟨splitFamily p q⟩ : Config)=⟨splitFamily (swapP p) (swapP q)⟩ := by
    unfold reflected
    congr 1
    funext i
    fin_cases i <;> rfl
  have he := (reflected_equiv (⟨splitFamily p q⟩ : Config)).gapArea_eq
  rw [hs,split_gap,split_gap] at he
  exact he.symm

def present (flip : Bool) (p : Plank) : Plank := if flip then swapP p else p

theorem present_width (flip : Bool) (p : Plank) :
    (present flip p).relWidth stdTriangle=p.relWidth stdTriangle := by
  cases flip
  · rfl
  · exact swap_width p

theorem present_gap (flip : Bool) (p q : Plank) :
    pairGap (present flip p) (present flip q)=pairGap p q := by
  cases flip
  · rfl
  · exact swap_gap p q

def StackFamily (p q : Plank) : Prop :=
  p.u.2 ≤ p.u.1 ∧ q.u.2 ≤ q.u.1 ∧ PairOrderedStack stdTriangle p q

def EdgeFamily (p q : Plank) : Prop :=
  ∃ a b : ℝ, (0 ≤ a ∧ a < 1) ∧ (0 ≤ b ∧ b < 1) ∧
    p.u=(1,b) ∧ q.u=(a,1) ∧
    ((a=0 ∧ q.lo=0 ∧ p.lo=b*(1-p.relWidth stdTriangle)) ∨
     (b=0 ∧ p.lo=0 ∧ q.lo=a*(1-q.relWidth stdTriangle)))

/-- Ordered pair, or inward edge band plus one calibrated transverse band;
reflection merely exchanges the two coordinate vertices. -/
def Catalogue (p q : Plank) : Prop :=
  ∃ flip : Bool, StackFamily (present flip p) (present flip q) ∨
    EdgeFamily (present flip p) (present flip q)

theorem stack_iff (p q : Plank) (hpu : 0 ≤ p.u.2 ∧ p.u.2 ≤ p.u.1)
    (hqu : 0 ≤ q.u.2 ∧ q.u.2 ≤ q.u.1)
    (hp : 0 < p.relWidth stdTriangle) (hq : 0 < q.relWidth stdTriangle)
    (hR : p.relWidth stdTriangle+q.relWidth stdTriangle < 1) :
    pairGap p q=(1-(p.relWidth stdTriangle+q.relWidth stdTriangle))^2*(1/2) ↔
      PairOrderedStack stdTriangle p q := by
  have hpc : CommonExtremes stdTriangle p := by simpa [CommonExtremes,stdTriangle,dot] using hpu
  have hqc : CommonExtremes stdTriangle q := by simpa [CommonExtremes,stdTriangle,dot] using hqu
  have hc : ∀ i, CommonExtremes stdTriangle (splitFamily p q i) := by
    intro i
    fin_cases i
    exacts [hpc,hpc,hqc]
  have hw : ∀ i, 0 < (splitFamily p q i).relWidth stdTriangle := by
    intro i
    fin_cases i
    · change 0 < (halfLo p).relWidth stdTriangle
      rw [halfLo_relWidth]
      exact half_pos hp
    · change 0 < (halfHi p).relWidth stdTriangle
      rw [halfHi_relWidth]
      exact half_pos hp
    · exact hq
  have he := CommonMiddleAffineTransport.equality_iff_orderedStack stdTriangle
    (splitFamily p q) hc hw (by rw [split_sum]; exact add_pos hp hq)
    (by rw [split_sum]; exact hR)
  rw [split_union,split_sum,Proofs.Quant.volume_stdTriangle] at he
  norm_num only [ENNReal.toReal_ofReal] at he
  exact he.trans ⟨pairStack_of_splitStack stdTriangle p q hpc hp hq,
    splitStack_of_pairStack stdTriangle p q hpc hqc⟩

theorem mixed_iff (p q : Plank) (hpu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2)
    (hqu : 0 ≤ q.u.1 ∧ 0 ≤ q.u.2) (hpm : max p.u.1 p.u.2=1)
    (hqm : max q.u.1 q.u.2=1) (hpd : p.u.2 < p.u.1) (hqd : q.u.1 < q.u.2)
    (hp : 0 < p.relWidth stdTriangle) (hq : 0 < q.relWidth stdTriangle)
    (hR : p.relWidth stdTriangle+q.relWidth stdTriangle < 1) :
    pairGap p q=(1-(p.relWidth stdTriangle+q.relWidth stdTriangle))^2*(1/2) ↔
      EdgeFamily p q := by
  have hpx : p.u.1=1 := by simpa only [max_eq_left hpd.le] using hpm
  have hqy : q.u.2=1 := by simpa only [max_eq_right hqd.le] using hqm
  have ha : 0 ≤ q.u.1 ∧ q.u.1 < 1 := ⟨hqu.1,by linarith only [hqd,hqy]⟩
  have hb : 0 ≤ p.u.2 ∧ p.u.2 < 1 := ⟨hpu.2,by linarith only [hpd,hpx]⟩
  have hpn : p.u=(1,p.u.2) := Prod.ext hpx rfl
  have hqn : q.u=(q.u.1,1) := Prod.ext rfl hqy
  have he := TriangleMixedPairCatalogue.equality_iff_families p q q.u.1 p.u.2 ha hb hpn hqn hp hq hR
  constructor
  · intro h
    exact ⟨q.u.1,p.u.2,ha,hb,hpn,hqn,he.mp h⟩
  · rintro ⟨a,b,ha',hb',hu,hv,h⟩
    exact (TriangleMixedPairCatalogue.equality_iff_families p q a b ha' hb' hu hv hp hq hR).mpr h

theorem equality_iff_catalogue (p q : Plank) (hpu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2)
    (hqu : 0 ≤ q.u.1 ∧ 0 ≤ q.u.2) (hpm : max p.u.1 p.u.2=1)
    (hqm : max q.u.1 q.u.2=1) (hp : 0 < p.relWidth stdTriangle)
    (hq : 0 < q.relWidth stdTriangle) (hR : p.relWidth stdTriangle+q.relWidth stdTriangle < 1) :
    pairGap p q=(1-(p.relWidth stdTriangle+q.relWidth stdTriangle))^2*(1/2) ↔
      Catalogue p q := by
  have hn (f : Bool) : (0 ≤ (present f p).u.1 ∧ 0 ≤ (present f p).u.2) ∧
      (0 ≤ (present f q).u.1 ∧ 0 ≤ (present f q).u.2) := by
    cases f
    · exact ⟨hpu,hqu⟩
    · exact ⟨⟨hpu.2,hpu.1⟩,⟨hqu.2,hqu.1⟩⟩
  have hm (f : Bool) : max (present f p).u.1 (present f p).u.2=1 ∧
      max (present f q).u.1 (present f q).u.2=1 := by
    cases f
    · exact ⟨hpm,hqm⟩
    · exact ⟨by simpa only [present,Bool.true_eq,if_true,swapP,max_comm] using hpm,
        by simpa only [present,Bool.true_eq,if_true,swapP,max_comm] using hqm⟩
  have hw (f : Bool) : 0 < (present f p).relWidth stdTriangle ∧
      0 < (present f q).relWidth stdTriangle := by
    simpa only [present_width] using And.intro hp hq
  have hr (f : Bool) : (present f p).relWidth stdTriangle+
      (present f q).relWidth stdTriangle < 1 := by simpa only [present_width] using hR
  constructor
  · intro he
    have hs (f : Bool) (hdp : (present f p).u.2 ≤ (present f p).u.1)
        (hdq : (present f q).u.2 ≤ (present f q).u.1) : Catalogue p q := by
      refine ⟨f,Or.inl ⟨hdp,hdq,?_⟩⟩
      apply (stack_iff _ _ ⟨(hn f).1.2,hdp⟩ ⟨(hn f).2.2,hdq⟩ (hw f).1 (hw f).2 (hr f)).mp
      simpa only [present_gap,present_width] using he
    have hx (f : Bool) (hdp : (present f p).u.2 < (present f p).u.1)
        (hdq : (present f q).u.1 < (present f q).u.2) : Catalogue p q := by
      refine ⟨f,Or.inr ?_⟩
      apply (mixed_iff _ _ (hn f).1 (hn f).2 (hm f).1 (hm f).2 hdp hdq
        (hw f).1 (hw f).2 (hr f)).mp
      simpa only [present_gap,present_width] using he
    by_cases hh : p.u.2 ≤ p.u.1 ∧ q.u.2 ≤ q.u.1
    · exact hs false hh.1 hh.2
    by_cases hv : p.u.1 ≤ p.u.2 ∧ q.u.1 ≤ q.u.2
    · exact hs true hv.1 hv.2
    rcases le_total p.u.2 p.u.1 with hpd | hpd
    · have hqd : q.u.1 < q.u.2 := lt_of_not_ge (fun h => hh ⟨hpd,h⟩)
      have hpd' : p.u.2 < p.u.1 := lt_of_not_ge (fun h => hv ⟨h,hqd.le⟩)
      exact hx false hpd' hqd
    · have hqd : q.u.2 < q.u.1 := lt_of_not_ge (fun h => hv ⟨hpd,h⟩)
      have hpd' : p.u.1 < p.u.2 := lt_of_not_ge (fun h => hh ⟨h,hqd.le⟩)
      exact hx true hpd' hqd
  · rintro ⟨f,hf⟩
    have he : pairGap (present f p) (present f q)=
        (1-((present f p).relWidth stdTriangle+(present f q).relWidth stdTriangle))^2*(1/2) := by
      rcases hf with ⟨hdp,hdq,hstack⟩ | ⟨a,b,ha,hb,hu,hv,hedge⟩
      · exact (stack_iff _ _ ⟨(hn f).1.2,hdp⟩ ⟨(hn f).2.2,hdq⟩ (hw f).1 (hw f).2 (hr f)).mpr hstack
      · exact (TriangleMixedPairCatalogue.equality_iff_families _ _ a b ha hb hu hv
          (hw f).1 (hw f).2 (hr f)).mpr hedge
    simpa only [present_gap,present_width] using he

end Quant.TrianglePairCatalogue

/-- info: 'Quant.TrianglePairCatalogue.equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TrianglePairCatalogue.equality_iff_catalogue
