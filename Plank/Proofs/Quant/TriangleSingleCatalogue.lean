/- One calibrated band, including tied extrema, in every original triangle. -/
module
public import Plank.Proofs.Quant.TrianglePairAffineCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleSingleCatalogue
open Set MeasureTheory Proofs.Basic Proofs.Transport CommonMiddleNullWindow
open CommonMiddleAffineTransport TriangleCommonExtremeCatalogue TriangleOrientationExhaustion
open TrianglePairCatalogue

theorem halves_union (p : Plank) : (halfLo p).set ∪ (halfHi p).set=p.set := by
  ext z
  constructor
  · rintro (⟨hl,hh⟩ | ⟨hl,hh⟩)
    · exact ⟨hl,by change dot p.u z ≤ (p.lo+p.hi)/2 at hh; linarith [p.lo_le_hi]⟩
    · exact ⟨by change (p.lo+p.hi)/2 ≤ dot p.u z at hl; linarith [p.lo_le_hi],hh⟩
  · intro h
    by_cases hm : dot p.u z ≤ (p.lo+p.hi)/2
    · exact Or.inl ⟨h.1,hm⟩
    · exact Or.inr ⟨le_of_not_ge hm,h.2⟩

theorem halves_stack_iff (T : Triangle) (p : Plank) (hc : CommonExtremes T p)
    (hp : 0 < p.relWidth T) :
    PairOrderedStack T (halfLo p) (halfHi p) ↔
      lower T p=(1-p.relWidth T)*CommonMiddleAffineTransport.slope T p := by
  have hu := upper_eq_lower_add_width T p hc
  simp only [PairOrderedStack,slope_halfLo,slope_halfHi,halfLo_relWidth,halfHi_relWidth,
    lower_halfLo,lower_halfHi,le_refl,true_and]
  constructor
  · rintro (⟨h,_⟩ | ⟨h0,h1⟩)
    · nlinarith only [h]
    · exfalso
      nlinarith only [h0,h1,hu,hp]
  · intro h
    exact Or.inl ⟨by nlinarith only [h],by nlinarith only [h,hu]⟩

theorem ordered_single_iff (p : Plank) (hu : 0 ≤ p.u.2 ∧ p.u.2 ≤ p.u.1)
    (hp : 0 < p.relWidth stdTriangle) (hR : p.relWidth stdTriangle < 1) :
    plankGap p=(1-p.relWidth stdTriangle)^2*(1/2) ↔
      lower stdTriangle p=(1-p.relWidth stdTriangle)*CommonMiddleAffineTransport.slope stdTriangle p := by
  have hs : (halfLo p).relWidth stdTriangle+(halfHi p).relWidth stdTriangle=p.relWidth stdTriangle := by
    rw [halfLo_relWidth,halfHi_relWidth]
    ring
  have he := stack_iff (halfLo p) (halfHi p) hu hu
    (by rw [halfLo_relWidth]; exact half_pos hp) (by rw [halfHi_relWidth]; exact half_pos hp)
    (by rw [hs]; exact hR)
  have hg : pairGap (halfLo p) (halfHi p)=plankGap p := by
    unfold pairGap plankGap
    rw [halves_union]
  rw [hg,hs] at he
  have hc : CommonExtremes stdTriangle p := by simpa [CommonExtremes,stdTriangle,dot] using hu
  exact he.trans (halves_stack_iff stdTriangle p hc hp)

theorem present_single_gap (flip : Bool) (p : Plank) : plankGap (present flip p)=plankGap p := by
  have he := present_gap flip p p
  simpa only [pairGap,plankGap,union_self] using he

/-- A single calibrated position, after optionally exchanging the two
coordinate vertices. The slope may equal zero or one. -/
def NormalizedFamily (p : Plank) : Prop :=
  ∃ flip : Bool, (present flip p).u.2 ≤ (present flip p).u.1 ∧
    lower stdTriangle (present flip p)=(1-p.relWidth stdTriangle)*
      CommonMiddleAffineTransport.slope stdTriangle (present flip p)

theorem normalized_equality_iff (p : Plank) (hu : 0 ≤ p.u.1 ∧ 0 ≤ p.u.2)
    (hp : 0 < p.relWidth stdTriangle) (hR : p.relWidth stdTriangle < 1) :
    plankGap p=(1-p.relWidth stdTriangle)^2*(1/2) ↔ NormalizedFamily p := by
  have hn (f : Bool) : 0 ≤ (present f p).u.2 := by
    cases f
    · exact hu.2
    · exact hu.1
  have he (f : Bool) (hd : (present f p).u.2 ≤ (present f p).u.1) :=
    ordered_single_iff (present f p) ⟨hn f,hd⟩
      (by rw [present_width]; exact hp) (by rw [present_width]; exact hR)
  constructor
  · intro h
    rcases le_total p.u.2 p.u.1 with hd | hd
    · refine ⟨false,hd,?_⟩
      exact (he false hd).mp h
    · refine ⟨true,hd,?_⟩
      have hh := (he true hd).mp (by simpa only [present_single_gap,present_width] using h)
      simpa only [present_width] using hh
  · rintro ⟨f,hd,h⟩
    have hh := (he f hd).mpr (by simpa only [present_width] using h)
    simpa only [present_single_gap,present_width] using hh

theorem single_transport (T : Triangle) (p : Plank) :
    (volume (T.set \ p.set)).toReal=|det3 T.A T.B T.C| * plankGap (pullbackPlank T p) := by
  have he := TrianglePairAffineCatalogue.pair_transport T p p
  simpa only [pairGap,plankGap,union_self] using he

theorem minimum_equality_iff (T : Triangle) (p : Plank) (hu : AtMinimum T p)
    (hp : 0 < p.relWidth T) (hR : p.relWidth T < 1) :
    ((volume (T.set \ p.set)).toReal=(1-p.relWidth T)^2*(volume T.set).toReal) ↔
      NormalizedFamily (TrianglePairAffineCatalogue.normalized T p hu) := by
  have he := normalized_equality_iff (TrianglePairAffineCatalogue.normalized T p hu)
    (TrianglePairAffineCatalogue.normalized_nonneg T p hu)
    (by rw [TrianglePairAffineCatalogue.normalized_width]; exact hp)
    (by rw [TrianglePairAffineCatalogue.normalized_width]; exact hR)
  have hg : plankGap (TrianglePairAffineCatalogue.normalized T p hu)=plankGap (pullbackPlank T p) := by
    simp only [plankGap,TrianglePairAffineCatalogue.normalized_set]
  rw [TrianglePairAffineCatalogue.normalized_width,hg] at he
  rw [← he,single_transport,AffineTransport.area_triangle]
  rw [show (1-p.relWidth T)^2*(|det3 T.A T.B T.C| * (1/2)) =
    |det3 T.A T.B T.C| * ((1-p.relWidth T)^2*(1/2)) by ring]
  have hd : |det3 T.A T.B T.C| ≠ 0 := abs_ne_zero.mpr (det3_ne_zero T)
  exact ⟨mul_left_cancel₀ hd,fun h => congrArg (fun x => |det3 T.A T.B T.C| * x) h⟩

theorem chart_equality_iff (T : Triangle) (p : Plank) (v : Fin 3)
    (hu : AtExtreme (atVertex T v) p) (hp : 0 < p.relWidth T) (hR : p.relWidth T < 1) :
    ((volume (T.set \ p.set)).toReal=(1-p.relWidth T)^2*(volume T.set).toReal) ↔
      NormalizedFamily (TrianglePairAffineCatalogue.atChart T v p hu) := by
  have he := minimum_equality_iff (atVertex T v) (oriented (atVertex T v) p)
    (oriented_minimum _ _ hu)
    (by rw [oriented_width,atVertex_width]; exact hp)
    (by rw [oriented_width,atVertex_width]; exact hR)
  simp only [oriented_width] at he
  simpa only [TrianglePairAffineCatalogue.atChart,oriented_set,atVertex_set,atVertex_width] using he

def Family (T : Triangle) (p : Plank) : Prop :=
  ∃ (v : Fin 3) (h : AtExtreme (atVertex T v) p),
    NormalizedFamily (TrianglePairAffineCatalogue.atChart T v p h)

/-- Every original direction and placement is classified, including all
edge-parallel directions. The affine chart and orientation are constructed. -/
theorem equality_iff_family (T : Triangle) (p : Plank)
    (hp : 0 < p.relWidth T) (hR : p.relWidth T < 1) :
    ((volume (T.set \ p.set)).toReal=(1-p.relWidth T)^2*(volume T.set).toReal) ↔ Family T p := by
  constructor
  · intro he
    obtain ⟨v,hv⟩ := pair_common_extreme T ![p,p]
    exact ⟨v,hv 0,(chart_equality_iff T p v (hv 0) hp hR).mp he⟩
  · rintro ⟨v,hv,hf⟩
    exact (chart_equality_iff T p v hv hp hR).mpr hf

theorem two_null_gap (T : Triangle) (p n m : Plank) (hn : n.lo=n.hi) (hm : m.lo=m.hi) :
    (volume (T.set \ (p.set ∪ n.set ∪ m.set))).toReal=(volume (T.set \ p.set)).toReal := by
  rw [area_remove_null T p n m hm]
  have hs : T.set \ (p.set ∪ n.set)=(T.set \ p.set) \ n.set := by
    ext z
    simp only [mem_sdiff,mem_union]
    tauto
  rw [hs,measure_sdiff_null (volume_plank_set_of_degenerate hn)]

theorem two_null_equality_iff_family (T : Triangle) (p n m : Plank)
    (hp : 0 < p.relWidth T) (hR : p.relWidth T < 1) (hn : n.lo=n.hi) (hm : m.lo=m.hi) :
    ((volume (T.set \ (p.set ∪ n.set ∪ m.set))).toReal =
      (1-(p.relWidth T+n.relWidth T+m.relWidth T))^2*(volume T.set).toReal) ↔ Family T p := by
  rw [two_null_gap T p n m hn hm,null_relWidth T n hn,null_relWidth T m hm,add_zero,add_zero]
  exact equality_iff_family T p hp hR

theorem all_null_equality (T : Triangle) (p n m : Plank)
    (hp : p.lo=p.hi) (hn : n.lo=n.hi) (hm : m.lo=m.hi) :
    (volume (T.set \ (p.set ∪ n.set ∪ m.set))).toReal =
      (1-(p.relWidth T+n.relWidth T+m.relWidth T))^2*(volume T.set).toReal := by
  rw [two_null_gap T p n m hn hm,measure_sdiff_null (volume_plank_set_of_degenerate hp)]
  simp only [null_relWidth T p hp,null_relWidth T n hn,null_relWidth T m hm,zero_add,
    sub_zero,one_pow,one_mul]

end Quant.TriangleSingleCatalogue

/-- info: 'Quant.TriangleSingleCatalogue.equality_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleSingleCatalogue.equality_iff_family

/-- info: 'Quant.TriangleSingleCatalogue.two_null_equality_iff_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleSingleCatalogue.two_null_equality_iff_family
