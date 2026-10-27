/- Exhaustive two-band equality catalogue on arbitrary triangles. -/
module
public import Plank.Proofs.Quant.TrianglePairCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TrianglePairAffineCatalogue
open Set MeasureTheory Proofs.Basic Proofs.Transport CommonMiddleNullWindow
open TriangleCommonExtremeCatalogue TriangleOrientationExhaustion
open TriangleCommonMinimumAffineCatalogue
open scoped BigOperators

theorem pullback_nonneg (T : Triangle) (p : Plank) (h : AtMinimum T p) :
    0 ≤ (pullbackPlank T p).u.1 ∧ 0 ≤ (pullbackPlank T p).u.2 := by
  change 0 ≤ dot p.u (T.B-T.A) ∧ 0 ≤ dot p.u (T.C-T.A)
  rw [dot_sub_right,dot_sub_right]
  exact ⟨sub_nonneg.mpr h.1,sub_nonneg.mpr h.2⟩

def normalized (T : Triangle) (p : Plank) (h : AtMinimum T p) : Plank :=
  TriangleCommonMinimumAffineCatalogue.normalizedPlank (pullbackPlank T p) (pullback_nonneg T p h)

theorem normalized_set (T : Triangle) (p : Plank) (h : AtMinimum T p) :
    (normalized T p h).set=(pullbackPlank T p).set :=
  normalizedPlank_set _ _

theorem normalized_width (T : Triangle) (p : Plank) (h : AtMinimum T p) :
    (normalized T p h).relWidth stdTriangle=p.relWidth T := by
  rw [normalized,normalizedPlank_width,relWidth_pullback]

theorem normalized_nonneg (T : Triangle) (p : Plank) (h : AtMinimum T p) :
    0 ≤ (normalized T p h).u.1 ∧ 0 ≤ (normalized T p h).u.2 :=
  normalizedPlank_nonneg _ _

theorem normalized_max (T : Triangle) (p : Plank) (h : AtMinimum T p) :
    max (normalized T p h).u.1 (normalized T p h).u.2=1 :=
  normalizedPlank_max _ _

theorem duplicate_union (p q : Plank) : (⋃ i : Fin 3, (![p,p,q] i).set)=p.set ∪ q.set := by
  ext z
  constructor
  · intro h
    obtain ⟨i,hi⟩ := mem_iUnion.mp h
    fin_cases i
    exacts [Or.inl hi,Or.inl hi,Or.inr hi]
  · rintro (hp | hq)
    · exact mem_iUnion.mpr ⟨0,hp⟩
    · exact mem_iUnion.mpr ⟨2,hq⟩

theorem duplicate_gap (p q : Plank) : (⟨![p,p,q]⟩ : Config).gapArea=pairGap p q := by
  change (volume (stdTriangle.set \ ⋃ i : Fin 3, (![p,p,q] i).set)).toReal=pairGap p q
  rw [duplicate_union]
  rfl

theorem pair_transport (T : Triangle) (p q : Plank) :
    (volume (T.set \ (p.set ∪ q.set))).toReal =
      |det3 T.A T.B T.C| * pairGap (pullbackPlank T p) (pullbackPlank T q) := by
  have he : AffineTransport.pullbackConfig T ![p,p,q]=
      ⟨![pullbackPlank T p,pullbackPlank T p,pullbackPlank T q]⟩ := by
    unfold AffineTransport.pullbackConfig
    congr 1
    funext i
    fin_cases i <;> rfl
  have hg := AffineTransport.gapArea_transport T ![p,p,q]
  rw [duplicate_union,he,duplicate_gap] at hg
  exact hg

theorem normalized_gap (T : Triangle) (p q : Plank)
    (hp : AtMinimum T p) (hq : AtMinimum T q) :
    pairGap (normalized T p hp) (normalized T q hq)=
      pairGap (pullbackPlank T p) (pullbackPlank T q) := by
  simp only [pairGap,area,normalized_set]

theorem minimum_equality_iff_catalogue (T : Triangle) (p q : Plank)
    (hpu : AtMinimum T p) (hqu : AtMinimum T q)
    (hp : 0 < p.relWidth T) (hq : 0 < q.relWidth T) (hR : p.relWidth T+q.relWidth T < 1) :
    ((volume (T.set \ (p.set ∪ q.set))).toReal =
      (1-(p.relWidth T+q.relWidth T))^2*(volume T.set).toReal) ↔
      TrianglePairCatalogue.Catalogue (normalized T p hpu) (normalized T q hqu) := by
  have he := TrianglePairCatalogue.equality_iff_catalogue (normalized T p hpu) (normalized T q hqu)
    (normalized_nonneg T p hpu) (normalized_nonneg T q hqu)
    (normalized_max T p hpu) (normalized_max T q hqu)
    (by rw [normalized_width]; exact hp) (by rw [normalized_width]; exact hq)
    (by rw [normalized_width,normalized_width]; exact hR)
  rw [normalized_width,normalized_width] at he
  rw [← he,pair_transport,← normalized_gap T p q hpu hqu,AffineTransport.area_triangle]
  rw [show (1-(p.relWidth T+q.relWidth T))^2*(|det3 T.A T.B T.C| * (1/2)) =
    |det3 T.A T.B T.C| * ((1-(p.relWidth T+q.relWidth T))^2*(1/2)) by ring]
  have hd : |det3 T.A T.B T.C| ≠ 0 := abs_ne_zero.mpr (det3_ne_zero T)
  exact ⟨mul_left_cancel₀ hd,fun h => congrArg (fun x => |det3 T.A T.B T.C| * x) h⟩

def atChart (T : Triangle) (v : Fin 3) (p : Plank) (h : AtExtreme (atVertex T v) p) : Plank :=
  normalized (atVertex T v) (oriented (atVertex T v) p) (oriented_minimum _ _ h)

theorem atChart_width (T : Triangle) (v : Fin 3) (p : Plank)
    (h : AtExtreme (atVertex T v) p) : (atChart T v p h).relWidth stdTriangle=p.relWidth T := by
  rw [atChart,normalized_width,oriented_width,atVertex_width]

theorem chart_equality_iff_catalogue (T : Triangle) (p q : Plank) (v : Fin 3)
    (hpu : AtExtreme (atVertex T v) p) (hqu : AtExtreme (atVertex T v) q)
    (hp : 0 < p.relWidth T) (hq : 0 < q.relWidth T) (hR : p.relWidth T+q.relWidth T < 1) :
    ((volume (T.set \ (p.set ∪ q.set))).toReal =
      (1-(p.relWidth T+q.relWidth T))^2*(volume T.set).toReal) ↔
      TrianglePairCatalogue.Catalogue (atChart T v p hpu) (atChart T v q hqu) := by
  have he := minimum_equality_iff_catalogue (atVertex T v)
    (oriented (atVertex T v) p) (oriented (atVertex T v) q)
    (oriented_minimum _ _ hpu) (oriented_minimum _ _ hqu)
    (by rw [oriented_width,atVertex_width]; exact hp)
    (by rw [oriented_width,atVertex_width]; exact hq)
    (by rw [oriented_width,oriented_width,atVertex_width,atVertex_width]; exact hR)
  simp only [oriented_width] at he
  simpa only [atChart,oriented_set,atVertex_set,atVertex_width] using he

/-- Two explicit geometric templates after a constructed affine chart,
independent orientations, and optional reflection. No area condition occurs. -/
def Catalogue (T : Triangle) (p q : Plank) : Prop :=
  ∃ (v : Fin 3) (hp : AtExtreme (atVertex T v) p) (hq : AtExtreme (atVertex T v) q),
    TrianglePairCatalogue.Catalogue (atChart T v p hp) (atChart T v q hq)

theorem equality_iff_catalogue (T : Triangle) (p q : Plank)
    (hp : 0 < p.relWidth T) (hq : 0 < q.relWidth T) (hR : p.relWidth T+q.relWidth T < 1) :
    ((volume (T.set \ (p.set ∪ q.set))).toReal =
      (1-(p.relWidth T+q.relWidth T))^2*(volume T.set).toReal) ↔ Catalogue T p q := by
  constructor
  · intro he
    obtain ⟨v,hv⟩ := pair_common_extreme T ![p,q]
    exact ⟨v,hv 0,hv 1,(chart_equality_iff_catalogue T p q v (hv 0) (hv 1) hp hq hR).mp he⟩
  · rintro ⟨v,hvp,hvq,hf⟩
    exact (chart_equality_iff_catalogue T p q v hvp hvq hp hq hR).mpr hf

/-- An arbitrary zero-width third plank imposes no direction or position
constraint. Both active bands retain their original actual relative widths. -/
theorem null_third_equality_iff_catalogue (T : Triangle) (p q n : Plank)
    (hp : 0 < p.relWidth T) (hq : 0 < q.relWidth T) (hn : n.lo=n.hi)
    (hR : p.relWidth T+q.relWidth T < 1) :
    ((volume (T.set \ (p.set ∪ q.set ∪ n.set))).toReal =
      (1-(p.relWidth T+q.relWidth T+n.relWidth T))^2*(volume T.set).toReal) ↔ Catalogue T p q := by
  rw [area_remove_null T p q n hn,null_relWidth T n hn,add_zero]
  exact equality_iff_catalogue T p q hp hq hR

end Quant.TrianglePairAffineCatalogue

/-- info: 'Quant.TrianglePairAffineCatalogue.equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TrianglePairAffineCatalogue.equality_iff_catalogue

/-- info: 'Quant.TrianglePairAffineCatalogue.null_third_equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TrianglePairAffineCatalogue.null_third_equality_iff_catalogue
