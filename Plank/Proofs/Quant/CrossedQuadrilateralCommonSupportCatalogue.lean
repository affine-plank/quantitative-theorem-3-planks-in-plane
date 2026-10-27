/- The complete calibrated-stack catalogue in a common support-diagonal chart. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonSupport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCommonSupportCatalogue
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralDiagonalSplit
open CrossedQuadrilateralCommonSupport CommonMiddleAffineTransport
open scoped BigOperators

/-- Three adjacent positive pieces of one calibrated diagonal band.
The common coordinate runs from zero at `(-c,0)` to one at `(a,0)`;
its diagonal-intersection value is `c/(a+c)`. -/
def Adjacent (S : Shape) (p : Fin 3 → Plank) : Prop :=
  (∀ i, (p i).u.2 = 0) ∧ ∃ σ : Equiv.Perm (Fin 3),
    lower (half S true) (p (σ 0)) =
      (1-∑ i, relativeWidth S (p i))*(S.c/(S.a+S.c)) ∧
    upper (half S true) (p (σ 0)) = lower (half S true) (p (σ 1)) ∧
    upper (half S true) (p (σ 1)) = lower (half S true) (p (σ 2)) ∧
    upper (half S true) (p (σ 2)) =
      (1-∑ i, relativeWidth S (p i))*(S.c/(S.a+S.c)) + ∑ i, relativeWidth S (p i)

theorem diagonal_slope (S : Shape) (p : Plank) (h : CommonSupports S p)
    (hp : p.u.2 = 0) (j : Bool) : CommonMiddleAffineTransport.slope (half S j) p = S.c/(S.a+S.c) := by
  unfold CommonMiddleAffineTransport.slope
  apply (div_eq_div_iff (span_pos _ _ (h j)).ne' (add_pos S.ha S.hc).ne').mpr
  simp only [span,half,dot,hp,zero_mul,mul_zero,add_zero]
  ring

theorem endpoint_width (S : Shape) (p : Plank) (h : CommonSupports S p) :
    upper (half S true) p - lower (half S true) p = relativeWidth S p := by
  rw [← relativeWidth_half S p h true]
  simp only [upper,lower,Plank.relWidth,width_eq_span _ _ (h true)]
  ring

/-- Both necessity and actual-area sufficiency. The common-support
hypothesis is explicit; no claim about all remaining quadrilateral triples
is hidden in this sector classification. -/
theorem equality_iff_adjacent (S : Shape) (p : Fin 3 → Plank)
    (h : ∀ i, CommonSupports S (p i)) (hw : ∀ i, 0 < relativeWidth S (p i))
    (hR : (∑ i, relativeWidth S (p i)) < 1) :
    (volume (S.body \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, relativeWidth S (p i))^2*(volume S.body).toReal ↔ Adjacent S p := by
  constructor
  · intro he
    have hp := parallel_of_equality S p h hw hR he
    have ht := (equality_iff_orderedStack (half S true) p (fun i => h i true)
      (fun i => by rw [relativeWidth_half S _ (h i)]; exact hw i)
      (by simpa only [relativeWidth_half S _ (h _)] using
        (Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty))
      (by simpa only [relativeWidth_half S _ (h _)] using hR)).mp
        (half_equality S p h hR he true)
    obtain ⟨σ,_,_,hl0,hh0,hl1,hh1,hl2,hh2⟩ := ht
    simp only [diagonal_slope S _ (h _) (hp _),relativeWidth_half S _ (h _)]
      at hl0 hh0 hl1 hh1 hl2 hh2
    exact ⟨hp,σ,hl0,hh0.trans hl1.symm,hh1.trans hl2.symm,hh2⟩
  · rintro ⟨hp,σ,hl0,ha01,ha12,hh2⟩
    have ho (j : Bool) : OrderedStack (half S j) p := by
      refine ⟨σ,?_,?_,?_,?_,?_,?_,?_,?_⟩
      all_goals simp only [diagonal_slope S _ (h _) (hp _),relativeWidth_half S _ (h _)]
      · exact le_rfl
      · exact le_rfl
      · exact hl0
      · change upper (half S true) (p (σ 0)) = _
        linarith only [hl0,endpoint_width S _ (h (σ 0))]
      · change lower (half S true) (p (σ 1)) = _
        linarith only [hl0,ha01,endpoint_width S _ (h (σ 0))]
      · change upper (half S true) (p (σ 1)) = _
        linarith only [hl0,ha01,endpoint_width S _ (h (σ 0)),endpoint_width S _ (h (σ 1))]
      · change lower (half S true) (p (σ 2)) = _
        linarith only [hl0,ha01,ha12,endpoint_width S _ (h (σ 0)),endpoint_width S _ (h (σ 1))]
      · exact hh2
    have he (j : Bool) := equality_of_orderedStack (half S j) p (fun i => h i j)
      (by simpa only [relativeWidth_half S _ (h _)] using hR) (ho j)
    simp only [relativeWidth_half S _ (h _)] at he
    rw [gap_split S _ (MeasurableSet.iUnion
      (fun i => (Proofs.Quant.isClosed_plank_set (p i)).measurableSet)),he false,he true,area_split]
    ring

end Quant.CrossedQuadrilateralCommonSupportCatalogue

/-- info: 'Quant.CrossedQuadrilateralCommonSupportCatalogue.equality_iff_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCommonSupportCatalogue.equality_iff_adjacent
