/- Exhaustive geometric equality catalogue in the strict ABC chart. -/
module
public import Plank.Proofs.Quant.TriangleCyclicSeparation

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicCatalogue
open MeasureTheory OrdinalArea CyclicBadThresholds CyclicThresholdCaps CyclicGapCancellation
open TriangleEqualityReductions CyclicGapMinimizer CyclicEqualityObstruction
open CyclicCevianFamily

/-- Every former regional hypothesis is derived from actual equality. -/
theorem noClipping_of_equality (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    CyclicUnclippedEquality.NoClippingRegion (1-a) b c (lowerLevels C c) (upperLevels C c) := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith only [ha.1]⟩
  have hd := CyclicSixTermCompensation.deficit_eq_window_deficit C hb ha hc hu0 hu1 hu2
  change C.deficit=SixTriangleResidual.deficit (lowerLevels C c) (upperLevels C c) at hd
  have hr (i : Fin 3) : (C.plank i).lo < (C.plank i).hi := by
    have hw := hp i
    simpa only [Config.relW,Plank.relWidth,
      BalancedArea.abc_width_one C hb ha hc hu0 hu1 hu2,div_one,sub_pos] using hw
  obtain ⟨h0,h1,h2⟩ := TriangleEndpointPositions.abc_internal C hb ha hc hu0 hu1 hu2 hp hδ he
  have H : StrictRegion (1-a) b c (lowerLevels C c,upperLevels C c) := by
    refine ⟨?_,TriangleCyclicCompatibility.endpoint_compatible C hb ha hc hu0 hu1 hu2 hp hδ he,
      TriangleCyclicLowerSlack.lower_slack_pos C hb ha hc hu0 hu1 hu2 hp hδ he,
      TriangleCyclicSeparation.upper_slack_neg C hb ha hc hu0 hu1 hu2 hp hδ he,hd ▸ hδ⟩
    intro i
    fin_cases i <;> dsimp [lowerLevels,upperLevels] <;>
      constructor <;> first | linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,hr 0,hr 1,hr 2] | constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,hr 0,hr 1,hr 2]
  have hm : ∀ i, lowerLevels C c i ≤ direction (1-a) b c i ∧
      direction (1-a) b c i ≤ upperLevels C c i := by
    obtain ⟨h0',h1',h2'⟩ := TriangleCyclicStrictVertices.abc_strict_middle C hb ha hc hu0 hu1 hu2 hp hδ he
    intro i
    fin_cases i <;> dsimp [lowerLevels,upperLevels,direction] <;>
      constructor <;> linarith only [h0'.1,h0'.2,h1'.1,h1'.2,h2'.1,h2'.2]
  have hg : C.gapArea=CyclicGapMinimizer.area (1-a) b c (lowerLevels C c,upperLevels C c) := by
    rw [Config.gapArea,CyclicExteriorAssembly.configuration_uncovered C hu0 hu1 hu2]
    rfl
  have he' : actualMargin (1-a) b c (lowerLevels C c,upperLevels C c)=0 := by
    dsimp only [actualMargin,squarePos]
    rw [← hg,← hd,max_eq_right hδ.le]
    rw [Equality,max_eq_right hδ.le] at he
    linarith only [he]
  exact TriangleCyclicMiddlePayments.noClipping_of_separated_equality ha' hb hc
    (lowerLevels C c,upperLevels C c) H hm he'

/-- All strict cyclic equality bands are precisely the calibrated bands
through the cevians of an interior barycentric point, with widths proportional
to its reciprocal coordinates. No clipping or placement premise remains. -/
theorem equality_iff_cevians (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    Equality C ↔ ∃ u v w R : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u+v+w=1 ∧
      1-a=da u v w ∧ b=db u v w ∧ c=dc u v w ∧
      0 < R ∧ R < 1 ∧ lowerLevels C c=lower u v w R ∧ upperLevels C c=upper u v w R := by
  have ha' : 0 < 1-a ∧ 1-a < 1 := ⟨sub_pos.mpr ha.2,by linarith only [ha.1]⟩
  have hd := CyclicSixTermCompensation.deficit_eq_window_deficit C hb ha hc hu0 hu1 hu2
  change C.deficit=SixTriangleResidual.deficit (lowerLevels C c) (upperLevels C c) at hd
  have hg : C.gapArea=(volume (CyclicExteriorAssembly.uncovered (1-a) b c
      (lowerLevels C c) (upperLevels C c))).toReal := by
    rw [Config.gapArea,CyclicExteriorAssembly.configuration_uncovered C hu0 hu1 hu2]
  constructor
  · intro he
    have H := noClipping_of_equality C hb ha hc hu0 hu1 hu2 hp hδ he
    apply (CyclicCevianFamily.equality_iff_cevians ha' hb hc _ _ H (hd ▸ hδ)).mp
    rw [Equality,max_eq_right hδ.le,hg,hd] at he
    simpa only [div_eq_mul_inv,one_mul] using he
  · rintro ⟨u,v,w,R,hu,hv,hw,_,ha'',hb',hc',hR,hR1,hl,hh⟩
    have hd' : C.deficit=1-R := by
      rw [hd,hl,hh]
      have hs := total_width hu hv hw R
      simp only [Fin.sum_univ_three] at hs
      dsimp only [SixTriangleResidual.deficit]
      linarith only [hs]
    rw [Equality,max_eq_right hδ.le,hg,hl,hh,ha'',hb',hc',hd',uncovered_area hu hv hw hR hR1]
    ring

end Quant.TriangleCyclicCatalogue

/-- info: 'Quant.TriangleCyclicCatalogue.equality_iff_cevians' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicCatalogue.equality_iff_cevians
