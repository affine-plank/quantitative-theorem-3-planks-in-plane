/- Exhaustive subcritical equality families on every nondegenerate triangle. -/
module
public import Plank.Proofs.Quant.TriangleCyclicNormalization
public import Plank.Proofs.Quant.TriangleCyclicCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleGeometricCatalogue
open MeasureTheory OrdinalArea CyclicGapCancellation CyclicCevianFamily CyclicBadThresholds
open TriangleCyclicNormalization TriangleOrientationExhaustion
open Set Proofs.Basic Proofs.Transport
open scoped BigOperators

/-- The cyclic family is specified by actual normalized bands and their
geometric parameters. The parameter R is the original total relative width. -/
def CevianFamily (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  TriangleNullableCatalogue.Positive T p ∧
  ∃ (σ : Equiv.Perm (Fin 3)) (b a c : ℝ),
    (0 < b ∧ b < 1) ∧ (0 < a ∧ a < 1) ∧ (0 < c ∧ c < 1) ∧
    ((chartConfig T p σ).plank 0).u=(1,b) ∧
    ((chartConfig T p σ).plank 1).u=(a,1) ∧
    ((chartConfig T p σ).plank 2).u=(c,c-1) ∧
    ∃ u v w R : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u+v+w=1 ∧
      1-a=da u v w ∧ b=db u v w ∧ c=dc u v w ∧
      0 < R ∧ R < 1 ∧ R=(∑ i, (p i).relWidth T) ∧
      lowerLevels (chartConfig T p σ) c=lower u v w R ∧
      upperLevels (chartConfig T p σ) c=upper u v w R

theorem parameter_eq_actual_width (C : Config) {b a c u v w R : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1)) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : lowerLevels C c=lower u v w R) (hh : upperLevels C c=upper u v w R) :
    R=C.sumRelW := by
  have hd := CyclicSixTermCompensation.deficit_eq_window_deficit C hb ha hc hu0 hu1 hu2
  change C.deficit=SixTriangleResidual.deficit (lowerLevels C c) (upperLevels C c) at hd
  rw [hl,hh] at hd
  have hs := total_width hu hv hw R
  simp only [Fin.sum_univ_three] at hs
  dsimp only [Config.deficit,SixTriangleResidual.deficit] at hd
  linarith only [hd,hs]

/-- Every strict cyclic equality on the original triangle is a member of
the cevian family. No assumption on band placement or clipping is required. -/
theorem cevianFamily_of_cyclic_equality (T : Triangle) (p : Fin 3 → Plank)
    (hp : TriangleNullableCatalogue.Positive T p) (hcyc : StrictCyclic T p)
    (hR : (∑ i, (p i).relWidth T) < 1) (he : TriangleNullableCatalogue.Equality T p) :
    CevianFamily T p := by
  obtain ⟨σ,b,a,c,hb,ha,hc,h0,h1,h2⟩ := exists_abc T p hcyc
  have hpos : ∀ i, 0 < (chartConfig T p σ).relW i := by
    intro i
    rw [chartConfig_width]
    exact hp (σ i)
  have hd : 0 < (chartConfig T p σ).deficit := by
    rw [Config.deficit,chartConfig_sum]
    exact sub_pos.mpr hR
  obtain ⟨u,v,w,R,hu,hv,hw,hs,ha',hb',hc',hr,hr1,hl,hh⟩ :=
    (TriangleCyclicCatalogue.equality_iff_cevians _ hb ha hc h0 h1 h2 hpos hd).mp
      ((chartConfig_equality T p σ hR).mp he)
  refine ⟨hp,σ,b,a,c,hb,ha,hc,h0,h1,h2,u,v,w,R,hu,hv,hw,hs,ha',hb',hc',hr,hr1,?_,hl,hh⟩
  rw [← chartConfig_sum T p σ]
  exact parameter_eq_actual_width _ hb ha hc h0 h1 h2 hu hv hw hl hh

/-- Every listed cevian configuration attains the bound for its original
uncovered area and original relative widths. -/
theorem equality_of_cevianFamily (T : Triangle) (p : Fin 3 → Plank)
    (hR : (∑ i, (p i).relWidth T) < 1) (hf : CevianFamily T p) :
    TriangleNullableCatalogue.Equality T p := by
  obtain ⟨hp,σ,b,a,c,hb,ha,hc,h0,h1,h2,u,v,w,R,hu,hv,hw,hs,ha',hb',hc',hr,hr1,_,hl,hh⟩ := hf
  have hpos : ∀ i, 0 < (chartConfig T p σ).relW i := by
    intro i
    rw [chartConfig_width]
    exact hp (σ i)
  have hd : 0 < (chartConfig T p σ).deficit := by
    rw [Config.deficit,chartConfig_sum]
    exact sub_pos.mpr hR
  apply (chartConfig_equality T p σ hR).mpr
  exact (TriangleCyclicCatalogue.equality_iff_cevians _ hb ha hc h0 h1 h2 hpos hd).mpr
    ⟨u,v,w,R,hu,hv,hw,hs,ha',hb',hc',hr,hr1,hl,hh⟩

/-- The complete geometric list: arbitrary null lines; one calibrated
band; either of the two positive-pair families; the four common-extreme
positive families; or the calibrated concurrent-cevian family. -/
def Families (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  TriangleNullableCatalogue.Families T p ∨ CevianFamily T p

/-- Exhaustive equality iff, with no residual directional sector and no
extra placement, clipping, or scalar-stationarity premise. -/
theorem equality_iff_families (T : Triangle) (p : Fin 3 → Plank)
    (hR : (∑ i, (p i).relWidth T) < 1) :
    TriangleNullableCatalogue.Equality T p ↔ Families T p := by
  constructor
  · intro he
    rcases TriangleNullableCatalogue.families_or_strict_cyclic T p hR he with hf | ⟨hp,hc⟩
    · exact Or.inl hf
    · exact Or.inr (cevianFamily_of_cyclic_equality T p hp hc hR he)
  · rintro (hf | hf)
    · exact TriangleNullableCatalogue.equality_of_families T p hR hf
    · exact equality_of_cevianFamily T p hR hf

/-- The quantitative formula with its positive part, for any actual budget. -/
def ActualEquality (T : Triangle) (p : Fin 3 → Plank) : Prop :=
  (volume (T.set \ ⋃ i, (p i).set)).toReal =
    (max 0 (1-∑ i, (p i).relWidth T))^2*(volume T.set).toReal

theorem equality_iff_cover_of_one_le (T : Triangle) (p : Fin 3 → Plank)
    (hR : 1 ≤ ∑ i, (p i).relWidth T) :
    ActualEquality T p ↔ T.set ⊆ ⋃ i, (p i).set := by
  rw [ActualEquality,max_eq_left (sub_nonpos.mpr hR),zero_pow (by decide : 2 ≠ 0),zero_mul]
  have hV : 0 < (volume T.set).toReal := by
    rw [AffineTransport.area_triangle]
    exact mul_pos (abs_pos.mpr (det3_ne_zero T)) (by norm_num)
  have hC : IsClosed (⋃ i, (p i).set) :=
    isClosed_iUnion_of_finite (fun i => Proofs.Quant.isClosed_plank_set (p i))
  have h := Plank.PlanarGapAnalysis.area_sdiff_eq_zero_iff_subset
    (ParallelProductPlane.compact_preimage (Proofs.GapCells.isCompact_triangle T))
    ((convex_triangle T).linear_preimage ParallelProductPlane.coordinates.toLinearMap)
    (by rwa [ParallelProductPlane.volume_preimage])
    (hC.preimage ParallelProductPlane.coordinates.continuous)
  rw [← Set.preimage_sdiff,ParallelProductPlane.volume_preimage] at h
  refine h.trans ⟨?_,?_⟩
  · intro hc z hz
    have hh := hc (show ParallelProductPlane.coordinates.symm z ∈
      ParallelProductPlane.coordinates ⁻¹' T.set by simpa using hz)
    simpa using hh
  · intro hc z hz
    exact hc hz

/-- Exhaustive for every budget: the geometric catalogue below one;
an actual closed cover at or above one. -/
theorem all_budgets_iff (T : Triangle) (p : Fin 3 → Plank) :
    ActualEquality T p ↔
      if (∑ i, (p i).relWidth T) < 1 then Families T p else T.set ⊆ ⋃ i, (p i).set := by
  by_cases hR : (∑ i, (p i).relWidth T) < 1
  · rw [if_pos hR]
    have h := equality_iff_families T p hR
    simpa only [ActualEquality,TriangleNullableCatalogue.Equality,
      max_eq_right (sub_pos.mpr hR).le] using h
  · rw [if_neg hR]
    exact equality_iff_cover_of_one_le T p (le_of_not_gt hR)

end Quant.TriangleGeometricCatalogue

/-- info: 'Quant.TriangleGeometricCatalogue.equality_iff_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleGeometricCatalogue.equality_iff_families

/-- info: 'Quant.TriangleGeometricCatalogue.all_budgets_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleGeometricCatalogue.all_budgets_iff
