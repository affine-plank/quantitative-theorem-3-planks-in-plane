/- The critical cover with singleton corners identifies an exact quadrilateral. -/
module

public import Plank.Proofs.Quant.PlanarSingletonCorners
public import Plank.Convex.PlanarTight.QuadrilateralShape

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCriticalQuadrilateral

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts
open PlanarShiftedDomain (deficit)
open Plank.Convex.DeficientHeightTilt
open Plank.Convex.PlanarTight

/-- The quadrilateral enclosure is exact in the original plane. The
attained contacts themselves prove injectivity of the coordinate map, so
no independence assumption on the two directions is required. -/
theorem shape_of_interior {K : Set Point} (hK : Convex ℝ K)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : TwoPlankClassification.Ranges K (f 0) (f 1))
    (l u m v : ℝ) (hn : TwoPlankInterior.Normal K (f 0) (f 1) l u m v) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨g,q,p,_,_,hq,hq1,hp,hp1,_,_,_,_,hshape⟩ := hn
  obtain ⟨⟨L,hL,hXL,hYL⟩,⟨R,hR,hXR,hYR⟩,⟨B,hB,hXB,hYB⟩,⟨T,hT,hXT,hYT⟩⟩ :=
    QuadrilateralShape.contacts K (f 0) (f 1) H q p hq hq1 hp hp1 hshape
  let F : Point →ᵃ[ℝ] Point := AffineMap.pi f
  have hRlin : F.linear (R-L) = ![1,0] := by
    have hh := F.linearMap_vsub R L
    change F.linear (R-L) = F R-F L at hh
    rw [hh]
    ext i
    fin_cases i <;> simp [F,hXL,hYL,hXR,hYR]
  have hBlin : F.linear (B-L) = ![q,-p] := by
    have hh := F.linearMap_vsub B L
    change F.linear (B-L) = F B-F L at hh
    rw [hh]
    ext i
    fin_cases i <;> simp [F,hXL,hYL,hXB,hYB]
  have hsurj : Function.Surjective F.linear := by
    intro z
    refine ⟨(z 0+q*z 1/p) • (R-L)+(-z 1/p) • (B-L),?_⟩
    rw [map_add,map_smul,map_smul,hRlin,hBlin]
    ext i
    fin_cases i <;> simp
    all_goals field_simp
    all_goals ring
  have hinj : Function.Injective F :=
    F.linear_injective_iff.mp (LinearMap.injective_iff_surjective.mpr hsurj)
  let w : Fin 4 → Point := ![L,B,R,T]
  have hw : ∀ i, F (w i) = QuadrilateralShape.vertices q p i := by
    intro i
    fin_cases i <;> ext j <;> fin_cases j <;>
      simp [F,w,QuadrilateralShape.vertices,hXL,hYL,hXB,hYB,hXR,hYR,hXT,hYT]
  have himage : F '' range w = range (QuadrilateralShape.vertices q p) := by
    rw [← range_comp]
    congr 1
    funext i
    exact hw i
  have hKeq : K = convexHull ℝ (range w) := by
    apply Subset.antisymm
    · intro x hx
      have hh : F x ∈ convexHull ℝ (range (QuadrilateralShape.vertices q p)) :=
        QuadrilateralShape.mem_convexHull (F x) q p hp hp1 (hshape x hx)
      rw [← himage,← F.image_convexHull] at hh
      obtain ⟨y,hy,hxy⟩ := hh
      exact hinj hxy ▸ hy
    · apply convexHull_min _ hK
      rintro x ⟨i,rfl⟩
      fin_cases i <;> assumption
  refine ⟨L,B,R,T,?_⟩
  simpa only [w,Matrix.range_cons,Matrix.range_empty,union_empty,singleton_union] using hKeq

/-- If two positive windows collapse simultaneously along an equality
line and all four cells have positive area, the body has exactly the
interior full-cover quadrilateral shape. -/
theorem shape_of_simultaneous_collapse {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : TwoPlankClassification.Ranges K (f 0) (f 1))
    (p z : Endpoints 2) (c : ℝ) (hp : ∀ i, p.1 i < p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hu : ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (hpos : ∀ s, 0 < (volume (signCell K f p.1 p.2 s)).toReal)
    (τ : ℝ) (hτ : 0 < τ) (hz : ∀ i, (p+τ • z).1 i = (p+τ • z).2 i) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨hW0,hW1⟩ := PlanarCriticalNormalForm.rangeWidth_eq_one (f 0) (f 1) H
  have hW : ∀ i, 0 < rangeWidth K (f i) := by
    intro i
    fin_cases i
    · change 0 < rangeWidth K (f 0)
      rw [hW0]
      exact zero_lt_one
    · change 0 < rangeWidth K (f 1)
      rw [hW1]
      exact zero_lt_one
  obtain ⟨hc,hcrit⟩ := PlanarSimultaneousCollapse.critical_cover_and_copies_at
    hK hconv hne hV f hW p z c (fun i => (hp i).le) hR0 hR1 heq hd hu τ hτ hz
  let r : Endpoints 2 := p+(-(c⁻¹)) • z
  change budget K f r = 1 ∧ (∀ i, r.1 i ≤ r.2 i) ∧
    K ⊆ ⋃ i, {x | r.1 i ≤ f i x ∧ f i x ≤ r.2 i} ∧ _ at hcrit
  have hstrict : ∀ i, r.1 i < r.2 i := by
    intro i
    have hzi : p.1 i+τ*z.1 i = p.2 i+τ*z.2 i := hz i
    have hdw : z.2 i-z.1 i < 0 := by nlinarith only [hzi,hp i,hτ]
    have ht : -(c⁻¹) < 0 := neg_neg_of_pos (inv_pos.mpr hc)
    have hprod := mul_pos_of_neg_of_neg ht hdw
    change p.1 i+(-(c⁻¹))*z.1 i < p.2 i+(-(c⁻¹))*z.2 i
    nlinarith only [hprod,hp i]
  have hs : ∀ s, ∃ y : Point, signCell K f r.1 r.2 s = {y} := by
    intro s
    obtain ⟨y,hy,_⟩ := hcrit.2.2.2 s (hpos s)
    exact ⟨y,hy⟩
  exact shape_of_interior hconv f H _ _ _ _
    (PlanarSingletonCorners.interior_of_critical_cover hconv f H r hcrit.1 hstrict
      hcrit.2.2.1 hs)

end Plank.PlanarCriticalQuadrilateral

/-- info: 'Plank.PlanarCriticalQuadrilateral.shape_of_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCriticalQuadrilateral.shape_of_interior
/-- info: 'Plank.PlanarCriticalQuadrilateral.shape_of_simultaneous_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarCriticalQuadrilateral.shape_of_simultaneous_collapse
