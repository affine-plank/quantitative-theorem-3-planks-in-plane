/- Actual bands, widths, area and triangle witnesses across plane coordinates. -/
module
public import Plank.Proofs.Quant.TriangleGeometricCatalogue
public import Plank.Proofs.Quant.CrossedQuadrilateralSupportTriangle

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.PlanarGeometricCatalogueBridge
open Set MeasureTheory Proofs.Transport
open CrossedQuadrilateralAttainment
open Plank.Convex.DeficientHeightTilt
open Plank.PlanarParameterDomain
open scoped BigOperators

local instance : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure)

def coordinateBody (K : Set (ℝ × ℝ)) : Set (Fin 2 → ℝ) :=
  ParallelProductPlane.coordinates ⁻¹' K

def forms (p : Fin 3 → Plank) : Fin 3 → (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
  fun i => ParallelProductPlane.pullForm (direction (p i).u)

def ends (p : Fin 3 → Plank) : Endpoints 3 := (fun i => (p i).lo,fun i => (p i).hi)

def relativeWidth (K : Set (ℝ × ℝ)) (p : Plank) : ℝ :=
  (p.hi-p.lo)/rangeWidth K (direction p.u)

def actualBudget (K : Set (ℝ × ℝ)) (p : Fin 3 → Plank) : ℝ :=
  ∑ i, relativeWidth K (p i)

def ActualEquality (K : Set (ℝ × ℝ)) (p : Fin 3 → Plank) : Prop :=
  (volume (K \ ⋃ i, (p i).set)).toReal =
    (max 0 (1-actualBudget K p))^2*(volume K).toReal

theorem width_bridge (K : Set (ℝ × ℝ)) (p : Fin 3 → Plank) (i : Fin 3) :
    rangeWidth (coordinateBody K) (forms p i) = rangeWidth K (direction (p i).u) :=
  CrossedQuadrilateralDirections.width_preimage K _

theorem budget_bridge (K : Set (ℝ × ℝ)) (p : Fin 3 → Plank) :
    budget (coordinateBody K) (forms p) (ends p) = actualBudget K p := by
  simp only [budget,ends,width_bridge,actualBudget,relativeWidth]

theorem gap_bridge (K : Set (ℝ × ℝ)) (p : Fin 3 → Plank) :
    gapArea (coordinateBody K) (forms p) (ends p) =
      (volume (K \ ⋃ i, (p i).set)).toReal := by
  unfold gapArea
  rw [← ParallelProductPlane.volume_preimage (K \ ⋃ i, (p i).set)]
  rw [Set.preimage_sdiff,Set.preimage_iUnion]
  rfl

theorem equality_bridge (K : Set (ℝ × ℝ)) (p : Fin 3 → Plank) :
    Plank.PlanarEqualityReductions.Equality (coordinateBody K) (forms p) (ends p) ↔
      ActualEquality K p := by
  unfold Plank.PlanarEqualityReductions.Equality
  rw [gap_bridge,budget_bridge]
  simp only [coordinateBody,ParallelProductPlane.volume_preimage,ActualEquality]

theorem cover_bridge (K : Set (ℝ × ℝ)) (p : Fin 3 → Plank) :
    coordinateBody K ⊆ ⋃ i, {x | (ends p).1 i ≤ forms p i x ∧ forms p i x ≤ (ends p).2 i} ↔
      K ⊆ ⋃ i, (p i).set := by
  have hp : (⋃ i, {x | (ends p).1 i ≤ forms p i x ∧ forms p i x ≤ (ends p).2 i}) =
      ParallelProductPlane.coordinates ⁻¹' (⋃ i, (p i).set) := by
    rw [Set.preimage_iUnion]
    rfl
  rw [hp]
  exact ParallelProductPlane.coordinates.surjective.preimage_subset_preimage_iff

theorem nonempty_of_area {K : Set (ℝ × ℝ)} (hV : 0 < (volume K).toReal) : K.Nonempty := by
  by_contra hn
  rw [Set.not_nonempty_iff_eq_empty.mp hn] at hV
  simpa using hV

theorem coordinate_nonempty {K : Set (ℝ × ℝ)} (hne : K.Nonempty) :
    (coordinateBody K).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨ParallelProductPlane.coordinates.symm x,by simpa [coordinateBody] using hx⟩

theorem width_pos_of_area {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hV : 0 < (volume K).toReal) (p : Plank) : 0 < rangeWidth K (direction p.u) := by
  have hne := nonempty_of_area hV
  obtain ⟨x,hx,y,hy,hmax,hmin⟩ := Plank.Body.exists_realisers hK hne
    (f := direction p.u) (form p.u).continuous
  have he : rangeWidth K (direction p.u) = dot p.u x-dot p.u y :=
    Plank.Body.width_eq_of_realisers hx hy hmax hmin
  have hf : form p.u ≠ 0 := by
    intro hz
    have h1 := congrArg (fun f : (ℝ × ℝ) →L[ℝ] ℝ => f (1,0)) hz
    have h2 := congrArg (fun f : (ℝ × ℝ) →L[ℝ] ℝ => f (0,1)) hz
    apply p.u_ne_zero
    apply Prod.ext
    · simpa [form_apply,dot] using h1
    · simpa [form_apply,dot] using h2
  by_contra hn
  have hd : dot p.u x ≤ dot p.u y := by rw [he] at hn; linarith
  have hs : K ⊆ {z | form p.u z = dot p.u y} := by
    intro z hz
    exact le_antisymm ((hmax z hz).trans hd) (hmin z hz)
  have hz := measure_mono_null hs (Plank.LinearBands.measure_level_zero volume (form p.u) hf _)
  simpa [hz] using hV

theorem budget_nonneg {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hV : 0 < (volume K).toReal) (p : Fin 3 → Plank) : 0 ≤ actualBudget K p := by
  exact Finset.sum_nonneg (fun i _ => div_nonneg (sub_nonneg.mpr (p i).lo_le_hi)
    (width_pos_of_area hK hV (p i)).le)

theorem triangle_range (T : Triangle) (u : ℝ × ℝ) :
    rangeWidth T.set (direction u) = T.width u := by
  have hit (a b c : ℝ) : max a (max b c)=a ∨ max a (max b c)=b ∨ max a (max b c)=c := by
    rcases max_choice a (max b c) with h | h
    · exact Or.inl h
    · rw [h]
      exact Or.inr (max_choice b c)
  have himax : ∃ x ∈ T.set, dot u x=max (dot u T.A) (max (dot u T.B) (dot u T.C)) := by
    rcases hit (dot u T.A) (dot u T.B) (dot u T.C) with h | h | h
    · exact ⟨T.A,mem_A T,h.symm⟩
    · exact ⟨T.B,mem_B T,h.symm⟩
    · exact ⟨T.C,mem_C T,h.symm⟩
  have himin : ∃ x ∈ T.set, dot u x=min (dot u T.A) (min (dot u T.B) (dot u T.C)) := by
    have h := hit (-dot u T.A) (-dot u T.B) (-dot u T.C)
    simp only [max_neg_neg] at h
    rcases h with h | h | h
    · exact ⟨T.A,mem_A T,(neg_injective h).symm⟩
    · exact ⟨T.B,mem_B T,(neg_injective h).symm⟩
    · exact ⟨T.C,mem_C T,(neg_injective h).symm⟩
  obtain ⟨x,hx,hxm⟩ := himax
  obtain ⟨y,hy,hym⟩ := himin
  have he := Plank.Body.width_eq_of_realisers (f := direction u) hx hy
    (fun z hz => by simpa only [direction_apply,hxm] using dot_le_max T u hz)
    (fun z hz => by simpa only [direction_apply,hym] using min_le_dot T u hz)
  change rangeWidth T.set (direction u) = dot u x-dot u y at he
  simpa only [hxm,hym,Triangle.width] using he

theorem triangle_budget (T : Triangle) (p : Fin 3 → Plank) :
    actualBudget T.set p = ∑ i, (p i).relWidth T := by
  simp only [actualBudget,relativeWidth,triangle_range,Plank.relWidth]

theorem triangle_equality (T : Triangle) (p : Fin 3 → Plank) :
    ActualEquality T.set p ↔ TriangleGeometricCatalogue.ActualEquality T p := by
  simp only [ActualEquality,triangle_budget,TriangleGeometricCatalogue.ActualEquality]

theorem triangle_of_three_vertices {K : Set (ℝ × ℝ)} (hV : 0 < (volume K).toReal)
    (a b c : Fin 2 → ℝ) (hbody : coordinateBody K=convexHull ℝ {a,b,c}) :
    ∃ T : Triangle, T.set=K := by
  let C := ParallelProductPlane.coordinates
  have hK : K=convexHull ℝ {C a,C b,C c} := by
    have hi : C '' coordinateBody K=K := Set.image_preimage_eq K C.surjective
    rw [hbody] at hi
    have hm := C.toLinearEquiv.toAffineEquiv.toAffineMap.image_convexHull {a,b,c}
    simpa only [Set.image_insert_eq,Set.image_singleton,
      AffineEquiv.coe_toAffineMap,LinearEquiv.coe_toAffineEquiv,
      ContinuousLinearEquiv.coe_toLinearEquiv] using hi.symm.trans hm
  have hs : affineSpan ℝ ({C a,C b,C c} : Set (ℝ × ℝ))=⊤ := by
    by_contra hn
    have hz := measure_mono_null (convexHull_subset_affineSpan (𝕜 := ℝ) {C a,C b,C c})
      (Measure.addHaar_affineSubspace volume _ hn)
    rw [hK,hz] at hV
    simpa using hV
  have hn : ¬ Collinear ℝ ({C a,C b,C c} : Set (ℝ × ℝ)) := by
    intro h
    have hf := h.finrank_le_one
    rw [AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ (ℝ × ℝ) (ℝ × ℝ) hs] at hf
    norm_num [finrank_top,Module.finrank_prod] at hf
  exact ⟨⟨C a,C b,C c,hn⟩,(set_eq_convexHull _).trans hK.symm⟩

theorem zero_area_equality {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hV : (volume K).toReal=0) (p : Fin 3 → Plank) : ActualEquality K p := by
  unfold ActualEquality
  rw [hV,mul_zero]
  apply le_antisymm
  · have h := ENNReal.toReal_mono (hK.measure_ne_top (μ := volume)) (measure_mono (sdiff_subset :
      K \ ⋃ i, (p i).set ⊆ K))
    simpa [hV] using h
  · exact ENNReal.toReal_nonneg

end Quant.PlanarGeometricCatalogueBridge
