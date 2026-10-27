/- Each positive coordinate cut in a triangular enclosure adds at most one vertex. -/
module

public import Plank.Proofs.Quant.PlanarTriangularExtreme

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTriangularSections

open Set MeasureTheory PlanarQuantitative PlanarOnePlankShape PlanarOnePlankVertices PlanarGapCells
open Plank.Convex.PlanarTight TwoPlankClassification

/-- A coordinate section has its upper endpoint on the attained top
edge. The other endpoint is selected as an actual minimum on the section. -/
theorem section_from_top {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ)
    (hinj : ∀ x y : Point, X x = X y → Y x = Y y → x = y)
    (hshape : ∀ x ∈ K, X x+Y x ≤ 1)
    (P : Point) (hP : P ∈ K) (t : ℝ) (hXP : X P = t) (hYP : Y P = 1-t) :
    ∃ a ∈ levelSection K X t, levelSection K X t = segment ℝ a P := by
  let S := levelSection K X t
  have hPS : P ∈ S := ⟨hP,hXP⟩
  have hcpt : IsCompact S := hK.inter_right (isClosed_eq (continuous_form X) continuous_const)
  have hcs : Convex ℝ S := hconv.inter ((convex_singleton t).affine_preimage X)
  obtain ⟨a,ha,hmin⟩ := hcpt.exists_isMinOn ⟨P,hPS⟩ (continuous_form Y).continuousOn
  refine ⟨a,ha,Subset.antisymm ?_ (hcs.segment_subset ha hPS)⟩
  intro x hx
  have hax : Y a ≤ Y x := hmin hx
  have hxp : Y x ≤ Y P := by
    have hh := hshape x hx.1
    rw [hx.2] at hh
    rw [hYP]
    linarith only [hh]
  rcases eq_or_lt_of_le (show Y a ≤ Y P from hmin hPS) with hap | hap
  · have he : x = a := hinj x a (hx.2.trans ha.2.symm)
      (le_antisymm (hxp.trans hap.symm.le) hax)
    rw [he]
    exact left_mem_segment ℝ a P
  · let u := (Y x-Y a)/(Y P-Y a)
    have hgap : 0 < Y P-Y a := sub_pos.mpr hap
    have hu : u ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (sub_nonneg.mpr hax) hgap.le,
        (div_le_one hgap).mpr (by linarith only [hxp])⟩
    have hz : a+u • (P-a) ∈ S := hcs.add_smul_sub_mem ha hPS hu
    have hy : Y (a+u • (P-a)) = Y x := by
      rw [Body.map_add_smul_sub]
      change Y a+((Y x-Y a)/(Y P-Y a))*(Y P-Y a) = Y x
      rw [div_mul_cancel₀ _ hgap.ne',add_sub_cancel]
    have he := hinj (a+u • (P-a)) x (hz.2.trans hx.2.symm) hy
    rw [segment_eq_image' ℝ]
    exact ⟨u,hu,he⟩

/-- A strictly positive level contributes at most one extreme point
apart from the top contact. The endpoint level one is included. -/
theorem one_extreme_per_cut {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ)
    (hinj : ∀ x y : Point, X x = X y → Y x = Y y → x = y)
    (hshape : ∀ x ∈ K, X x+Y x ≤ 1)
    (R T : Point) (hR : R ∈ K) (hT : T ∈ K)
    (hXR : X R = 1) (hYR : Y R = 0) (hXT : X T = 0) (hYT : Y T = 1)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ a ∈ K, ∀ x ∈ K.extremePoints ℝ, X x = t → x = a ∨ x = R := by
  let P := T+t • (R-T)
  have hP : P ∈ K := hconv.add_smul_sub_mem hT hR ⟨ht.le,ht1⟩
  have hXP : X P = t := by simp [P,Body.map_add_smul_sub,hXT,hXR]
  have hYP : Y P = 1-t := by
    simp only [P,Body.map_add_smul_sub,hYT,hYR]
    ring
  obtain ⟨a,ha,hsec⟩ := section_from_top hK hconv X Y hinj hshape P hP t hXP hYP
  refine ⟨a,ha.1,fun x hx hxt => ?_⟩
  have hseg : x ∈ segment ℝ a P := by rw [← hsec]; exact ⟨hx.1,hxt⟩
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxp : x = P
  · by_cases htone : t = 1
    · right
      rw [hxp]
      simp [P,htone]
    · have hop : P ∈ openSegment ℝ T R := by
        rw [openSegment_eq_image']
        exact ⟨t,⟨ht,lt_of_le_of_ne ht1 htone⟩,rfl⟩
      have hh : T = x := hx.2 hT hR (hxp.symm ▸ hop)
      have hzero : t = 0 := hxt.symm.trans ((congrArg X hh).symm.trans hXT)
      exact (ht.ne' hzero).elim
  · have hop : x ∈ openSegment ℝ a P :=
      mem_openSegment_of_ne_left_right (fun he => hxa he.symm) (fun he => hxp he.symm) hseg
    exact Or.inl (hx.2 ha.1 hP hop).symm

/-- Two positive coordinate cuts and the critical corner singletons
give at most four vertices in an independent triangular enclosure. -/
theorem four_of_locations {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (hinj : ∀ x y : Point, X x = X y → Y x = Y y → x = y)
    (hshape : ∀ x ∈ K, X x+Y x ≤ 1)
    (qX qY u : ℝ) (hqX : 0 < qX) (hqX1 : qX ≤ 1)
    (hqY : 0 < qY) (hqY1 : qY ≤ 1) (hu : 0 < u) (hu1 : u < 1)
    (hloc : ∀ x ∈ K.extremePoints ℝ, X x = qX ∨ Y x = qY ∨
      ∃ sx sy, PlanarSingletonCorners.corner K X Y 0 u 0 (1-u) sx sy = {x}) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  classical
  by_cases hf : ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}
  · exact hf
  obtain ⟨R,hR,T,hT,hXR,hYR,hXT,hYT⟩ := PlanarTriangularExtreme.contacts X Y H hshape
  obtain ⟨a,ha,hacut⟩ := one_extreme_per_cut hK hconv X Y hinj hshape R T hR hT
    hXR hYR hXT hYT qX hqX hqX1
  obtain ⟨b,hb,hbcut⟩ := one_extreme_per_cut hK hconv Y X
    (fun x y hy hx => hinj x y hx hy)
    (fun x hx => by simpa only [add_comm] using hshape x hx)
    T R hT hR hYT hXT hYR hXR qY hqY hqY1
  have hex : K.extremePoints ℝ ⊆ ({R,T,a,b} : Set Point) := by
    intro x hx
    rcases hloc x hx with h | h | ⟨sx,sy,hs⟩
    · rcases hacut x hx h with rfl | rfl <;> simp
    · rcases hbcut x hx h with rfl | rfl <;> simp
    · rcases PlanarTriangularExtreme.singleton_extreme hconv X Y H hshape R T hR hT
        hXR hYR hXT hYT u hu hu1 x hx sx sy hs with rfl | rfl | ⟨a,b,d,he⟩
      · simp
      · simp
      · exact (hf ⟨a,b,d,d,by simpa using he⟩).elim
  refine ⟨R,T,a,b,Subset.antisymm ?_ ?_⟩
  · rw [← closure_convexHull_extremePoints hK hconv]
    exact closure_minimal (convexHull_mono hex)
      ((toFinite ({R,T,a,b} : Set Point)).isClosed_convexHull ℝ)
  · apply convexHull_min _ hconv
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption

end Plank.PlanarTriangularSections

/-- info: 'Plank.PlanarTriangularSections.four_of_locations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarTriangularSections.four_of_locations
