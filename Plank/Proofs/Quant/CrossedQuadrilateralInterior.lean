/- Every two-positive-plank equality on a genuine quadrilateral is interior. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSupportTriangle

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralInterior
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells PlanarEqualityReductions
open Plank.Convex.DeficientHeightTilt

theorem strict_endpoints {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1) (he : Equality K f p) :
    ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1 := by
  have hK := CrossedQuadrilateralSupportOriginal.genuine_compact hG
  have hc := CrossedQuadrilateralSupportOriginal.genuine_convex hG
  have hne : K.Nonempty := by
    obtain ⟨v,_,hbody,_⟩ := hG
    refine ⟨v 0,?_⟩
    rw [hbody]
    exact subset_convexHull ℝ _ (mem_range_self 0)
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; exact zero_lt_one
  have hbounds := CrossedQuadrilateralTwoWindows.no_waste hK hc hne hV f p hW hnorm ho hR he
  have hb : budget K f p = (p.2 0-p.1 0)+(p.2 1-p.1 1) := by
    simp only [budget,Fin.sum_univ_two,hunit,div_one]
  have hu : (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) =
      ({x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪ {x | p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1}) := by
    ext x
    simp only [mem_iUnion,Fin.exists_fin_two,mem_union]
  have harea : (volume (K \ ({x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪
      {x | p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1}))).toReal =
      (1-(p.2 0-p.1 0)-(p.2 1-p.1 1))^2*(volume K).toReal := by
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at he
    rw [max_eq_right (sub_pos.mpr hR).le,hb] at he
    simpa only [gapArea,hu,sub_add_eq_sub_sub] using he
  have hface (i : Fin 2) (hfi : p.1 i = 0 ∨ p.2 i = 1) : False := by
    obtain ⟨a,ha,b,hb',hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form (f i))
    have hw : rangeWidth K (f i) = f i a-f i b := Body.width_eq_of_realisers ha hb' hmax hmin
    have hmax' : f i a = 1 := by
      rw [hunit] at hw
      linarith only [hw,(hnorm i a ha).2,(hnorm i b hb').1]
    have hmin' : f i b = 0 := by
      rw [hunit] at hw
      linarith only [hw,(hnorm i a ha).2,(hnorm i b hb').1]
    have hsupport : f i b = p.1 i ∨ f i a = p.2 i := by
      rcases hfi with hl | hh
      · exact Or.inl (hmin'.trans hl.symm)
      · exact Or.inr (hmax'.trans hh.symm)
    fin_cases i
    · have hh := CrossedQuadrilateralSupportOriginal.support_strict hG hV (f 0) (f 1) a b
        ha hb' hmax hmin (p.1 0) (p.2 0) (p.1 1) (p.2 1) hsupport (ho 0) (ho 1) (hW 0) (hW 1)
        (by simpa only [hunit,div_one,hb] using hR)
      simp only [hunit,div_one] at hh
      linarith only [hh,harea]
    · have hh := CrossedQuadrilateralSupportOriginal.support_strict hG hV (f 1) (f 0) a b
        ha hb' hmax hmin (p.1 1) (p.2 1) (p.1 0) (p.2 0) hsupport (ho 1) (ho 0) (hW 1) (hW 0)
        (by simpa only [hunit,div_one,hb,add_comm] using hR)
      simp only [hunit,div_one,Set.union_comm] at hh
      have heq : (1-(p.2 1-p.1 1)-(p.2 0-p.1 0))^2 =
          (1-(p.2 0-p.1 0)-(p.2 1-p.1 1))^2 := by ring
      rw [heq] at hh
      linarith only [hh,harea]
  intro i
  exact ⟨lt_of_le_of_ne (hbounds i).1 (fun h => hface i (Or.inl h.symm)),ho i,
    lt_of_le_of_ne (hbounds i).2 (fun h => hface i (Or.inr h))⟩

theorem mem_interior {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1) (he : Equality K f p) :
    p ∈ interior (domain K f) :=
  mem_interior_of_strict K f (strict_endpoints hG hV f p hnorm hunit ho hR he) hR

theorem boundary_zero_window {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hp : p ∈ domain K f) (hnot : p ∉ interior (domain K f))
    (hR : budget K f p < 1) (he : Equality K f p) : ∃ i, p.1 i = p.2 i := by
  by_contra hn
  apply hnot
  apply mem_interior hG hV f p hnorm hunit _ hR he
  intro i
  exact lt_of_le_of_ne (hp.1 i).2.1 (fun hh => hn ⟨i,hh⟩)

end Quant.CrossedQuadrilateralInterior

/-- info: 'Quant.CrossedQuadrilateralInterior.mem_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralInterior.mem_interior
