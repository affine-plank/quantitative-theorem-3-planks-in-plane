/- Three-positive-plank quadrilateral equalities stay strictly inside all supports. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralSupportTripleOriginal

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralTripleInterior
open Plank
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells PlanarEqualityReductions
open CrossedQuadrilateralSupportOriginal
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem strict_endpoints {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1) (he : Equality K f p) :
    ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1 := by
  have hK := genuine_compact hG
  have hc := genuine_convex hG
  have hne : K.Nonempty := by
    obtain ⟨v,_,hbody,_⟩ := hG
    refine ⟨v 0,?_⟩
    rw [hbody]
    exact subset_convexHull ℝ _ (mem_range_self 0)
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; exact zero_lt_one
  have hbounds (i) := positive_window_no_waste_three hK hc hne hV f p hW hnorm
    (fun j => (ho j).le) hR he i (ho i)
  have hface (i : Fin 3) (hfi : p.1 i = 0 ∨ p.2 i = 1) : False := by
    obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form (f i))
    have hw : rangeWidth K (f i) = f i a-f i b := Body.width_eq_of_realisers ha hb hmax hmin
    have hmax' : f i a = 1 := by
      rw [hunit] at hw
      linarith only [hw,(hnorm i a ha).2,(hnorm i b hb).1]
    have hmin' : f i b = 0 := by
      rw [hunit] at hw
      linarith only [hw,(hnorm i a ha).2,(hnorm i b hb).1]
    have hsupport : f i b = p.1 i ∨ f i a = p.2 i := by
      rcases hfi with hl | hh
      · exact Or.inl (hmin'.trans hl.symm)
      · exact Or.inr (hmax'.trans hh.symm)
    have hbudget : budget K f p = (p.2 i-p.1 i)/rangeWidth K (f i)+
        ∑ j : Fin 2, (p.2 (i.succAbove j)-p.1 (i.succAbove j))/rangeWidth K (f (i.succAbove j)) :=
      Fin.sum_univ_succAbove (fun j => (p.2 j-p.1 j)/rangeWidth K (f j)) i
    have hu : (⋃ j, {x | p.1 j ≤ f j x ∧ f j x ≤ p.2 j}) =
        {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∪
          ⋃ j : Fin 2, {x | p.1 (i.succAbove j) ≤ f (i.succAbove j) x ∧
            f (i.succAbove j) x ≤ p.2 (i.succAbove j)} := by
      ext x
      simp only [mem_iUnion,mem_union,Fin.exists_iff_succAbove i]
    have hs := CrossedQuadrilateralSupportTripleOriginal.support_strict hG hV (f i)
      (fun j => f (i.succAbove j)) a b ha hb hmax hmin (p.1 i) (p.2 i)
      (fun j => p.1 (i.succAbove j)) (fun j => p.2 (i.succAbove j)) hsupport
      (ho i) (fun j => ho (i.succAbove j)) (hW i) (fun j => hW (i.succAbove j)) (by rwa [← hbudget])
    have heq := he
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at heq
    rw [max_eq_right (sub_pos.mpr hR).le,hbudget] at heq
    simp only [gapArea,hu,sub_add_eq_sub_sub] at heq
    linarith only [heq,hs]
  intro i
  exact ⟨lt_of_le_of_ne (hbounds i).1 (fun h => hface i (Or.inl h.symm)),ho i,
    lt_of_le_of_ne (hbounds i).2 (fun h => hface i (Or.inr h))⟩

theorem mem_interior {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1) (he : Equality K f p) :
    p ∈ interior (domain K f) :=
  mem_interior_of_strict K f (strict_endpoints hG hV f p hnorm hunit ho hR he) hR

theorem boundary_zero_window {K : Set Point} (hG : CrossedQuadrilateralGenuine.Genuine K)
    (hV : 0 < (volume K).toReal) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hp : p ∈ domain K f) (hnot : p ∉ interior (domain K f))
    (hR : budget K f p < 1) (he : Equality K f p) : ∃ i, p.1 i = p.2 i := by
  by_contra hn
  apply hnot
  apply mem_interior hG hV f p hnorm hunit _ hR he
  intro i
  exact lt_of_le_of_ne (hp.1 i).2.1 (fun hh => hn ⟨i,hh⟩)

end Quant.CrossedQuadrilateralTripleInterior

/-- info: 'Quant.CrossedQuadrilateralTripleInterior.mem_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralTripleInterior.mem_interior
