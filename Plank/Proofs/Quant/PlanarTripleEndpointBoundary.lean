/- Every positive-budget endpoint boundary equality has four body vertices. -/
module

public import Plank.Proofs.Quant.PlanarNullPlankTriple

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTripleEndpointBoundary

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- On the actual normalized support box, any null or support endpoint
reduces a positive-deficit equality triple to the four-point body stratum. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (p : Endpoints 3) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hboundary : ∃ i, p.1 i = 0 ∨ p.1 i = p.2 i ∨ p.2 i = 1) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  have hEq : PlanarAffineEquality.Equality K f p.1 p.2 := by
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal
    rwa [max_eq_right (sub_pos.mpr hR1).le]
  by_cases hz : ∃ i, p.1 i = p.2 i
  · exact PlanarNullPlankTriple.four_vertices hK hconv hne hV f p hW ho hz hR0 hR1 hEq
  have hp (i) : p.1 i < p.2 i := lt_of_le_of_ne (ho i) (fun he => hz ⟨i,he⟩)
  obtain ⟨i,hi⟩ := hboundary
  have hface : p.1 i = 0 ∨ p.2 i = 1 := by
    rcases hi with hi | hi | hi
    · exact Or.inl hi
    · exact (hz ⟨i,hi⟩).elim
    · exact Or.inr hi
  obtain ⟨a,ha,hfa⟩ := hU i
  obtain ⟨b,hb,hfb⟩ := hL i
  have hbudget : budget K f p = (p.2 i-p.1 i)/rangeWidth K (f i)+
      ∑ j : Fin 2, (p.2 (i.succAbove j)-p.1 (i.succAbove j))/rangeWidth K (f (i.succAbove j)) := by
    unfold budget
    rw [Fin.sum_univ_succAbove _ i]
  have hunion : (⋃ j, {x | p.1 j ≤ f j x ∧ f j x ≤ p.2 j}) =
      {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∪
        ⋃ j : Fin 2, {x | p.1 (i.succAbove j) ≤ f (i.succAbove j) x ∧
          f (i.succAbove j) x ≤ p.2 (i.succAbove j)} := by
    ext x
    simp only [mem_iUnion,mem_union,mem_ofPred_eq]
    exact Fin.exists_iff_succAbove i
  apply PlanarOneSupportTripleShape.four_vertices_of_support hK hconv hV (f i)
    (fun j : Fin 2 => f (i.succAbove j)) a b ha hb
    (fun x hx => (hnorm i x hx).2.trans_eq hfa.symm)
    (fun x hx => hfb.trans_le (hnorm i x hx).1)
    (p.1 i) (p.2 i) (fun j => p.1 (i.succAbove j)) (fun j => p.2 (i.succAbove j))
    (by simpa only [hfa,hfb,eq_comm] using hface) (ho i)
    (fun j => ho (i.succAbove j)) (hW i) (fun j => hW (i.succAbove j))
  · rw [Fin.sum_univ_two]
    exact add_pos (div_pos (sub_pos.mpr (hp _)) (hW _))
      (div_pos (sub_pos.mpr (hp _)) (hW _))
  · rwa [← hbudget]
  · change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at hEq
    simpa only [gapArea,hunion,hbudget,sub_add_eq_sub_sub] using hEq

/-- Away from four-point bodies, every normalized positive-deficit
equality has strictly positive widths and strictly interior endpoints. -/
theorem strict_of_not_four {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (p : Endpoints 3) (hp : p ∈ domain K f)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hnf : ¬ ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d}) :
    ∀ i, 0 < p.1 i ∧ p.1 i < p.2 i ∧ p.2 i < 1 := by
  have hn : ¬ ∃ i, p.1 i = 0 ∨ p.1 i = p.2 i ∨ p.2 i = 1 := fun hb =>
    hnf (four_vertices hK hconv hne hV f hW hnorm hL hU p
      (fun i => (hp.1 i).2.1) hR0 hR1 heq hb)
  intro i
  exact ⟨lt_of_le_of_ne (hp.1 i).1 (fun he => hn ⟨i,Or.inl he.symm⟩),
    lt_of_le_of_ne (hp.1 i).2.1 (fun he => hn ⟨i,Or.inr (Or.inl he)⟩),
    lt_of_le_of_ne (hp.1 i).2.2 (fun he => hn ⟨i,Or.inr (Or.inr he)⟩)⟩

end Plank.PlanarTripleEndpointBoundary

/-- info: 'Plank.PlanarTripleEndpointBoundary.strict_of_not_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarTripleEndpointBoundary.strict_of_not_four
