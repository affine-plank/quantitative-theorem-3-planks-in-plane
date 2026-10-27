/- The planar two-plank bound uses the same contact cells and area expansion
as the three-plank bound. No two-window covering theorem is needed. -/
module

public import Plank.Proofs.Quant.AntipodalEndpointCells
public import Plank.Proofs.Quant.FiniteDimensionalNormalization
public import Plank.Proofs.Quant.FiniteDimensionalOnePlankCaps
public import Plank.Proofs.Quant.PlanarNonemptyCellCore
public import Plank.Proofs.Quant.PlanarPairAnchorBound

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarTwoPlankCells

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalMinimumCellRank
  FiniteDimensionalInductionBoundary FiniteDimensionalParameterDomain
open scoped BigOperators

/-- Four nonempty exterior cells supply every pair of corner witnesses. -/
theorem corners_of_four (K : Set (Point 1))
    (f : Fin 2 → (Point 1) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin 2))
    (hcount : 4 ≤ (nonemptyCells K f p).card)
    (i j : Fin 2) (hij : i ≠ j) :
    ∀ b c : Bool, ∃ x ∈ K,
      (if b then p.2 i ≤ f i x else f i x ≤ p.1 i) ∧
      (if c then p.2 j ≤ f j x else f j x ≤ p.1 j) := by
  classical
  have hall : nonemptyCells K f p = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hu := Finset.card_le_univ (nonemptyCells K f p)
    norm_num at hu ⊢
    omega
  intro b c
  let s : Finset (Fin 2) := Finset.univ.filter (fun k => if k=i then b else c)
  have hs : (signCell K f p s).Nonempty := by
    have hm : s ∈ nonemptyCells K f p := by rw [hall]; exact Finset.mem_univ _
    simpa only [nonemptyCells,Finset.mem_filter,Finset.mem_univ,true_and] using hm
  obtain ⟨x,hx,hcuts⟩ := hs
  refine ⟨x,hx,?_,?_⟩
  · simpa [s] using hcuts i
  · simpa [s,Ne.symm hij] using hcuts j

/-- The shared finite-family area expansion already proves the sharp bound
whenever all four closed exterior cells are nonempty. -/
theorem bound_of_four_cells {K : Set (Point 1)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin 2 → (Point 1) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1) (p : Endpoints (Fin 2))
    (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (hcount : 4 ≤ (nonemptyCells K f p).card) :
    (1-budget K f p)^2*(volume K).toReal ≤ gapVolume K f p := by
  have ho := strict_windows_of_interior K f hp
  have hcorners := corners_of_four K f p hcount
  have hR0 : 0 < budget K f p := by
    simp only [budget,hunit,div_one]
    exact Finset.sum_pos (fun i _ => sub_pos.mpr (ho i)) Finset.univ_nonempty
  apply PlanarPairAnchorBound.bound_of_pair_corners hK hc hne f hnorm hunit
    p (interior_subset hp).1 hR0 hR hcorners
  intro i j k hij hik hjk
  omega

/-- A selected two-plank minimum has all four exterior cells. Their area
expansion contradicts a root cost below one, for any uncovered volume. -/
theorem sharpBound_two : SharpBound 1 2 := by
  classical
  by_contra hn
  obtain ⟨K,hK,hc,hne,hV,f,hunit,hnorm,p₀,hp₀,hbad⟩ :=
    FiniteDimensionalNormalization.exists_normalized_counterexample hn
  have hW (i) : 0 < Body.width K (f i) := by rw [hunit]; norm_num
  obtain ⟨p,hp,hcost,_,hcount,_⟩ := AntipodalEndpointCells.exists_minimum_contact_counts
    FiniteDimensionalOnePlankCaps.sharpBound_one hK hc hne hV f hW hnorm hp₀
    ((rootCost_lt_one_iff hV f p₀ hp₀.2).mpr hbad)
  have hR := (budget_le_rootCost K f p).trans_lt hcost
  have hbadp := (rootCost_lt_one_iff hV f p (interior_subset hp).2).mp hcost
  rw [max_eq_right (sub_nonneg.mpr (interior_subset hp).2)] at hbadp
  exact hbadp.not_ge (bound_of_four_cells hK hc hne f hnorm hunit p hp hR hcount)

end Plank.PlanarTwoPlankCells

#print axioms Plank.PlanarTwoPlankCells.corners_of_four
#print axioms Plank.PlanarTwoPlankCells.bound_of_four_cells
#print axioms Plank.PlanarTwoPlankCells.sharpBound_two
