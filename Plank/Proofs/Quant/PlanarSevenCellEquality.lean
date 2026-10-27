/- Shape rigidity for seven positive exterior cells. -/
module

public import Plank.Proofs.Quant.PlanarWindowEulerRigidity
public import Plank.Proofs.Quant.PlanarPositiveCellPersistence
public import Plank.Proofs.Quant.PlanarThreePlank
public import Plank.Proofs.Quant.PlanarPairwiseGapUpper

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenCellEquality

open Set MeasureTheory Filter Topology PlanarQuantitative PlanarGapCells
open PlanarParameterDomain PlanarSevenCellGeometry PlanarSevenCellArea PlanarPairArea
open PlanarBodySectionDensity PlanarDirectionDerivatives
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def path (c r : Fin 3 → ℝ) (t : ℝ) : Endpoints 3 :=
  (fun i => (1-r i)*c i+t*(-r i*c i),
    fun i => c i+(1-c i)*r i+t*(r i*(1-c i)))

theorem path_width (c r : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    (path c r t).2 i-(path c r t).1 i = (1+t)*r i := by
  dsimp [path]
  ring

theorem gap_eq_pair_formula {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (e : Endpoints 3) (horder : ∀ i, e.1 i ≤ e.2 i)
    (hcount : 7 ≤ (positiveCells K f e).card) :
    gapArea K f e = (volume K).toReal-
      ∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+
      pairCoefficient (f 0) (f 1) (hpairs 0 1 (by decide))*(e.2 0-e.1 0)*(e.2 1-e.1 1)+
      pairCoefficient (f 0) (f 2) (hpairs 0 2 (by decide))*(e.2 0-e.1 0)*(e.2 2-e.1 2)+
      pairCoefficient (f 1) (f 2) (hpairs 1 2 (by decide))*(e.2 1-e.1 1)*(e.2 2-e.1 2) := by
  rw [gap_inclusion_exclusion hK f e
    (fun i j hij => pair_subset_of_seven hK.isClosed hconv f e hcount i j hij (hpairs i j hij))
    (triple_empty_of_seven K f hf e hcount)]
  simp only [plank]
  rw [area_pair (f 0) (f 1) _ _ _ _ _ (horder 0) (horder 1),
    area_pair (f 0) (f 2) _ _ _ _ _ (horder 0) (horder 2),
    area_pair (f 1) (f 2) _ _ _ _ _ (horder 1) (horder 2)]
  rfl

/-- Canonical windows in a touching equality inherit the finite-family rigidity. -/
theorem four_vertices_of_pairwise_identity {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (c r : Fin 3 → ℝ) (hc : ∀ i, c i ∈ Icc 0 1)
    (hr0 : ∀ i, 0 < r i) (hR : (∑ i, r i) < 1)
    (hpair : gapArea K f (path c r 0) = (volume K).toReal-
      ∑ i, coveredArea K (f i) ((path c r 0).1 i) ((path c r 0).2 i)+
        PlanarPairwiseGapUpper.pairSum f (path c r 0))
    (heq : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  classical
  have hr1 (i) : r i < 1 :=
    (Finset.single_le_sum (fun j _ => (hr0 j).le) (Finset.mem_univ i)).trans_lt hR
  have hw (i) : (path c r 0).2 i-(path c r 0).1 i = r i := by
    simp only [path_width,add_zero,one_mul]
  have hp (i) : 0 ≤ (path c r 0).1 i ∧
      (path c r 0).1 i ≤ (path c r 0).2 i ∧ (path c r 0).2 i ≤ 1 := by
    refine ⟨?_,sub_nonneg.mp (by rw [hw]; exact (hr0 i).le),?_⟩
    · change 0 ≤ (1-r i)*c i+0*(-r i*c i)
      simpa only [zero_mul,add_zero] using mul_nonneg (sub_pos.mpr (hr1 i)).le (hc i).1
    · change c i+(1-c i)*r i+0*(r i*(1-c i)) ≤ 1
      have h := mul_nonneg (sub_nonneg.mpr (hc i).2) (sub_pos.mpr (hr1 i)).le
      nlinarith only [h]
  have hb : budget K f (path c r 0) = ∑ i, r i := by
    simp only [budget,hunit,div_one,hw]
  have hR0 : 0 < budget K f (path c r 0) := by
    rw [hb]
    exact Finset.sum_pos (fun i _ => hr0 i) Finset.univ_nonempty
  apply PlanarFinitePairwiseBound.four_vertices_of_pairwise_identity hK hconv hne hV f
    hnorm hunit hpairs (path c r 0) hp hR0 (by rwa [hb]) ?_ (by rwa [hb]) 0
      (sub_pos.mp (by rw [hw]; exact hr0 0))
  simpa only [PlanarPairwiseGapUpper.finite_pairSum_eq] using hpair

/-- Seven positive cells give the touching identity, so finite surplus proves rigidity. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (c r : Fin 3 → ℝ) (hc : ∀ i, c i ∈ Icc 0 1)
    (hr0 : ∀ i, 0 < r i) (hR : (∑ i, r i) < 1)
    (hcount : 7 ≤ (positiveCells K f (path c r 0)).card)
    (heq : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  have hf (i) : (f i).linear ≠ 0 := linear_ne_zero_of_rangeWidth_pos hne (f i)
    (by rw [hunit]; norm_num)
  apply four_vertices_of_pairwise_identity hK hconv hne hV f hnorm hunit hpairs c r hc hr0 hR ?_ heq
  apply PlanarPairwiseGapUpper.gap_eq_pair_sum hK f (path c r 0)
    (fun i j hij => pair_subset_of_seven hK.isClosed hconv f (path c r 0) hcount i j hij (hpairs i j hij))
  rw [triple_empty_of_seven K f hf (path c r 0) hcount,measure_empty]

/-- Compatibility endpoint; the section-density argument is no longer needed. -/
theorem four_vertices_of_densities {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (D : ∀ i, BodySectionDensity K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (c r : Fin 3 → ℝ) (hc : ∀ i, c i ∈ Icc 0 1)
    (hr0 : ∀ i, 0 < r i) (hR : (∑ i, r i) < 1)
    (hcount : 7 ≤ (positiveCells K f (path c r 0)).card)
    (heq : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  exact four_vertices hK hconv hne hV f hnorm hunit hpairs c r hc hr0 hR hcount heq


/-- Compatibility endpoint for a transverse finite half-plane body;
the finite surplus argument applies directly to the compact convex body. -/
theorem four_vertices_of_transverse_halfplanes {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal)
    (F : ι → Point →ᵃ[ℝ] ℝ) (C : ι → ℝ) (hrep : K = {x | ∀ j, F j x ≤ C j})
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hbody : ∀ i j, cross (f i) (F j) ≠ 0)
    (c r : Fin 3 → ℝ) (hc : ∀ i, c i ∈ Icc 0 1)
    (hr0 : ∀ i, 0 < r i) (hR : (∑ i, r i) < 1)
    (hcount : 7 ≤ (positiveCells K f (path c r 0)).card)
    (heq : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  exact four_vertices hK hconv hne hV f hnorm hunit hpairs c r hc hr0 hR hcount heq

end Plank.PlanarSevenCellEquality

/-- info: 'Plank.PlanarSevenCellEquality.four_vertices_of_densities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSevenCellEquality.four_vertices_of_densities
/-- info: 'Plank.PlanarSevenCellEquality.four_vertices_of_transverse_halfplanes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSevenCellEquality.four_vertices_of_transverse_halfplanes
