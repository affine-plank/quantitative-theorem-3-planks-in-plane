/- Three distinct directions are strict on a genuine quadrilateral when
all pair overlaps are contained and the triple overlap has zero area. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralFormDirections
public import Plank.Proofs.Quant.PlanarPairwiseGapUpper
public import Plank.Proofs.Quant.PlanarSevenCellEquality
public import Plank.Proofs.Quant.PlanarUnitEulerRigidity
public import Plank.Proofs.Quant.PlanarEqualityReductions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralContainedPairs
open Plank
open Set MeasureTheory Filter Topology PlanarQuantitative PlanarParameterDomain
open PlanarSevenCellArea PlanarSevenCellEquality PlanarPairArea PlanarDirectionDerivatives
open PlanarBodySectionDensity PlanarUnitSectionDensity PlanarPairwiseGapUpper
open PlanarEqualityReductions
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Actual overlap geometry and actual multi-window equality force every
individual canonical window to attain its own square bound. -/
theorem individual_equality_canonical {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (c r : Fin 3 → ℝ) (hcc : ∀ i, c i ∈ Icc 0 1)
    (hr : ∀ i, 0 < r i) (hR : (∑ i, r i) < 1)
    (hcontain : ∀ i j, i ≠ j →
      plank (f i) ((path c r 0).1 i) ((path c r 0).2 i) ∩
        plank (f j) ((path c r 0).1 j) ((path c r 0).2 j) ⊆ K)
    (htriple : volume {x | ∀ i, (path c r 0).1 i ≤ f i x ∧ f i x ≤ (path c r 0).2 i} = 0)
    (heq : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal) :
    ∀ i, (volume (K \ plank (f i) ((path c r 0).1 i) ((path c r 0).2 i))).toReal =
      (1-r i)^2*(volume K).toReal := by
  classical
  let D (i) : UnitSectionDensity K (f i) := Classical.choice
    (exists_unitSectionDensity hK hc hne hV (f i) (hnorm i) (hunit i))
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  let P := pairCoefficient (f 0) (f 1) (hpairs 0 1 (by decide))*r 0*r 1+
    pairCoefficient (f 0) (f 2) (hpairs 0 2 (by decide))*r 0*r 2+
    pairCoefficient (f 1) (f 2) (hpairs 1 2 (by decide))*r 1*r 2
  have ho (t : ℝ) (ht : -1 < t) (i : Fin 3) :
      (path c r t).1 i ≤ (path c r t).2 i := by
    apply sub_nonneg.mp
    rw [path_width]
    exact mul_nonneg (by linarith only [ht]) (hr i).le
  have hscale (t : ℝ) (ht : -1 < t) : pairSum f (path c r t) = (1+t)^2*P := by
    unfold pairSum
    simp only [plank]
    rw [area_pair (f 0) (f 1) (hpairs 0 1 (by decide)) _ _ _ _ (ho t ht 0) (ho t ht 1),
      area_pair (f 0) (f 2) (hpairs 0 2 (by decide)) _ _ _ _ (ho t ht 0) (ho t ht 2),
      area_pair (f 1) (f 2) (hpairs 1 2 (by decide)) _ _ _ _ (ho t ht 1) (ho t ht 2)]
    simp only [path_width]
    dsimp only [P]
    ring
  have hbudget (t : ℝ) : budget K f (path c r t) = (1+t)*(∑ i, r i) := by
    simp only [budget,hunit,div_one,path_width,Finset.mul_sum]
  have hz : PlanarWindowEulerRigidity.margin K f c r P 0 = 0 := by
    have he := gap_eq_pair_sum hK f (path c r 0) hcontain htriple
    rw [he,hscale 0 (by norm_num)] at heq
    change (volume K).toReal-(∑ i, coveredArea K (f i) ((1-r i)*c i+0*(-r i*c i))
      (c i+(1-c i)*r i+0*(r i*(1-c i))))+(1+0)^2*P-
      (volume K).toReal*(1-(1+0)*(∑ i, r i))^2 = 0
    simp only [add_zero,one_mul] at heq ⊢
    rw [mul_comm (volume K).toReal ((1-∑ i, r i)^2)]
    exact sub_eq_zero.mpr heq
  have hmin : IsLocalMin (PlanarWindowEulerRigidity.margin K f c r P) 0 := by
    have ht : ∀ᶠ t : ℝ in 𝓝 0, -1 < t := Ioi_mem_nhds (by norm_num)
    have hb : ∀ᶠ t : ℝ in 𝓝 0, (1+t)*(∑ i, r i) < 1 :=
      (show ContinuousAt (fun t : ℝ => (1+t)*(∑ i, r i)) 0 by fun_prop).eventually_lt_const
        (by simpa only [add_zero,one_mul] using hR)
    filter_upwards [ht,hb] with t ht hb
    rw [hz]
    change 0 ≤ (volume K).toReal-(∑ i, coveredArea K (f i) ((path c r t).1 i) ((path c r t).2 i))+
      (1+t)^2*P-(volume K).toReal*(1-(1+t)*(∑ i, r i))^2
    apply sub_nonneg.mpr
    have hl := PlanarThreePlank.sharpPlanarBound_three K hK hc hne f
      (path c r t).1 (path c r t).2 (ho t ht) hW
    change (max 0 (1-budget K f (path c r t)))^2*(volume K).toReal ≤ gapArea K f (path c r t) at hl
    rw [hbudget,max_eq_right (sub_nonneg.mpr hb.le)] at hl
    have hu := gap_le_pair_sum hK f hpairs (path c r t)
    rw [hscale t ht] at hu
    apply le_trans (b := gapArea K f (path c r t)) ?_ hu
    rw [mul_comm (volume K).toReal]
    exact hl
  intro i
  have hr1 (j) : r j < 1 :=
    (Finset.single_le_sum (fun k _ => (hr k).le) (Finset.mem_univ j)).trans_lt hR
  have hbalance := PlanarUnitEulerRigidity.balance_eq_of_local_min f D c r hcc hr hr1 P hmin hz i
  simpa only [path,zero_mul,add_zero] using
    PlanarUnitWindowRigidity.gap_eq_of_balance_eq hK (D i) (hcc i) (hr i).le (hr1 i) hbalance

/-- Arbitrary ordered endpoints are reduced using actual equality no-waste. -/
theorem individual_equality {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints 3) (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0)
    (heq : Equality K f p) : ∀ i, (volume (K \ plank (f i) (p.1 i) (p.2 i))).toReal =
      (1-(p.2 i-p.1 i)/rangeWidth K (f i))^2*(volume K).toReal := by
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  have he := PlanarEqualityReductions.positive_window_no_waste_three hK hc hne hV f p
    hW hnorm (fun i => (ho i).le) hR heq
  let r (i) := p.2 i-p.1 i
  have hr (i) : 0 < r i := sub_pos.mpr (ho i)
  have hsum : (∑ i, r i) = budget K f p := by simp only [budget,hunit,div_one,r]
  have hr1 (i) : r i < 1 :=
    (Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)).trans_lt (hsum ▸ hR)
  let c (i) := p.1 i/(1-r i)
  have hcanonical (i) := FiniteDimensionalNormalization.canonical_window
    (he i (ho i)).1 (he i (ho i)).2 (hr1 i)
  have hcc (i) : c i ∈ Icc (0 : ℝ) 1 := (hcanonical i).1
  have hp : path c r 0 = p := by
    apply Prod.ext <;> funext i
    · change (1-r i)*c i+0*(-r i*c i) = p.1 i
      simpa only [zero_mul,add_zero] using (hcanonical i).2.1
    · change c i+(1-c i)*r i+0*(r i*(1-c i)) = p.2 i
      simpa only [zero_mul,add_zero] using (hcanonical i).2.2
  have heq' : gapArea K f (path c r 0) = (1-∑ i, r i)^2*(volume K).toReal := by
    rw [hp,hsum]
    change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at heq
    rwa [max_eq_right (sub_pos.mpr hR).le] at heq
  have hi := individual_equality_canonical hK hc hne hV f hnorm hunit hpairs c r hcc hr
    (by rwa [hsum]) (by simpa only [hp] using hcontain) (by simpa only [hp] using htriple) heq'
  intro i
  simpa only [hp,hunit,div_one,r] using hi i


/-- This entire geometric stratum is excluded for three distinct positive
directions on the genuine quadrilateral. Neither a polygon chart for the
windows nor persistence of pair containment is assumed. -/
theorem not_equality (S : CrossedQuadrilateralAttainment.Shape)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ CrossedQuadrilateralFormDirections.body S → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints 3) (ho : ∀ i, p.1 i < p.2 i)
    (hR : budget (CrossedQuadrilateralFormDirections.body S) f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩
      plank (f j) (p.1 j) (p.2 j) ⊆ CrossedQuadrilateralFormDirections.body S)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0) :
    ¬PlanarEqualityReductions.Equality (CrossedQuadrilateralFormDirections.body S) f p := by
  intro he
  have hK := ParallelProductPlane.compact_preimage (CrossedQuadrilateralAttainment.compact_body S)
  have hc := (CrossedQuadrilateralAttainment.convex_body S).linear_preimage
    ParallelProductPlane.coordinates.toLinearMap
  have hne : (CrossedQuadrilateralFormDirections.body S).Nonempty :=
    ⟨ParallelProductPlane.coordinates.symm 0,by simpa using CrossedQuadrilateralAttainment.zero_mem S⟩
  have hV : 0 < (volume (CrossedQuadrilateralFormDirections.body S)).toReal := by
    rw [ParallelProductPlane.volume_preimage]
    exact CrossedQuadrilateralAttainment.area_body_pos S
  have hi := individual_equality hK hc hne hV f hnorm hunit hpairs p ho hR hcontain htriple he
  have hRi (i) : (p.2 i-p.1 i)/rangeWidth (CrossedQuadrilateralFormDirections.body S) (f i) < 1 := by
    rw [hunit,div_one]
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      (sub_pos.mpr (ho j)).le) (Finset.mem_univ i)
    have hsum : (∑ j, (p.2 j-p.1 j)) < 1 := by
      simpa only [budget,hunit,div_one] using hR
    exact hh.trans_lt hsum
  obtain ⟨i,j,hij,hij0⟩ := CrossedQuadrilateralFormDirections.three_tight_have_parallel_pair
    S f p.1 p.2 ho (fun i => by rw [hunit]; norm_num) hRi hi
  exact hpairs i j hij hij0

end Quant.CrossedQuadrilateralContainedPairs

/-- info: 'Quant.CrossedQuadrilateralContainedPairs.not_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralContainedPairs.not_equality
