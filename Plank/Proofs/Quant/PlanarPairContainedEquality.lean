/- Equality classification from actual pair containment and null triple overlap. -/
module

public import Plank.Proofs.Quant.PlanarPairwiseGapUpper
public import Plank.Proofs.Quant.PlanarSevenCellEquality
public import Plank.Proofs.Quant.PlanarUnitEulerRigidity
public import Plank.Proofs.Quant.PlanarFourPointClassification
public import Plank.Proofs.Quant.PlanarEqualityReductions

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPairContainedEquality

open Set MeasureTheory Filter Topology PlanarQuantitative PlanarParameterDomain
open PlanarSevenCellArea PlanarSevenCellEquality PlanarPairArea PlanarDirectionDerivatives
open PlanarBodySectionDensity PlanarUnitSectionDensity PlanarPairwiseGapUpper
open PlanarAffineEquality PlanarFourPointClassification
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Pair containment and null triple overlap at the original windows
suffice for shape rigidity. The finite surplus inequality applies at the
original windows, without endpoint motion or a local minimum. -/
theorem four_vertices_canonical {K : Set Point} (hK : IsCompact K)
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
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  exact PlanarSevenCellEquality.four_vertices_of_pairwise_identity hK hc hne hV f
    hnorm hunit hpairs c r hcc hr hR
    (PlanarPairwiseGapUpper.gap_eq_pair_sum hK f (path c r 0) hcontain htriple) heq

/-- No positive-cell count is assumed. Positive windows of an actual
equality lie inside their normalized support intervals by the proved
no-waste theorem, so the canonical motion applies to arbitrary endpoints. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints 3) (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0)
    (heq : Equality K f p.1 p.2) : ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
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
  apply four_vertices_canonical hK hc hne hV f hnorm hunit hpairs c r hcc hr
    (by rwa [hsum]) (by simpa only [hp] using hcontain) (by simpa only [hp] using htriple)
  rw [hp,hsum]
  change gapArea K f p = (max 0 (1-budget K f p))^2*(volume K).toReal at heq
  rwa [max_eq_right (sub_pos.mpr hR).le] at heq

theorem equality_iff {K : Set Point} (hK : IsCompact K)
    (hc : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints 3) (ho : ∀ i, p.1 i < p.2 i) (hR : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (htriple : volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0) :
    Equality K f p.1 p.2 ↔ Family K f p.1 p.2 := by
  have hW (i) : 0 < rangeWidth K (f i) := by rw [hunit]; norm_num
  constructor
  · intro he
    exact (equality_iff_of_four_vertices hV
      (four_vertices hK hc hne hV f hnorm hunit hpairs p ho hR hcontain htriple he)
      f p.1 p.2 hW (fun i => (ho i).le)).mp he
  · exact family_sound f p.1 p.2 hW (fun i => (ho i).le)

end Plank.PlanarPairContainedEquality

/-- info: 'Plank.PlanarPairContainedEquality.equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarPairContainedEquality.equality_iff
