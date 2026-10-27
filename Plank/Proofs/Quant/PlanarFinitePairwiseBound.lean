/- Finite-window expansion for an arbitrary finite planar plank family. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalCapWindowScaling
public import Plank.Proofs.Quant.PlanarFinitePairwiseCore

public import Plank.Proofs.Quant.PlanarOnePlankClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFinitePairwiseBound

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open PlanarBodySectionDensity PlanarSevenCellArea PlanarPairArea PlanarDirectionDerivatives
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem windowExcess_nonneg {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (f : Point →ᵃ[ℝ] ℝ)
    (hunit : rangeWidth K f = 1) {lo hi : ℝ} (ho : lo ≤ hi) (hr : hi-lo ≤ 1) :
    0 ≤ windowExcess K f lo hi := by
  have h := PlanarOnePlank.uncovered_area_lower_bound hK hconv hne f lo hi ho
    (by rw [hunit]; norm_num)
  rw [hunit,div_one,max_eq_right (sub_nonneg.mpr hr)] at h
  exact sub_nonneg.mpr h

/-- The full pairwise expression retains each actual excess with its width-dependent weight.
It is a lower bound for the actual gap only when the pairwise identity holds. -/
theorem pairwise_expression_bound_with_weighted_surplus {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1) :
    (1-budget K f p)^2*(volume K).toReal+
      (1-budget K f p)*(∑ i, 2/(2-(p.2 i-p.1 i))*windowExcess K (f i) (p.1 i) (p.2 i)) ≤ (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p := by
  classical
  let r (i : Fin n) := p.2 i-p.1 i
  let R := ∑ i, r i
  have hbudget : budget K f p=R := by simp only [budget,hunit,div_one,R,r]
  rw [hbudget] at hR0 hR1 ⊢
  have hr0 (i) : 0 ≤ r i := sub_nonneg.mpr (hp i).2.1
  have hrR (i) : r i ≤ R := Finset.single_le_sum (fun j _ => hr0 j) (Finset.mem_univ i)
  have hr1 (i) : r i < 1 := (hrR i).trans_lt hR1
  let c (i) := p.1 i/(1-r i)
  have hcanonical (i) := FiniteDimensionalNormalization.canonical_window
    (hp i).1 (hp i).2.2 (hr1 i)
  have hc (i) : c i ∈ Icc (0 : ℝ) 1 := (hcanonical i).1
  have hlo (i) : (1-r i)*c i=p.1 i := (hcanonical i).2.1
  have hhi (i) : c i+(1-c i)*r i=p.2 i := (hcanonical i).2.2
  let s (i) := r i/R
  let e : Endpoints n := (fun i => (1-s i)*c i,fun i => c i+(1-c i)*s i)
  have hsupports (i) :=
    FiniteDimensionalNormalization.unit_realisers hK hne (f i) (hnorm i) (hunit i)
  have harea (i) : coveredArea K (f i) (p.1 i) (p.2 i)+
      (1-R)*(2/(2-r i)*windowExcess K (f i) (p.1 i) (p.2 i)) ≤
      R^2*coveredArea K (f i) (e.1 i) (e.2 i)+2*r i*(1-R)*(volume K).toReal := by
    have hf : (f i).linear ≠ 0 := PlanarGapCells.linear_ne_zero_of_rangeWidth_pos
      hne (f i) (by rw [hunit i]; norm_num)
    have h := FiniteDimensionalCapWindowScaling.window_expansion_bound hK hconv (f i) hf
      (hsupports i).1 (hsupports i).2 (hc i) ⟨hR0,hR1.le⟩ (hr0 i) (hrR i)
    rw [FiniteDimensionalCapWindowScaling.excessWeight_two R ⟨hr0 i,(hr1 i).le⟩] at h
    norm_num only at h
    simp only [hlo,hhi] at h
    have hq : 2/(2-r i)*(2-r i)=2 := div_mul_cancel₀ 2 (by linarith only [hr1 i])
    have hid := congrArg (fun x : ℝ => (1-R)*r i*(volume K).toReal*x) hq
    rw [windowExcess_eq hK]
    dsimp only [coveredArea,plank,e,s,r] at h hid ⊢
    nlinarith only [h,hid]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => harea i)
  have hextra : (∑ i, 2*r i*(1-R)*(volume K).toReal)=
      2*R*(1-R)*(volume K).toReal := by
    simp only [←Finset.sum_mul,←Finset.mul_sum]
    rfl
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,hextra] at hsum
  have hscale : pairSum f p=R^2*pairSum f e :=
    pairSum_capExpansion f p hR0 hpairs (fun i => (hp i).2.1)
  have hupper := gap_le_pair_sum hK f hpairs e
  have hgap : 0 ≤ gapArea K f e := ENNReal.toReal_nonneg
  have hexpanded : (∑ i, coveredArea K (f i) (e.1 i) (e.2 i)) ≤
      (volume K).toReal+pairSum f e := by linarith only [hupper,hgap]
  have hscaled := mul_le_mul_of_nonneg_left hexpanded (sq_nonneg R)
  rw [hscale]
  dsimp only [r] at hsum ⊢
  nlinarith only [hsum,hscaled]

/-- A touching pairwise identity transfers the finite weighted surplus to actual gap area. -/
theorem bound_with_weighted_surplus_of_pairwise_identity {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (hpair : gapArea K f p = (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p) :
    (1-budget K f p)^2*(volume K).toReal+
      (1-budget K f p)*(∑ i, 2/(2-(p.2 i-p.1 i))*windowExcess K (f i) (p.1 i) (p.2 i)) ≤ gapArea K f p := by
  rw [hpair]
  exact pairwise_expression_bound_with_weighted_surplus hK hconv hne f hnorm hunit hpairs p hp hR0 hR1

/-- A touching pairwise identity transfers the finite surplus to actual gap area. -/
theorem bound_with_surplus_of_pairwise_identity {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (hpair : gapArea K f p = (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p) :
    (1-budget K f p)^2*(volume K).toReal+
      (1-budget K f p)*(∑ i, windowExcess K (f i) (p.1 i) (p.2 i)) ≤ gapArea K f p := by
  rw [hpair]
  exact pairwise_expression_bound_with_surplus hK hconv hne f hnorm hunit hpairs p hp hR0 hR1

/-- Equality with a touching pairwise identity forces each actual window to be sharp. -/
theorem each_window_equality_of_pairwise_identity {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (hpair : gapArea K f p = (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∀ i, (volume (K \ plank (f i) (p.1 i) (p.2 i))).toReal =
      (1-(p.2 i-p.1 i))^2*(volume K).toReal := by
  classical
  have hE (i) : 0 ≤ windowExcess K (f i) (p.1 i) (p.2 i) :=
    windowExcess_nonneg hK hconv hne (f i) (hunit i) (hp i).2.1
      (by linarith only [(hp i).1,(hp i).2.2])
  have h := bound_with_surplus_of_pairwise_identity hK hconv hne f hnorm hunit hpairs
    p hp hR0 hR1 hpair
  rw [heq] at h
  have hs : ∑ i, windowExcess K (f i) (p.1 i) (p.2 i) = 0 := by
    have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hE i)
    have hp := sub_pos.mpr hR1
    nlinarith only [h,hn,hp]
  intro i
  exact sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hE j)).mp
    hs i (Finset.mem_univ i))

/-- A positive window in a finite touching equality forces at most four body vertices. -/
theorem four_vertices_of_pairwise_identity {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (hpair : gapArea K f p = (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (i : Fin n) (hi : p.1 i < p.2 i) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  have hR : (∑ j, (p.2 j-p.1 j)) < 1 := by
    simpa only [budget,hunit,div_one] using hR1
  have hr : p.2 i-p.1 i < 1 :=
    (Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hp j).2.1) (Finset.mem_univ i)).trans_lt hR
  apply PlanarOnePlankClassification.equality_implies_four_vertices hK hconv hne hV
    (f i) (p.1 i) (p.2 i) hi (by rw [hunit]; norm_num) (by rwa [hunit,div_one])
  rw [hunit,div_one]
  exact each_window_equality_of_pairwise_identity hK hconv hne f hnorm hunit hpairs
    p hp hR0 hR1 hpair heq i

end Plank.PlanarFinitePairwiseBound
