/- Direct finite-family planar expansion without weighted or chart imports. -/
module

public import Plank.Proofs.Quant.PlanarFiniteWindowCore
public import Plank.Proofs.Quant.FiniteDimensionalCapWindowScaling
public import Plank.Proofs.Quant.PlanarPairAreaCore

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFinitePairwiseBound

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open PlanarBodySectionDensity PlanarSevenCellArea PlanarPairArea PlanarDirectionDerivatives
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Actual one-window excess above the normalized quadratic lower bound. -/
def windowExcess (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) : ℝ :=
  (volume (K \ plank f lo hi)).toReal-(1-(hi-lo))^2*(volume K).toReal

theorem windowExcess_eq {K : Set Point} (hK : IsCompact K)
    (f : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ) :
    windowExcess K f lo hi = (volume K).toReal-coveredArea K f lo hi-
      (1-(hi-lo))^2*(volume K).toReal := by
  have h := measureReal_sdiff_add_inter (μ := volume) (s := K)
    (isClosed_plank f lo hi).measurableSet hK.measure_ne_top
  change (volume (K \ plank f lo hi)).toReal+coveredArea K f lo hi =
    (volume K).toReal at h
  unfold windowExcess
  linarith only [h]

/-- The cap argument needs only a bound on the expanded total covered area.
The correction `B` can come from any valid union certificate. -/
theorem cap_expansion_certificate {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1) (B : ℝ)
    (hexpanded : (∑ i, coveredArea K (f i)
      ((capExpansion p (budget K f p)).1 i) ((capExpansion p (budget K f p)).2 i)) ≤
        (volume K).toReal+B) :
    (0 ≤ ∑ i, windowExcess K (f i) (p.1 i) (p.2 i)) ∧
    ((1-budget K f p)^2*(volume K).toReal+
      (1-budget K f p)*(∑ i, windowExcess K (f i) (p.1 i) (p.2 i)) ≤ (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+(budget K f p)^2*B) := by
  classical
  let r (i : Fin n) := p.2 i-p.1 i
  let R := ∑ i, r i
  have hbudget : budget K f p=R := by simp only [budget,hunit,div_one,R,r]
  rw [hbudget] at hR0 hR1 hexpanded ⊢
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
  have hs (i) : s i ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (hr0 i) hR0.le,(div_le_one hR0).mpr (hrR i)⟩
  let e : Endpoints n := (fun i => (1-s i)*c i,fun i => c i+(1-c i)*s i)
  have hsupports (i) :=
    FiniteDimensionalNormalization.unit_realisers hK hne (f i) (hnorm i) (hunit i)
  have hrs (i) : R*s i=r i := by
    dsimp only [s]
    rw [mul_div_cancel₀ _ hR0.ne']
  have hf (i) : (f i).linear ≠ 0 :=
    Body.linear_ne_zero_of_width_pos hne (f i)
      (show 0 < rangeWidth K (f i) by rw [hunit i]; norm_num)
  have hE0 (i) : 0 ≤ windowExcess K (f i) (p.1 i) (p.2 i) := by
    have h := FiniteDimensionalCapWindowScaling.gap_excess_nonneg (d := 1)
      hK hconv (f i) (hf i) (hsupports i).1 (hsupports i).2 (hc i) ⟨hr0 i,(hr1 i).le⟩
    simpa only [FiniteDimensionalCapWindowScaling.gap,windowExcess,plank,hlo,hhi,r] using h
  have harea (i) : coveredArea K (f i) (p.1 i) (p.2 i)+
      (1-R)*windowExcess K (f i) (p.1 i) (p.2 i) ≤
      R^2*coveredArea K (f i) (e.1 i) (e.2 i)+
        2*r i*(1-R)*(volume K).toReal := by
    have h := FiniteDimensionalCapWindowScaling.gap_excess_contraction_linear (d := 1)
      hK hconv (f i) (hf i)
      (hsupports i).1 (hsupports i).2 (hc i) ⟨hR0.le,hR1.le⟩ (hs i)
    have hm := mul_le_mul_of_nonneg_left h hR0.le
    simp only [FiniteDimensionalCapWindowScaling.gap_eq_sub_window hK, hrs, hlo, hhi] at hm
    rw [windowExcess_eq hK]
    change coveredArea K (f i) (p.1 i) (p.2 i) +
      (1-R)*((volume K).toReal-coveredArea K (f i) (p.1 i) (p.2 i)-
        (1-r i)^2*(volume K).toReal) ≤
      R^2*coveredArea K (f i) (e.1 i) (e.2 i)+2*r i*(1-R)*(volume K).toReal
    rw [← hrs i] at hm ⊢
    dsimp only [coveredArea, plank, e]
    norm_num only at hm
    nlinarith only [hm]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => harea i)
  have hextra : (∑ i, 2*r i*(1-R)*(volume K).toReal)=
      2*R*(1-R)*(volume K).toReal := by
    simp only [←Finset.sum_mul,←Finset.mul_sum]
    rfl
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,hextra] at hsum
  change (∑ i, coveredArea K (f i) (e.1 i) (e.2 i)) ≤ (volume K).toReal+B at hexpanded
  have hscaled := mul_le_mul_of_nonneg_left hexpanded (sq_nonneg R)
  exact ⟨Finset.sum_nonneg (fun i _ => hE0 i), by nlinarith only [hsum,hscaled]⟩

/-- The sum of the full pair-plank areas, without clipping to the body. -/
def pairSum {n : ℕ} (f : Fin n → Point →ᵃ[ℝ] ℝ) (e : Endpoints n) : ℝ :=
  areaPairs (fun i => plank (f i) (e.1 i) (e.2 i))

theorem compact_pair (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0)
    (lo hi lo' hi' : ℝ) :
    IsCompact (plank f lo hi ∩ plank g lo' hi') :=
  PlanarPairArea.compact_pair f g h lo hi lo' hi'

/-- The full pairwise expression bounds the actual gap for any finite family. -/
theorem gap_le_pair_sum {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (e : Endpoints n) :
    gapArea K f e ≤ (volume K).toReal-
      ∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+pairSum f e := by
  classical
  let A (i : Fin n) := K ∩ plank (f i) (e.1 i) (e.2 i)
  have hm (i) : MeasurableSet (A i) :=
    hK.measurableSet.inter (isClosed_plank _ _ _).measurableSet
  have hsub (i) : A i ⊆ K := inter_subset_left
  have hbound := sum_area_sub_pairs_le_union hK A hm hsub
  have hp : areaPairs A ≤ pairSum f e := by
    unfold pairSum areaPairs
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      apply ENNReal.toReal_mono
        (compact_pair _ _ (hpairs i j (ne_of_lt hij)) _ _ _ _).measure_ne_top
      exact measure_mono fun _ hx => ⟨hx.1.2, hx.2.2⟩
    · simp only [ite_eq_right hij, le_refl]
  change (∑ i, coveredArea K (f i) (e.1 i) (e.2 i))-areaPairs A ≤
    (volume (⋃ i, A i)).toReal at hbound
  rw [gap_eq_sub_union hK f e]
  linarith only [hbound, hp]

/-- Contained full pairs and null distinct triples give the actual touching
identity for any finite number of planks, including degenerate intersections. -/
theorem gap_eq_pair_sum {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (f : Fin n → Point →ᵃ[ℝ] ℝ) (e : Endpoints n)
    (hcontain : ∀ i j, i ≠ j →
      plank (f i) (e.1 i) (e.2 i) ∩ plank (f j) (e.1 j) (e.2 j) ⊆ K)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      volume ((plank (f i) (e.1 i) (e.2 i) ∩ plank (f j) (e.1 j) (e.2 j)) ∩
        plank (f k) (e.1 k) (e.2 k))=0) :
    gapArea K f e = (volume K).toReal-
      ∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+pairSum f e := by
  classical
  let A (i : Fin n) := K ∩ plank (f i) (e.1 i) (e.2 i)
  have hm (i) : MeasurableSet (A i) :=
    hK.measurableSet.inter (isClosed_plank _ _ _).measurableSet
  have ht (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      volume ((A i ∩ A j) ∩ A k)=0 := by
    apply measure_mono_null _ (htriple i j k hij hik hjk)
    intro x hx
    exact ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩
  have heq (i j : Fin n) (hij : i ≠ j) : A i ∩ A j =
      plank (f i) (e.1 i) (e.2 i) ∩ plank (f j) (e.1 j) (e.2 j) := by
    rw [show A i ∩ A j = K ∩ (plank (f i) (e.1 i) (e.2 i) ∩
      plank (f j) (e.1 j) (e.2 j)) from (inter_inter_distrib_left ..).symm]
    exact inter_eq_right.mpr (hcontain i j hij)
  have hp : areaPairs A=pairSum f e := by
    unfold pairSum areaPairs
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp only [ite_eq_left hij, heq i j (ne_of_lt hij)]
    · simp only [ite_eq_right hij]
  have hsum := sum_area_sub_pairs_eq_union hK A hm (fun _ => inter_subset_left) ht
  rw [hp] at hsum
  change (∑ i, coveredArea K (f i) (e.1 i) (e.2 i))-pairSum f e =
    (volume (⋃ i, A i)).toReal at hsum
  rw [gap_eq_sub_union hK f e]
  linarith only [hsum]

theorem pair_area_capExpansion {n : ℕ} (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints n) {R : ℝ} (hR : 0 < R) (i j : Fin n)
    (hij : cross (f i) (f j) ≠ 0) (hi : p.1 i ≤ p.2 i) (hj : p.1 j ≤ p.2 j) :
    (volume (plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j))).toReal =
      R^2*(volume (plank (f i) ((capExpansion p R).1 i) ((capExpansion p R).2 i) ∩
        plank (f j) ((capExpansion p R).1 j) ((capExpansion p R).2 j))).toReal := by
  have hord (k : Fin n) (hk : p.1 k ≤ p.2 k) :
      (capExpansion p R).1 k ≤ (capExpansion p R).2 k := by
    apply sub_nonneg.mp
    rw [capExpansion_width]
    exact div_nonneg (sub_nonneg.mpr hk) hR.le
  simp only [plank]
  rw [area_pair _ _ hij _ _ _ _ hi hj,
    area_pair _ _ hij _ _ _ _ (hord i hi) (hord j hj),
    capExpansion_width, capExpansion_width]
  field_simp

/-- The full pair sum scales quadratically under canonical expansion. -/
theorem pairSum_capExpansion {n : ℕ} (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints n) {R : ℝ} (hR : 0 < R)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (hp : ∀ i, p.1 i ≤ p.2 i) :
    pairSum f p=R^2*pairSum f (capExpansion p R) := by
  unfold pairSum areaPairs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simpa only [ite_eq_left hij] using
      pair_area_capExpansion f p hR i j (hpairs i j (ne_of_lt hij)) (hp i) (hp j)
  · simp only [ite_eq_right hij, mul_zero]

/-- Complete-pair Bonferroni is one instance of the cap certificate. -/
private theorem pairwise_expression_cap_certificate {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1) :
    (0 ≤ ∑ i, windowExcess K (f i) (p.1 i) (p.2 i)) ∧
    ((1-budget K f p)^2*(volume K).toReal+
      (1-budget K f p)*(∑ i, windowExcess K (f i) (p.1 i) (p.2 i)) ≤ (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p) := by
  classical
  let R := budget K f p
  let e := capExpansion p R
  have hscale : pairSum f p=R^2*pairSum f e :=
    pairSum_capExpansion f p hR0 hpairs (fun i => (hp i).2.1)
  have hupper := gap_le_pair_sum hK f hpairs e
  have hgap : 0 ≤ gapArea K f e := ENNReal.toReal_nonneg
  have hexpanded : (∑ i, coveredArea K (f i) (e.1 i) (e.2 i)) ≤
      (volume K).toReal+pairSum f e := by linarith only [hupper,hgap]
  rw [hscale]
  exact cap_expansion_certificate hK hconv hne f hnorm hunit p hp hR0 hR1
    (pairSum f e) hexpanded


/-- The full pairwise expression retains its uniform one-window surplus directly. -/
theorem pairwise_expression_bound_with_surplus {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1) :
    (1-budget K f p)^2*(volume K).toReal+
      (1-budget K f p)*(∑ i, windowExcess K (f i) (p.1 i) (p.2 i)) ≤ (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p := by
  exact (pairwise_expression_cap_certificate hK hconv hne f hnorm hunit hpairs p hp hR0 hR1).2

/-- The full pairwise expression itself satisfies the sharp quadratic bound.
The actual gap need not attain that expression in this theorem. -/
theorem pairwise_expression_bound {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1) :
    (1-budget K f p)^2*(volume K).toReal ≤ (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p := by
  have h := pairwise_expression_cap_certificate hK hconv hne f hnorm hunit hpairs p hp hR0 hR1
  have hn := mul_nonneg (sub_pos.mpr hR1).le h.1
  linarith only [h.2,hn]

/-- An actual touching pairwise area bound gives the sharp gap estimate for
any finite planar plank family. The touching identity is a geometric premise. -/
theorem bound_of_pairwise_identity {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+pairSum f p) :
    (1-budget K f p)^2*(volume K).toReal ≤ gapArea K f p := by
  rw [heq]
  exact pairwise_expression_bound hK hconv hne f hnorm hunit hpairs p hp hR0 hR1

/-- A geometric sufficient condition for the finite-family gap estimate.
No assertion is made that these containment and null-triple premises always hold. -/
theorem bound_of_pair_containment {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (hcontain : ∀ i j, i ≠ j →
      plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j) ⊆ K)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      volume ((plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j)) ∩
        plank (f k) (p.1 k) (p.2 k))=0) :
    (1-budget K f p)^2*(volume K).toReal ≤ gapArea K f p := by
  exact bound_of_pairwise_identity hK hconv hne f hnorm hunit hpairs p hp hR0 hR1
    (gap_eq_pair_sum hK f p hcontain htriple)

end Plank.PlanarFinitePairwiseBound
