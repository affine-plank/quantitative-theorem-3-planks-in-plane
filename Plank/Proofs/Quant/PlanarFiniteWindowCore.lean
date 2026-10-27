/- Finite inclusion-exclusion and the direct planar cap certificate. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalCapWindowCore
public import Plank.Proofs.Quant.PlanarWindowData
public import ResearchFormalized.Measure.FiniteUnion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFinitePairwiseBound
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open PlanarBodySectionDensity PlanarSevenCellArea
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

theorem iUnion_succ {n : ℕ} (A : Fin (n+1) → Set Point) :
    (⋃ i, A i) = A 0 ∪ ⋃ i : Fin n, A i.succ := by
  ext x
  simp only [mem_iUnion, mem_union, Fin.exists_fin_succ]

/-- Each unordered pair is counted once. -/
def areaPairs {n : ℕ} (A : Fin n → Set Point) : ℝ :=
  ∑ i, ∑ j, if i < j then (volume (A i ∩ A j)).toReal else 0

theorem areaPairs_succ {n : ℕ} (A : Fin (n+1) → Set Point) :
    areaPairs A = (∑ j : Fin n, (volume (A 0 ∩ A j.succ)).toReal)+
      areaPairs (fun i : Fin n => A i.succ) := by
  classical
  simp [areaPairs, Fin.sum_univ_succ]

/-- The second finite inclusion-exclusion bound, for actual measurable sets. -/
theorem sum_area_sub_pairs_le_union {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (A : Fin n → Set Point) (hm : ∀ i, MeasurableSet (A i))
    (hsub : ∀ i, A i ⊆ K) :
    (∑ i, (volume (A i)).toReal)-areaPairs A ≤ (volume (⋃ i, A i)).toReal := by
  exact (ResearchFormalized.FiniteUnion.two_term volume A hm
    (fun i => measure_ne_top_of_subset (hsub i) hK.measure_ne_top)).1

/-- Null intersections of three distinct sets make the second bound exact. -/
theorem sum_area_sub_pairs_eq_union {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (A : Fin n → Set Point) (hm : ∀ i, MeasurableSet (A i))
    (hsub : ∀ i, A i ⊆ K)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → volume ((A i ∩ A j) ∩ A k)=0) :
    (∑ i, (volume (A i)).toReal)-areaPairs A = (volume (⋃ i, A i)).toReal := by
  exact (ResearchFormalized.FiniteUnion.two_term volume A hm
    (fun i => measure_ne_top_of_subset (hsub i) hK.measure_ne_top)).2 htriple

/-- The actual gap is body area minus the union of the clipped planks. -/
theorem gap_eq_sub_union {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (f : Fin n → Point →ᵃ[ℝ] ℝ) (e : Endpoints n) :
    gapArea K f e = (volume K).toReal-
      (volume (⋃ i, K ∩ plank (f i) (e.1 i) (e.2 i))).toReal := by
  classical
  let A (i : Fin n) := K ∩ plank (f i) (e.1 i) (e.2 i)
  have hm (i) : MeasurableSet (A i) :=
    hK.measurableSet.inter (isClosed_plank _ _ _).measurableSet
  have hU : (⋃ i, A i) ⊆ K := iUnion_subset (fun _ => inter_subset_left)
  have hset : K \ (⋃ i, A i) = K \ (⋃ i, plank (f i) (e.1 i) (e.2 i)) := by
    change K \ (⋃ i, K ∩ plank (f i) (e.1 i) (e.2 i)) = _
    rw [← inter_iUnion, inter_comm K, sdiff_inter_self_eq_sdiff]
  have hd := measureReal_sdiff hU (MeasurableSet.iUnion hm) hK.measure_ne_top (μ := volume)
  rw [hset] at hd
  simpa only [A, measureReal_def, gapArea, plank] using hd

/-- Expand widths by `1 / R`, keeping each window's cap centre fixed. -/
def capExpansion {n : ℕ} (p : Endpoints n) (R : ℝ) : Endpoints n :=
  (fun i => (1-(p.2 i-p.1 i)/R)*(p.1 i/(1-(p.2 i-p.1 i))),
   fun i => p.1 i/(1-(p.2 i-p.1 i))+
     (1-p.1 i/(1-(p.2 i-p.1 i)))*((p.2 i-p.1 i)/R))

theorem capExpansion_width {n : ℕ} (p : Endpoints n) (R : ℝ) (i : Fin n) :
    (capExpansion p R).2 i-(capExpansion p R).1 i=(p.2 i-p.1 i)/R := by
  dsimp only [capExpansion]
  ring

/-- The cap argument needs only a bound on the expanded total covered area.
The correction `B` can come from any valid union certificate. -/
theorem cap_expansion_bound {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i)=1)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1) (B : ℝ)
    (hexpanded : (∑ i, coveredArea K (f i)
      ((capExpansion p (budget K f p)).1 i) ((capExpansion p (budget K f p)).2 i)) ≤
        (volume K).toReal+B) :
    (1-budget K f p)^2*(volume K).toReal ≤ (volume K).toReal-
      ∑ i, coveredArea K (f i) (p.1 i) (p.2 i)+(budget K f p)^2*B := by
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
  have harea (i) : coveredArea K (f i) (p.1 i) (p.2 i) ≤
      R^2*coveredArea K (f i) (e.1 i) (e.2 i)+
        2*r i*(1-R)*(volume K).toReal := by
    have h := FiniteDimensionalCapWindowScaling.window_contraction (d := 1)
      hK hconv (f i) (hf i)
      (hsupports i).1 (hsupports i).2 (hc i) ⟨hR0.le,hR1.le⟩ (hs i)
    simp only [hrs, hlo, hhi] at h
    norm_num only at h
    dsimp only [coveredArea, plank, e]
    convert h using 1
    rw [← hrs i]
    ring
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => harea i)
  have hextra : (∑ i, 2*r i*(1-R)*(volume K).toReal)=
      2*R*(1-R)*(volume K).toReal := by
    simp only [←Finset.sum_mul,←Finset.mul_sum]
    rfl
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,hextra] at hsum
  change (∑ i, coveredArea K (f i) (e.1 i) (e.2 i)) ≤ (volume K).toReal+B at hexpanded
  have hscaled := mul_le_mul_of_nonneg_left hexpanded (sq_nonneg R)
  nlinarith only [hsum,hscaled]

end Plank.PlanarFinitePairwiseBound
