/- Finite planar expansion uses clipped pairs and separate centres in the body. -/
module

public import Plank.Proofs.Quant.PlanarFiniteWindowCore
public import Plank.Proofs.Quant.FiniteDimensionalWindowAnchors

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPairAnchorBound

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open PlanarSevenCellArea PlanarBodySectionDensity PlanarFinitePairwiseBound
open FiniteDimensionalPairAnchors FiniteDimensionalWindowFamily
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Pair centres inside the body and null triple overlaps suffice. Full pair
intersections may escape the body, and directions need not be transverse. -/
theorem bound_of_pair_anchors {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (hanchor : ∀ i j, i ≠ j → ∃ z ∈ K,
      f i z = p.1 i/(1-(p.2 i-p.1 i)) ∧ f j z = p.1 j/(1-(p.2 j-p.1 j)))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      volume ((plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j)) ∩
        plank (f k) (p.1 k) (p.2 k)) = 0) :
    (1-budget K f p)^2*(volume K).toReal ≤ gapArea K f p := by
  classical
  let R := budget K f p
  let r (i : Fin n) := p.2 i-p.1 i
  let c (i : Fin n) := p.1 i/(1-r i)
  have hbudget : R = ∑ i, r i := by simp only [R, budget, hunit, div_one, r]
  have hr0 (i) : 0 ≤ r i := sub_nonneg.mpr (hp i).2.1
  have hrR (i) : r i ≤ R := by
    rw [hbudget]
    exact Finset.single_le_sum (fun j _ => hr0 j) (Finset.mem_univ i)
  have hr1 (i) : r i < 1 := (hrR i).trans_lt hR1
  have hcanonical (i) := FiniteDimensionalNormalization.canonical_window
    (hp i).1 (hp i).2.2 (hr1 i)
  have hlo (i) : (1-r i)*c i = p.1 i := (hcanonical i).2.1
  have hhi (i) : c i+(1-c i)*r i = p.2 i := (hcanonical i).2.2
  let e := capExpansion p R
  let A (q : Endpoints n) (i : Fin n) := K ∩ plank (f i) (q.1 i) (q.2 i)
  have hm (q i) : MeasurableSet (A q i) :=
    hK.measurableSet.inter (isClosed_plank _ _ _).measurableSet
  have hscale : R^2*areaPairs (A e) ≤ areaPairs (A p) := by
    unfold areaPairs
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i < j
    · simp only [ite_eq_left hij]
      obtain ⟨z, hz, hzi, hzj⟩ := hanchor i j (ne_of_lt hij)
      have h := volume_intersection_contraction hK hconv f c r {i, j} hz
        (by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hzi
          · exact hzj) ⟨hR0, hR1.le⟩
      have hpair (B : Fin n → Set Point) :
          (⋂ k ∈ ({i, j} : Finset (Fin n)), B k) = B i ∩ B j := by
        ext x
        simp
      simp only [hpair, windows, hlo, hhi, measureReal_def] at h
      simpa only [A, ← inter_inter_distrib_left, plank, e, capExpansion, c, r] using h
    · simp only [ite_eq_right hij, mul_zero, le_refl]
  have ht (i j k) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      volume ((A p i ∩ A p j) ∩ A p k) = 0 := by
    apply measure_mono_null _ (htriple i j k hij hik hjk)
    exact fun x hx => ⟨⟨hx.1.1.2, hx.1.2.2⟩, hx.2.2⟩
  have horiginal := sum_area_sub_pairs_eq_union hK (A p) (hm p)
    (fun _ => inter_subset_left) ht
  have hexpanded := sum_area_sub_pairs_le_union hK (A e) (hm e)
    (fun _ => inter_subset_left)
  have hunion := measureReal_mono (μ := volume)
    (iUnion_subset (fun i => (show A e i ⊆ K from inter_subset_left))) hK.measure_ne_top
  change (volume (⋃ i, A e i)).toReal ≤ (volume K).toReal at hunion
  have hB : (∑ i, coveredArea K (f i) (e.1 i) (e.2 i)) ≤
      (volume K).toReal+areaPairs (A e) := by
    change (∑ i, coveredArea K (f i) (e.1 i) (e.2 i))-areaPairs (A e) ≤ _ at hexpanded
    linarith only [hexpanded, hunion]
  have hcap := cap_expansion_bound hK hconv hne f hnorm hunit p hp hR0 hR1
    (areaPairs (A e)) hB
  rw [gap_eq_sub_union hK f p]
  change (1-R)^2*(volume K).toReal ≤ (volume K).toReal-(volume (⋃ i, A p i)).toReal
  change (∑ i, coveredArea K (f i) (p.1 i) (p.2 i))-areaPairs (A p) = _ at horiginal
  linarith only [hcap, hscale, horiginal]

/-- Four corner witnesses for each pair give the required centres by convexity.
Only the null-triple condition remains beyond this finite corner condition. -/
theorem bound_of_pair_corners {n : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (f : Fin n → Point →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, rangeWidth K (f i) = 1)
    (p : Endpoints n) (hp : ∀ i, 0 ≤ p.1 i ∧ p.1 i ≤ p.2 i ∧ p.2 i ≤ 1)
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (hcorners : ∀ i j, i ≠ j → ∀ b c : Bool, ∃ x ∈ K,
      (if b then p.2 i ≤ f i x else f i x ≤ p.1 i) ∧
      (if c then p.2 j ≤ f j x else f j x ≤ p.1 j))
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      volume ((plank (f i) (p.1 i) (p.2 i) ∩ plank (f j) (p.1 j) (p.2 j)) ∩
        plank (f k) (p.1 k) (p.2 k)) = 0) :
    (1-budget K f p)^2*(volume K).toReal ≤ gapArea K f p := by
  apply bound_of_pair_anchors hK hconv hne f hnorm hunit p hp hR0 hR1 _ htriple
  have hbudget : budget K f p = ∑ i, (p.2 i-p.1 i) := by
    simp only [budget, hunit, div_one]
  rw [hbudget] at hR1
  have hw (i) : p.2 i-p.1 i < 1 := lt_of_le_of_lt
    (Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hp j).2.1)
      (Finset.mem_univ i)) hR1
  intro i j hij
  exact exists_pair_anchor_of_corners hconv (f i) (f j)
    (canonical_centre_mem (hp i).1 (hp i).2.1 (hp i).2.2 (hw i))
    (canonical_centre_mem (hp j).1 (hp j).2.1 (hp j).2.2 (hw j)) (hcorners i j hij)

end Plank.PlanarPairAnchorBound
