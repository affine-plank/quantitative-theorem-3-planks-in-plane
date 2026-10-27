/- A global actual-gap upper bound using full pair-plank areas. -/
module

public import Plank.Proofs.Quant.PlanarFinitePairwiseBound

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPairwiseGapUpper

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarSevenCellArea
open PlanarBodySectionDensity PlanarPairArea PlanarDirectionDerivatives
open scoped BigOperators

/-- Finite real-area inclusion-exclusion, retaining the actual triple term. -/
theorem area_sdiff_three {K A B C : Set Point} (hK : IsCompact K)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hCK : C ⊆ K) :
    (volume (K \ ((A ∪ B) ∪ C))).toReal = (volume K).toReal-
      (volume A).toReal-(volume B).toReal-(volume C).toReal+
      (volume (A ∩ B)).toReal+(volume (A ∩ C)).toReal+(volume (B ∩ C)).toReal-
      (volume ((A ∩ B) ∩ C)).toReal := by
  have hAfin : volume A ≠ ⊤ := measure_ne_top_of_subset hAK hK.measure_ne_top
  have hBfin : volume B ≠ ⊤ := measure_ne_top_of_subset hBK hK.measure_ne_top
  have hCfin : volume C ≠ ⊤ := measure_ne_top_of_subset hCK hK.measure_ne_top
  have hABK : A ∪ B ⊆ K := union_subset hAK hBK
  have hABfin : volume (A ∪ B) ≠ ⊤ := measure_ne_top_of_subset hABK hK.measure_ne_top
  have hACfin : volume (A ∩ C) ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hAfin
  have hBCfin : volume (B ∩ C) ≠ ⊤ := measure_ne_top_of_subset inter_subset_left hBfin
  have hab := measureReal_union_add_inter (μ := volume) (s := A) hB hAfin hBfin
  have habc := measureReal_union_add_inter (μ := volume) (s := A ∪ B) hC hABfin hCfin
  have hcross := measureReal_union_add_inter (μ := volume) (s := A ∩ C) (hB.inter hC) hACfin hBCfin
  have he : (A ∩ C) ∩ (B ∩ C) = (A ∩ B) ∩ C := by
    ext x
    simp only [mem_inter_iff]
    tauto
  rw [he,← union_inter_distrib_right] at hcross
  have hdiff := measureReal_sdiff_add_inter (μ := volume) (s := K) ((hA.union hB).union hC)
    hK.measure_ne_top
  rw [inter_eq_right.mpr (union_subset hABK hCK)] at hdiff
  change (volume (A ∪ B)).toReal+(volume (A ∩ B)).toReal =
    (volume A).toReal+(volume B).toReal at hab
  change (volume ((A ∪ B) ∪ C)).toReal+(volume ((A ∪ B) ∩ C)).toReal =
    (volume (A ∪ B)).toReal+(volume C).toReal at habc
  change (volume ((A ∪ B) ∩ C)).toReal+(volume ((A ∩ B) ∩ C)).toReal =
    (volume (A ∩ C)).toReal+(volume (B ∩ C)).toReal at hcross
  change (volume (K \ ((A ∪ B) ∪ C))).toReal+(volume ((A ∪ B) ∪ C)).toReal =
    (volume K).toReal at hdiff
  linarith only [hab,habc,hcross,hdiff]

theorem compact_pair (f g : Point →ᵃ[ℝ] ℝ) (h : cross f g ≠ 0)
    (lo hi lo' hi' : ℝ) :
    IsCompact (plank f lo hi ∩ plank g lo' hi') := by
  exact PlanarFinitePairwiseBound.compact_pair f g h lo hi lo' hi'

def pairSum (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3) : ℝ :=
  (volume (plank (f 0) (e.1 0) (e.2 0) ∩ plank (f 1) (e.1 1) (e.2 1))).toReal+
  (volume (plank (f 0) (e.1 0) (e.2 0) ∩ plank (f 2) (e.1 2) (e.2 2))).toReal+
  (volume (plank (f 1) (e.1 1) (e.2 1) ∩ plank (f 2) (e.1 2) (e.2 2))).toReal

/-- Compatibility of the finite-family pair sum with the three-pair notation. -/
theorem finite_pairSum_eq (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3) :
    PlanarFinitePairwiseBound.pairSum f e = pairSum f e := by
  classical
  have h02 : (0 : Fin 3) < 2 := by decide
  have h12 : (1 : Fin 3) < 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  norm_num [PlanarFinitePairwiseBound.pairSum, PlanarFinitePairwiseBound.areaPairs,
    Fin.sum_univ_three, pairSum, h02, h12, h20]

theorem gap_identity {K : Set Point} (hK : IsCompact K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3) :
    gapArea K f e = (volume K).toReal-∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+
      (volume ((K ∩ plank (f 0) (e.1 0) (e.2 0)) ∩ (K ∩ plank (f 1) (e.1 1) (e.2 1)))).toReal+
      (volume ((K ∩ plank (f 0) (e.1 0) (e.2 0)) ∩ (K ∩ plank (f 2) (e.1 2) (e.2 2)))).toReal+
      (volume ((K ∩ plank (f 1) (e.1 1) (e.2 1)) ∩ (K ∩ plank (f 2) (e.1 2) (e.2 2)))).toReal-
      (volume (K ∩ {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i})).toReal := by
  let A (i : Fin 3) := K ∩ plank (f i) (e.1 i) (e.2 i)
  have hm (i) : MeasurableSet (A i) := hK.measurableSet.inter (isClosed_plank _ _ _).measurableSet
  have ht : (A 0 ∩ A 1) ∩ A 2 = K ∩ {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i} := by
    ext x
    simp only [A,plank,mem_inter_iff,mem_ofPred_eq,Fin.forall_fin_succ,Fin.forall_fin_zero,and_true]
    tauto
  have hs : K \ ((A 0 ∪ A 1) ∪ A 2) =
      K \ ⋃ i, {x | e.1 i ≤ f i x ∧ f i x ≤ e.2 i} := by
    ext x
    simp only [A,plank,mem_inter_iff,mem_sdiff,mem_union,mem_iUnion,mem_ofPred_eq,
      Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
    tauto
  have hh := area_sdiff_three hK (hm 0) (hm 1) (hm 2)
    inter_subset_left inter_subset_left inter_subset_left
  rw [ht,hs] at hh
  simpa only [gapArea,coveredArea,Fin.sum_univ_three,sub_add_eq_sub_sub,A] using hh

/-- The full pairwise expression is a global upper bound on the actual
uncovered area, with no containment or cell-count assumption. -/
theorem gap_le_pair_sum {K : Set Point} (hK : IsCompact K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (e : Endpoints 3) :
    gapArea K f e ≤ (volume K).toReal-∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+pairSum f e := by
  simpa only [finite_pairSum_eq] using
    PlanarFinitePairwiseBound.gap_le_pair_sum hK f hpairs e

/-- Pair containment and a null triple intersection attain that global
upper bound, even when the triple intersection is a point or segment. -/
theorem gap_eq_pair_sum {K : Set Point} (hK : IsCompact K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3)
    (hcontain : ∀ i j, i ≠ j → plank (f i) (e.1 i) (e.2 i) ∩ plank (f j) (e.1 j) (e.2 j) ⊆ K)
    (htriple : volume {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i} = 0) :
    gapArea K f e = (volume K).toReal-∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+pairSum f e := by
  have ht (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      volume ((plank (f i) (e.1 i) (e.2 i) ∩ plank (f j) (e.1 j) (e.2 j)) ∩
        plank (f k) (e.1 k) (e.2 k))=0 := by
    have hset : (plank (f i) (e.1 i) (e.2 i) ∩ plank (f j) (e.1 j) (e.2 j)) ∩
        plank (f k) (e.1 k) (e.2 k) = {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i} := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> try contradiction
      all_goals
        ext x
        simp only [plank, mem_inter_iff, mem_ofPred_eq, Fin.forall_fin_succ,
          Fin.forall_fin_zero, and_true]
        tauto
    rw [hset]
    exact htriple
  simpa only [finite_pairSum_eq] using
    PlanarFinitePairwiseBound.gap_eq_pair_sum hK f e hcontain ht

end Plank.PlanarPairwiseGapUpper

/-- info: 'Plank.PlanarPairwiseGapUpper.gap_le_pair_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarPairwiseGapUpper.gap_le_pair_sum
/-- info: 'Plank.PlanarPairwiseGapUpper.gap_eq_pair_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarPairwiseGapUpper.gap_eq_pair_sum
