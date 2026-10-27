/- The full overlap correction, retaining positive triple intersections. -/
module

public import Plank.Proofs.Quant.PlanarPairwiseGapUpper

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOverlapCorrection

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarSevenCellArea
open PlanarBodySectionDensity PlanarPairArea PlanarDirectionDerivatives
open PlanarPairwiseGapUpper
open scoped BigOperators

/-- The inclusion-exclusion correction is a sum of two actual areas.
This representation makes its monotonicity explicit. -/
def correction (P : Fin 3 → Set Point) : ℝ :=
  (volume ((P 0 ∩ P 1) ∪ (P 0 ∩ P 2))).toReal+(volume (P 1 ∩ P 2)).toReal

def windows (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3) (i : Fin 3) : Set Point :=
  plank (f i) (e.1 i) (e.2 i)

theorem correction_eq (P : Fin 3 → Set Point)
    (hm : ∀ i, MeasurableSet (P i))
    (h01 : volume (P 0 ∩ P 1) ≠ ⊤) (h02 : volume (P 0 ∩ P 2) ≠ ⊤) :
    correction P = (volume (P 0 ∩ P 1)).toReal+(volume (P 0 ∩ P 2)).toReal+
      (volume (P 1 ∩ P 2)).toReal-(volume ((P 0 ∩ P 1) ∩ P 2)).toReal := by
  have hh := measureReal_union_add_inter (μ := volume) (s := P 0 ∩ P 1)
    ((hm 0).inter (hm 2)) h01 h02
  have hs : (P 0 ∩ P 1) ∩ (P 0 ∩ P 2) = (P 0 ∩ P 1) ∩ P 2 := by
    ext x
    simp only [mem_inter_iff]
    tauto
  rw [hs] at hh
  change (volume ((P 0 ∩ P 1) ∪ (P 0 ∩ P 2))).toReal+
    (volume ((P 0 ∩ P 1) ∩ P 2)).toReal =
      (volume (P 0 ∩ P 1)).toReal+(volume (P 0 ∩ P 2)).toReal at hh
  unfold correction
  linarith only [hh]

theorem correction_mono (P Q : Fin 3 → Set Point) (hsub : ∀ i, P i ⊆ Q i)
    (hcompact : ∀ i j, i ≠ j → IsCompact (Q i ∩ Q j)) : correction P ≤ correction Q := by
  have hp (i j : Fin 3) : P i ∩ P j ⊆ Q i ∩ Q j := inter_subset_inter (hsub i) (hsub j)
  have hu : (volume ((P 0 ∩ P 1) ∪ (P 0 ∩ P 2))).toReal ≤
      (volume ((Q 0 ∩ Q 1) ∪ (Q 0 ∩ Q 2))).toReal := ENNReal.toReal_mono
    ((hcompact 0 1 (by decide)).union (hcompact 0 2 (by decide))).measure_ne_top
    (measure_mono (union_subset_union (hp 0 1) (hp 0 2)))
  have hv : (volume (P 1 ∩ P 2)).toReal ≤ (volume (Q 1 ∩ Q 2)).toReal :=
    ENNReal.toReal_mono (hcompact 1 2 (by decide)).measure_ne_top
    (measure_mono (hp 1 2))
  exact add_le_add hu hv

theorem gap_eq_restricted {K : Set Point} (hK : IsCompact K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3) :
    gapArea K f e = (volume K).toReal-∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+
      correction (fun i => K ∩ windows f e i) := by
  let P (i) := K ∩ windows f e i
  have hm (i) : MeasurableSet (P i) :=
    hK.measurableSet.inter (isClosed_plank _ _ _).measurableSet
  have hfin (i j : Fin 3) : volume (P i ∩ P j) ≠ ⊤ :=
    measure_ne_top_of_subset (inter_subset_left.trans inter_subset_left) hK.measure_ne_top
  have ht : (P 0 ∩ P 1) ∩ P 2 =
      K ∩ {x | ∀ i, e.1 i ≤ f i x ∧ f i x ≤ e.2 i} := by
    ext x
    simp only [P,windows,plank,mem_inter_iff,mem_ofPred_eq,Fin.forall_fin_succ,
      Fin.forall_fin_zero,and_true]
    tauto
  rw [gap_identity hK f e,correction_eq P hm (hfin 0 1) (hfin 0 2),ht]
  dsimp only [P,windows]
  ring

/-- The full correction bounds the restricted correction, including the
triple term. No null-overlap or containment premise is required. -/
theorem gap_le_full {K : Set Point} (hK : IsCompact K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hpairs : ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0) (e : Endpoints 3) :
    gapArea K f e ≤ (volume K).toReal-∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+
      correction (windows f e) := by
  rw [gap_eq_restricted hK f e]
  have hh : correction (fun i => K ∩ windows f e i) ≤ correction (windows f e) :=
    correction_mono _ _ (fun _ => inter_subset_right)
      (fun i j hij => PlanarPairwiseGapUpper.compact_pair _ _ (hpairs i j hij) _ _ _ _)
  exact add_le_add le_rfl hh

/-- Containment of every full pair overlap attains the correction bound,
with arbitrary positive, null or empty triple intersection. -/
theorem gap_eq_full {K : Set Point} (hK : IsCompact K)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (e : Endpoints 3)
    (hcontain : ∀ i j, i ≠ j → windows f e i ∩ windows f e j ⊆ K) :
    gapArea K f e = (volume K).toReal-∑ i, coveredArea K (f i) (e.1 i) (e.2 i)+
      correction (windows f e) := by
  have hp (i j : Fin 3) (hij : i ≠ j) :
      (K ∩ windows f e i) ∩ (K ∩ windows f e j) = windows f e i ∩ windows f e j := by
    ext x
    exact ⟨fun hx => ⟨hx.1.2,hx.2.2⟩,
      fun hx => ⟨⟨hcontain i j hij hx,hx.1⟩,⟨hcontain i j hij hx,hx.2⟩⟩⟩
  rw [gap_eq_restricted hK f e]
  simp only [correction,hp 0 1 (by decide),hp 0 2 (by decide),hp 1 2 (by decide)]

end Plank.PlanarOverlapCorrection

/-- info: 'Plank.PlanarOverlapCorrection.gap_le_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOverlapCorrection.gap_le_full
/-- info: 'Plank.PlanarOverlapCorrection.gap_eq_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOverlapCorrection.gap_eq_full
