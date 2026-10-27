/- Tied maximizing vertices force the actual triangle gap below the plank. -/
module
public import Plank.Proofs.Quant.TranslationMomentRigidity
public import Plank.Proofs.Quant.TriangleSourceBoundary

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleTiedMaximum
open Set MeasureTheory Function CommonVertex TranslationEquality
open CommonVertexTranslationEquality TriangleTranslationBoundary CommonMiddleNecessity
open scoped BigOperators

def actualCell (C : Config) (s : Finset (Fin 3)) : Set (ℝ × ℝ) :=
  stdTriangle.set ∩ exteriorCells C s

theorem actualCell_measurable (C : Config) (s : Finset (Fin 3)) :
    MeasurableSet (actualCell C s) :=
  Proofs.GapCells.isCompact_stdTriangle.isClosed.measurableSet.inter
    (exterior_open C s).measurableSet

theorem actualCell_finite (C : Config) (s : Finset (Fin 3)) :
    volume (actualCell C s) ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (measure_mono inter_subset_left)
  rw [Proofs.Quant.volume_stdTriangle]
  exact ENNReal.ofReal_ne_top

theorem actualCell_integrable (C : Config) (s : Finset (Fin 3)) :
    IntegrableOn (fun z : ℝ × ℝ => z.1) (actualCell C s) :=
  (continuous_fst.continuousOn.integrableOn_compact Proofs.GapCells.isCompact_stdTriangle).mono_set
    inter_subset_left

theorem core_integrable (C : Config) :
    IntegrableOn (fun z : ℝ × ℝ => z.1) (RowDeletion.triangle C.deficit) := by
  apply (continuous_fst.continuousOn.integrableOn_compact Proofs.GapCells.isCompact_stdTriangle).mono_set
  intro z hz
  have hr : 0 ≤ C.sumRelW := Finset.sum_nonneg (fun i _ => relWidth_nonneg (C.plank i))
  rw [Proofs.Quant.stdTriangle_set_eq]
  exact ⟨hz.1,hz.2.1,le_trans hz.2.2 (by dsimp only [Config.deficit]; linarith only [hr])⟩

/-- Any valid nonnegative escape steps give the equality partition. In
particular a tie between the two maxima may be resolved either way. -/
theorem partition_of_steps (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (v : Fin 3 → ℝ × ℝ) (hv : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2)
    (hcost : ∀ i, (v i).1+(v i).2=C.relW i)
    (hself : ∀ i, dot (C.plank i).u (v i)=(C.plank i).hi-(C.plank i).lo)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C) :
    Pairwise (AEDisjoint volume on sourcePiece (RowDeletion.triangle C.deficit)
      (shift v) (exteriorCells C)) ∧
      (⋃ s, targetPiece (RowDeletion.triangle C.deficit) (shift v) (exteriorCells C) s)
        =ᵐ[volume] C.uncovered := by
  have hTfin : volume stdTriangle.set ≠ ⊤ := by
    rw [Proofs.Quant.volume_stdTriangle]
    exact ENNReal.ofReal_ne_top
  apply (closed_gap_measure_eq_iff volume
    (fun i => dot (C.plank i).u) (fun i => (Proofs.GapCells.continuous_dot _).measurable)
    (fun i => (C.plank i).lo) (fun i => (C.plank i).hi) (fun i => (C.plank i).lo_le_hi)
    (fun i => volume_line_zero (C.plank i).u_ne_zero _)
    (fun i => volume_line_zero (C.plank i).u_ne_zero _)
    (RowDeletion.triangle C.deficit) (RowDeletion.measurableSet_triangle _)
    (shift v) ?_ stdTriangle.set hTfin ?_).mp ((equality_iff_core_measure C hδ).mp he)
  · intro z _
    have hc : ∀ i j, 0 ≤ dot (C.plank i).u (v j) := fun i j =>
      add_nonneg (mul_nonneg (hu i).1 (hv j).1) (mul_nonneg (hu i).2 (hv j).2)
    obtain ⟨s,hh,hl⟩ := CommonVertex.exists_side_assignment C.plank v hself hc z
    refine ⟨s,fun i => ?_⟩
    by_cases hi : i ∈ s
    · simpa only [hi,if_true] using (hh i hi).le
    · simpa only [hi,if_false] using hl i hi
  · intro s z hz
    apply shifted_mem_triangle v hv s
    simpa only [hcost,Config.deficit,Config.sumRelW] using hz

/-- The original strict cells, without clipping by a supplied core, pull
back to an almost-everywhere partition for every valid escape choice. -/
theorem actual_source_partition (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (v : Fin 3 → ℝ × ℝ) (hv : ∀ i, 0 ≤ (v i).1 ∧ 0 ≤ (v i).2)
    (hcost : ∀ i, (v i).1+(v i).2=C.relW i)
    (hself : ∀ i, dot (C.plank i).u (v i)=(C.plank i).hi-(C.plank i).lo)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C) :
    Pairwise (AEDisjoint volume on fun s => (fun z => z+shift v s) ⁻¹' actualCell C s) ∧
      (⋃ s, (fun z => z+shift v s) ⁻¹' actualCell C s) =ᵐ[volume]
        RowDeletion.triangle C.deficit := by
  classical
  have hp := partition_of_steps C hu v hv hcost hself hδ he
  have hactual (s) : targetPiece (RowDeletion.triangle C.deficit) (shift v) (exteriorCells C) s =
      actualCell C s := by
    ext z
    constructor
    · rintro ⟨hz,hs⟩
      refine ⟨?_,hs⟩
      change z-shift v s ∈ RowDeletion.triangle C.deficit at hz
      have hh := shifted_mem_triangle v hv s (t := z-shift v s)
        (by simpa only [hcost,Config.deficit,Config.sumRelW] using hz)
      simpa only [sub_add_cancel] using hh
    · rintro ⟨hz,hs⟩
      exact ⟨cell_core_of_exhaustion C _ (triangle_closed _) _ hp.2 s hz hs,hs⟩
  have hsource (s) : (fun z => z+shift v s) ⁻¹' actualCell C s =
      sourcePiece (RowDeletion.triangle C.deficit) (shift v) (exteriorCells C) s := by
    rw [← hactual]
    ext z
    simp only [sourcePiece,targetPiece,mem_inter_iff,mem_preimage,add_sub_cancel_right]
  have hdis : Pairwise (AEDisjoint volume on fun s =>
      (fun z => z+shift v s) ⁻¹' actualCell C s) := by
    simpa only [Function.onFun,hsource] using hp.1
  refine ⟨hdis,?_⟩
  have hsub : (⋃ s, (fun z => z+shift v s) ⁻¹' actualCell C s) ⊆
      RowDeletion.triangle C.deficit := by
    intro z hz
    obtain ⟨s,hs⟩ := mem_iUnion.mp hz
    rw [hsource] at hs
    exact hs.1
  have hmeas (s) := (actualCell_measurable C s).preimage (measurable_add_const (shift v s))
  have hcorefin : volume (RowDeletion.triangle C.deficit) ≠ ⊤ := by
    rw [RowDeletion.volume_triangle hδ]
    exact ENNReal.ofReal_ne_top
  have hAdis : Pairwise (Disjoint on actualCell C) := fun s t hst =>
    (Plank.LinearBands.disjoint_strictCells (fun i => dot (C.plank i).u)
      (fun i => (C.plank i).lo) (fun i => (C.plank i).hi)
      (fun i => (C.plank i).lo_le_hi) hst).mono inter_subset_right inter_subset_right
  have hAgap : (⋃ s, actualCell C s) =ᵐ[volume] C.uncovered := by
    simpa only [hactual] using hp.2
  have hAarea : volume (⋃ s, actualCell C s)=∑ s, volume (actualCell C s) := by
    rw [measure_iUnion hAdis (actualCell_measurable C),tsum_fintype]
  apply ae_eq_of_subset_of_measure_ge hsub _ (MeasurableSet.iUnion hmeas).nullMeasurableSet hcorefin
  rw [measure_iUnion₀ hdis (fun s => (hmeas s).nullMeasurableSet),tsum_fintype]
  simp_rw [measure_preimage_add_right]
  rw [← hAarea,measure_congr hAgap,
    (equality_iff_core_measure C hδ).mp he]

/-- Resolve every tie at X rather than Y. All other original steps agree. -/
def alternateSteps (C : Config) (i : Fin 3) : ℝ × ℝ :=
  if (C.plank i).u.1=(C.plank i).u.2 then (C.relW i,0) else steps C i

theorem alternate_nonneg (C : Config) (i : Fin 3) :
    0 ≤ (alternateSteps C i).1 ∧ 0 ≤ (alternateSteps C i).2 := by
  unfold alternateSteps
  split_ifs
  · exact ⟨relWidth_nonneg (C.plank i),le_rfl⟩
  · exact steps_nonneg C i

theorem alternate_cost (C : Config) (i : Fin 3) :
    (alternateSteps C i).1+(alternateSteps C i).2=C.relW i := by
  unfold alternateSteps
  split_ifs
  · simp
  · exact steps_cost C i

theorem alternate_self (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2) (i : Fin 3) :
    dot (C.plank i).u (alternateSteps C i)=(C.plank i).hi-(C.plank i).lo := by
  by_cases hi : (C.plank i).u.1=(C.plank i).u.2
  · have hs := steps_self C hu i
    simp only [steps,if_pos hi.le,dot,mul_zero,zero_add] at hs
    rw [alternateSteps,if_pos hi]
    change (C.plank i).u.1*C.relW i+(C.plank i).u.2*0=_
    rw [hi,mul_zero,add_zero]
    exact hs
  · simpa only [alternateSteps,if_neg hi] using steps_self C hu i

theorem alternate_fst_le (C : Config) (i : Fin 3) :
    (steps C i).1 ≤ (alternateSteps C i).1 := by
  by_cases hi : (C.plank i).u.1=(C.plank i).u.2
  · simp only [alternateSteps,if_pos hi,steps,if_pos hi.le]
    exact relWidth_nonneg (C.plank i)
  · simp only [alternateSteps,if_neg hi,le_refl]

/-- Positive planks constant on the far edge have no upper strict cell
of positive area at equality. Repeated tied directions are allowed. -/
theorem upper_cells_null (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C)
    (j : Fin 3) (hj : (C.plank j).u.1=(C.plank j).u.2) (hw : 0 < C.relW j)
    (s : Finset (Fin 3)) (hjs : j ∈ s) : volume (actualCell C s)=0 := by
  have hp := actual_source_partition C hu (steps C) (steps_nonneg C) (steps_cost C)
    (steps_self C hu) hδ he
  have hq := actual_source_partition C hu (alternateSteps C) (alternate_nonneg C)
    (alternate_cost C) (alternate_self C hu) hδ he
  apply TranslationMomentRigidity.null_of_increased_step (RowDeletion.triangle C.deficit)
    (actualCell C) (shift (steps C)) (shift (alternateSteps C))
    (actualCell_measurable C) (actualCell_finite C) (actualCell_integrable C)
    (core_integrable C) hp.1 hp.2 hq.1 hq.2 ?_ s ?_
  · intro t
    rw [shift_fst,shift_fst]
    exact Finset.sum_le_sum (fun i _ => alternate_fst_le C i)
  · rw [shift_fst,shift_fst]
    apply Finset.sum_lt_sum (fun i _ => alternate_fst_le C i)
    refine ⟨j,hjs,?_⟩
    simpa only [steps,if_pos hj.le,alternateSteps,if_pos hj] using hw

theorem actualCell_empty_of_null (C : Config) (s : Finset (Fin 3))
    (hn : volume (actualCell C s)=0) : actualCell C s=∅ := by
  have hT : stdTriangle.set=upperTriangle 0 := by
    rw [Proofs.Quant.stdTriangle_set_eq]
    rfl
  have hsub : stdTriangle.set ⊆ (exteriorCells C s)ᶜ := subset_of_null_sdiff
    (by rw [hT]; exact isClosed_upperTriangle 0)
    (by rw [hT]; exact convex_upperTriangle 0)
    (by rw [hT]; exact upperTriangle_interior_nonempty 0 (by norm_num))
    (exterior_open C s).isClosed_compl (by simpa only [actualCell,sdiff_compl] using hn)
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  exact hsub hz.1 hz.2

/-- Geometric consequence for the actual original uncovered set: every
uncovered point lies strictly below every positive far-edge-parallel band.
Only common-minimum signs and actual area equality are hypotheses. -/
theorem gap_below (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C)
    (j : Fin 3) (hj : (C.plank j).u.1=(C.plank j).u.2) (hw : 0 < C.relW j)
    {z : ℝ × ℝ} (hz : z ∈ C.uncovered) : dot (C.plank j).u z < (C.plank j).lo := by
  classical
  have hout (i) : ¬((C.plank i).lo ≤ dot (C.plank i).u z ∧
      dot (C.plank i).u z ≤ (C.plank i).hi) := fun hi => hz.2 (mem_iUnion.mpr ⟨i,hi⟩)
  let s : Finset (Fin 3) := Finset.univ.filter (fun i => (C.plank i).hi < dot (C.plank i).u z)
  have hs : z ∈ exteriorCells C s := by
    intro i
    by_cases hi : (C.plank i).hi < dot (C.plank i).u z
    · simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and,if_pos hi] using hi
    · have hl : dot (C.plank i).u z < (C.plank i).lo :=
        lt_of_not_ge (fun hl => hout i ⟨hl,le_of_not_gt hi⟩)
      simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and,if_neg hi] using hl
  by_contra hn
  have hh : (C.plank j).hi < dot (C.plank j).u z :=
    lt_of_not_ge (fun hh => hout j ⟨le_of_not_gt hn,hh⟩)
  have hjs : j ∈ s := by simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have hempty := actualCell_empty_of_null C s (upper_cells_null C hu hδ he j hj hw s hjs)
  have hz' : z ∈ actualCell C s := ⟨hz.1,hs⟩
  rw [hempty] at hz'
  exact hz'

end Quant.TriangleTiedMaximum

/-- info: 'Quant.TriangleTiedMaximum.gap_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleTiedMaximum.gap_below
