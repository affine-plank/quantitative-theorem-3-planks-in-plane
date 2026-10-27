/- Pointwise geometric consequences of triangle translation equality. -/
module
public import Plank.Proofs.Quant.CommonMiddleClassification

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleTranslationBoundary
open Set MeasureTheory Function CommonVertex TranslationEquality
open CommonVertexTranslationEquality CommonMiddleNecessity
open scoped BigOperators

theorem exterior_open (C : Config) (s : Finset (Fin 3)) :
    IsOpen (exteriorCells C s) := by
  classical
  rw [exteriorCells, Plank.LinearBands.strictCell, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  by_cases hi : i ∈ s
  · simp only [hi,if_true]
    exact isOpen_lt continuous_const (Proofs.GapCells.continuous_dot _)
  · simp only [hi,if_false]
    exact isOpen_lt (Proofs.GapCells.continuous_dot _) continuous_const

theorem triangle_closed (d : ℝ) : IsClosed (RowDeletion.triangle d) :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

/-- Almost-everywhere exhaustion actually confines every uncovered point
of each strict cell to its own translated closed core, including points
on the boundary of the original triangle. -/
theorem cell_core_of_exhaustion (C : Config) (core : Set (ℝ × ℝ))
    (hcore : IsClosed core) (v : Finset (Fin 3) → ℝ × ℝ)
    (hex : (⋃ s, targetPiece core v (exteriorCells C) s) =ᵐ[volume] C.uncovered)
    (s : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ stdTriangle.set)
    (hs : z ∈ exteriorCells C s) : z-v s ∈ core := by
  classical
  let H : Set (ℝ × ℝ) := (exteriorCells C s)ᶜ ∪ (fun z => z-v s) ⁻¹' core
  have hH : IsClosed H := (exterior_open C s).isClosed_compl.union
    (hcore.preimage (by fun_prop))
  have hT : stdTriangle.set = upperTriangle 0 := by
    rw [Proofs.Quant.stdTriangle_set_eq]
    rfl
  have hnull : volume (stdTriangle.set \ H) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hex] with x hx hmiss
    have hxs : x ∈ exteriorCells C s := by
      by_contra hn
      exact hmiss.2 (Or.inl hn)
    have hxgap : x ∈ C.uncovered :=
      ⟨hmiss.1,Plank.LinearBands.strictCell_subset_gap _ _ _ s hxs⟩
    obtain ⟨r,hr⟩ := mem_iUnion.mp ((iff_of_eq hx).mpr hxgap)
    have hrs : r=s := by
      by_contra hne
      have hd := Plank.LinearBands.disjoint_strictCells (fun i => dot (C.plank i).u)
        (fun i => (C.plank i).lo) (fun i => (C.plank i).hi)
        (fun i => (C.plank i).lo_le_hi) hne
      exact Set.disjoint_left.mp hd hr.2 hxs
    subst r
    exact hmiss.2 (Or.inr hr.1)
  have hcover : stdTriangle.set ⊆ H := subset_of_null_sdiff
    (by rw [hT]; exact isClosed_upperTriangle 0)
    (by rw [hT]; exact convex_upperTriangle 0)
    (by rw [hT]; exact upperTriangle_interior_nonempty 0 (by norm_num)) hH hnull
  exact (hcover hz).resolve_left (not_not.mpr hs)

/-- At equality, the actual sign cell lies in the corresponding translate
of the deficit triangle; there is no almost-everywhere qualification. -/
theorem common_vertex_cell (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C)
    (s : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ stdTriangle.set)
    (hs : z ∈ exteriorCells C s) :
    z-shift (steps C) s ∈ RowDeletion.triangle C.deficit := by
  have hp := (equality_iff_partition C hu hδ).mp he
  exact cell_core_of_exhaustion C _ (triangle_closed _) _ hp.2 s hz hs

theorem common_vertex_cell_inequalities (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C)
    (s : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ stdTriangle.set)
    (hs : z ∈ exteriorCells C s) :
    (shift (steps C) s).1 ≤ z.1 ∧ (shift (steps C) s).2 ≤ z.2 ∧
      z.1+z.2 ≤ C.deficit+∑ i ∈ s, C.relW i := by
  have hh := common_vertex_cell C hu hδ he s hz hs
  change 0 ≤ z.1-(shift (steps C) s).1 ∧
    0 ≤ z.2-(shift (steps C) s).2 ∧
    (z.1-(shift (steps C) s).1)+(z.2-(shift (steps C) s).2) ≤ C.deficit at hh
  have hsum : (shift (steps C) s).1+(shift (steps C) s).2 = ∑ i ∈ s, C.relW i := by
    rw [shift_fst,shift_snd,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => steps_cost C i)
  exact ⟨by linarith only [hh.1],by linarith only [hh.2.1],by linarith only [hh.2.2,hsum]⟩

/-- An uncovered point on the far edge must be above every positive
plank, since any missing positive escape step would leave too little room. -/
theorem far_edge_all_high (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C)
    (s : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ stdTriangle.set)
    (hs : z ∈ exteriorCells C s) (hedge : z.1+z.2=1)
    (i : Fin 3) (hi : 0 < C.relW i) : i ∈ s := by
  classical
  have hh := (common_vertex_cell_inequalities C hu hδ he s hz hs).2.2
  rw [hedge,Config.deficit,Config.sumRelW] at hh
  by_contra hn
  have hsub : insert i s ⊆ Finset.univ := Finset.subset_univ _
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ => relWidth_nonneg (C.plank j))
  rw [Finset.sum_insert hn] at hsum
  change C.relW i+∑ j ∈ s, C.relW j ≤ ∑ j, C.relW j at hsum
  linarith only [hh,hsum,hi]

end Quant.TriangleTranslationBoundary

/-- info: 'Quant.TriangleTranslationBoundary.far_edge_all_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleTranslationBoundary.far_edge_all_high
