/- Complete split-edge family in the remaining parallel mixed sector. -/
module
public import Plank.Proofs.Quant.TriangleMixedOneEdge
public import Plank.Proofs.Quant.TriangleSplitEdgeFamily

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedParallelEdge
open Set MeasureTheory CommonVertex CommonVertexTranslationEquality
open TriangleTranslationBoundary TriangleFarEdge TriangleMixedCalibration
open CommonMiddleAffineTransport TriangleStrictCommonMinimum
open scoped BigOperators

private theorem ordered_intervals {l₀ h₀ l₁ h₁ R : ℝ}
    (_hw₀ : l₀ < h₀) (_hw₁ : l₁ < h₁)
    (hs : (h₀-l₀)+(h₁-l₁)=R)
    (hL : l₀ ≤ 0 ∧ 0 ≤ h₀) (hU : l₁ ≤ R ∧ R ≤ h₁)
    (hc : ∀ x ∈ Icc 0 R, (l₀ ≤ x ∧ x ≤ h₀) ∨ (l₁ ≤ x ∧ x ≤ h₁)) :
    l₀=0 ∧ h₀=l₁ ∧ h₁=R := by
  have ht : l₁ ≤ h₀ := by
    by_contra hn
    have hg := not_le.mp hn
    have hm : (h₀+l₁)/2 ∈ Icc 0 R := by
      constructor <;> linarith only [hL.2,hU.1,hg]
    rcases hc _ hm with hh | hh <;> linarith only [hh.1,hh.2,hg]
  exact ⟨by linarith only [hs,hL.1,hU.2,ht],
    by linarith only [hs,hL.1,hU.2,ht],by linarith only [hs,hL.1,hU.2,ht]⟩

theorem two_intervals {l₀ h₀ l₁ h₁ R : ℝ}
    (hw₀ : l₀ < h₀) (hw₁ : l₁ < h₁) (hR : 0 < R)
    (hs : (h₀-l₀)+(h₁-l₁)=R)
    (hc : ∀ x ∈ Icc 0 R, (l₀ ≤ x ∧ x ≤ h₀) ∨ (l₁ ≤ x ∧ x ≤ h₁)) :
    (l₀=0 ∧ h₀=l₁ ∧ h₁=R) ∨ (l₁=0 ∧ h₁=l₀ ∧ h₀=R) := by
  rcases hc 0 ⟨le_rfl,hR.le⟩ with hL | hL <;>
    rcases hc R ⟨hR.le,le_rfl⟩ with hU | hU
  · exfalso
    linarith only [hs,hL.1,hU.2,hw₁]
  · exact Or.inl (ordered_intervals hw₀ hw₁ hs hL hU hc)
  · exact Or.inr (ordered_intervals hw₁ hw₀ (by linarith only [hs]) hL hU
      (fun x hx => (hc x hx).symm))
  · exfalso
    linarith only [hs,hL.1,hU.2,hw₀]

/-- The two original edge bands partition the full inward strip, in either label order. -/
def EdgePartition (C : Config) : Prop :=
  ((C.plank 0).lo=0 ∧ (C.plank 0).hi=(C.plank 1).lo ∧
    (C.plank 1).hi=C.relW 0+C.relW 1) ∨
  ((C.plank 1).lo=0 ∧ (C.plank 1).hi=(C.plank 0).lo ∧
    (C.plank 0).hi=C.relW 0+C.relW 1)

/-- Equality forces adjacency and the boundary anchor; neither is a premise. -/
theorem partition_of_equality (C : Config) (a : ℝ) (ha : 0 ≤ a ∧ a < 1)
    (hu0 : (C.plank 0).u=(1,0)) (hu1 : (C.plank 1).u=(1,0))
    (hu2 : (C.plank 2).u=(a,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C) : EdgePartition C := by
  classical
  have hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2 := by
    apply Proofs.Symmetry.forall_fin_three
    · simp [hu0]
    · simp [hu1]
    · simpa only [hu2] using And.intro ha.1 zero_le_one
  have hs0 : steps C 0=(C.relW 0,0) := by simp [steps,hu0]
  have hs1 : steps C 1=(C.relW 1,0) := by simp [steps,hu1]
  have hs2 : steps C 2=(0,C.relW 2) := by simp [steps,hu2,ha.2.le]
  have hall : shift (steps C) Finset.univ=(C.relW 0+C.relW 1,C.relW 2) := by
    simp only [shift,Fin.sum_univ_three,hs0,hs1,hs2,Prod.mk_add_mk,add_zero,zero_add]
  have hw0 := steps_self C hu 0
  have hw1 := steps_self C hu 1
  simp only [hs0,hu0,dot,one_mul,zero_mul,add_zero] at hw0
  simp only [hs1,hu1,dot,one_mul,zero_mul,add_zero] at hw1
  have hsum : C.deficit+C.relW 0+C.relW 1=1-C.relW 2 := by
    rw [Config.deficit,Config.sumRelW,Fin.sum_univ_three]
    ring
  have hcal := (isolated_calibration C a 0 0 ha ⟨le_rfl,zero_lt_one⟩
    ⟨le_rfl,zero_lt_one⟩ hu0 hu1 hu2 hw hδ he).2
  have hcov : Icc (0 : ℝ) (C.relW 0+C.relW 1) ⊆
      Icc (C.plank 0).lo (C.plank 0).hi ∪ Icc (C.plank 1).lo (C.plank 1).hi := by
    apply closed_interval_of_finite_exceptions (D := ∅)
      (isClosed_Icc.union isClosed_Icc) Set.finite_empty (add_pos (hw 0) (hw 1))
    intro x hx _
    by_contra hn
    have hn0 : ¬ ((C.plank 0).lo ≤ x ∧ x ≤ (C.plank 0).hi) := fun h => hn (Or.inl h)
    have hn1 : ¬ ((C.plank 1).lo ≤ x ∧ x ≤ (C.plank 1).hi) := fun h => hn (Or.inr h)
    have hz : (x,1-x) ∈ stdTriangle.set := by
      rw [Proofs.Quant.stdTriangle_set_eq]
      refine ⟨hx.1.le,?_,by dsimp; linarith⟩
      change 0 ≤ 1-x
      linarith only [hx.2,hsum,hδ,hw 2]
    have hv : (C.plank 2).hi < dot (C.plank 2).u (x,1-x) := by
      simp only [hu2,dot,one_mul]
      nlinarith only [hcal,mul_pos (sub_pos.mpr ha.2)
        (show 0 < 1-C.relW 2-x by linarith only [hx.2,hsum,hδ])]
    have hnone : ∀ i, ¬ ((C.plank i).lo ≤ dot (C.plank i).u (x,1-x) ∧
        dot (C.plank i).u (x,1-x) ≤ (C.plank i).hi) := by
      apply Proofs.Symmetry.forall_fin_three
      · simpa only [hu0,dot,one_mul,zero_mul,add_zero] using hn0
      · simpa only [hu1,dot,one_mul,zero_mul,add_zero] using hn1
      · exact fun h => (not_le_of_gt hv) h.2
    let s : Finset (Fin 3) := Finset.univ.filter (fun i => (C.plank i).hi < dot (C.plank i).u (x,1-x))
    have hs : (x,1-x) ∈ exteriorCells C s := by
      rw [exteriorCells,Plank.LinearBands.strictCell]
      intro i
      by_cases hi : (C.plank i).hi < dot (C.plank i).u (x,1-x)
      · simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and,hi,if_true] using hi
      · have hl : dot (C.plank i).u (x,1-x) < (C.plank i).lo :=
          lt_of_not_ge (fun h => hnone i ⟨h,le_of_not_gt hi⟩)
        simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and,hi,if_false] using hl
    have hsall : s=Finset.univ := Finset.eq_univ_of_forall
      (fun i => far_edge_all_high C hu hδ he s hz hs (by dsimp; ring) i (hw i))
    have hh := (common_vertex_cell_inequalities C hu hδ he s hz hs).1
    rw [hsall,hall] at hh
    change C.relW 0+C.relW 1 ≤ x at hh
    linarith only [hh,hx.2]
  exact two_intervals (by linarith only [hw0,hw 0]) (by linarith only [hw1,hw 1])
    (add_pos (hw 0) (hw 1)) (by linarith only [hw0,hw1]) (fun x hx => hcov hx)

theorem edge_union (C : Config)
    (hu0 : (C.plank 0).u=(1,0)) (hu1 : (C.plank 1).u=(1,0))
    (hp : EdgePartition C) :
    (C.plank 0).set ∪ (C.plank 1).set =
      {z | 0 ≤ z.1 ∧ z.1 ≤ C.relW 0+C.relW 1} := by
  ext z
  change (((C.plank 0).lo ≤ dot (C.plank 0).u z ∧ dot (C.plank 0).u z ≤ (C.plank 0).hi) ∨
    ((C.plank 1).lo ≤ dot (C.plank 1).u z ∧ dot (C.plank 1).u z ≤ (C.plank 1).hi)) ↔ _
  simp only [hu0,hu1,dot,one_mul,zero_mul,add_zero,Set.mem_ofPred_eq]
  have ho0 := (C.plank 0).lo_le_hi
  have ho1 := (C.plank 1).lo_le_hi
  rcases hp with ⟨hl,ht,hh⟩ | ⟨hl,ht,hh⟩
  · constructor
    · rintro (h | h) <;> constructor <;> linarith only [h.1,h.2,hl,ht,hh,ho0,ho1]
    · intro h
      by_cases hx : z.1 ≤ (C.plank 0).hi
      · left; constructor <;> linarith only [h.1,hl,hx]
      · right; constructor <;> linarith only [h.2,ht,hh,not_le.mp hx]
  · constructor
    · rintro (h | h) <;> constructor <;> linarith only [h.1,h.2,hl,ht,hh,ho0,ho1]
    · intro h
      by_cases hx : z.1 ≤ (C.plank 1).hi
      · right; constructor <;> linarith only [h.1,hl,hx]
      · left; constructor <;> linarith only [h.2,ht,hh,not_le.mp hx]

/-- Complete iff for two parallel edge bands and one transverse band:
the former are adjacent pieces of the inward edge strip, and the latter
has exactly its single-plank calibration. The endpoint conditions are
conclusions, with no clipping, adjacency or anchoring premise. -/
theorem equality_iff_split_edge (C : Config) (a : ℝ) (ha : 0 ≤ a ∧ a < 1)
    (hu0 : (C.plank 0).u=(1,0)) (hu1 : (C.plank 1).u=(1,0))
    (hu2 : (C.plank 2).u=(a,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔
      EdgePartition C ∧ (C.plank 2).lo=a*(1-C.relW 2) := by
  constructor
  · intro he
    exact ⟨partition_of_equality C a ha hu0 hu1 hu2 hw hδ he,
      (isolated_calibration C a 0 0 ha ⟨le_rfl,zero_lt_one⟩
        ⟨le_rfl,zero_lt_one⟩ hu0 hu1 hu2 hw hδ he).1⟩
  · rintro ⟨hpart,hcal⟩
    let T := swappedTriangle stdTriangle
    let F : (ℝ × ℝ) →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ).toAffineMap
    have hT : T.set=stdTriangle.set := swappedTriangle_set stdTriangle
    have hp : CommonExtremes T (C.plank 2) := by
      simpa [CommonExtremes,T,swappedTriangle,stdTriangle,hu2,dot] using And.intro ha.1 ha.2.le
    have hwidth : (C.plank 2).relWidth T=C.relW 2 := swappedTriangle_width stdTriangle _
    have hR : C.relW 0+C.relW 1+(C.plank 2).relWidth T < 1 := by
      rw [hwidth]
      simp only [Config.deficit,Config.sumRelW,Fin.sum_univ_three] at hδ
      linarith only [hδ]
    have hc : lower T (C.plank 2)=(1-(C.plank 2).relWidth T)*slope T (C.plank 2) := by
      rw [hwidth]
      simpa [CommonMiddleAffineTransport.lower,CommonMiddleAffineTransport.slope,
        CommonMiddleAffineTransport.span,T,swappedTriangle,stdTriangle,hu2,dot,mul_comm] using hcal
    have hpair : (C.plank 0).set ∪ (C.plank 1).set =
        {z | 0 ≤ F z ∧ F z ≤ C.relW 0+C.relW 1} := edge_union C hu0 hu1 hpart
    have hthree : (⋃ i, (C.plank i).set) =
        (C.plank 0).set ∪ ((C.plank 1).set ∪ (C.plank 2).set) := by
      ext z
      simp only [Set.mem_iUnion,Set.mem_union,Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
      rfl
    have hgap : T.set \ ({z | 0 ≤ F z ∧ F z ≤ C.relW 0+C.relW 1} ∪ (C.plank 2).set)=
        C.uncovered := by
      rw [hT,← hpair,Config.uncovered,hthree,union_assoc]
    have hg := (TriangleSplitEdgeFamily.edge_single_iff T
      (hT.symm ▸ Proofs.GapCells.isCompact_stdTriangle) F rfl rfl rfl (C.plank 2) hp
      (by rw [hwidth]; exact hw 2) (C.relW 0+C.relW 1) (add_pos (hw 0) (hw 1)).le hR).mpr hc
    rw [hgap,hT,Proofs.Quant.volume_stdTriangle,hwidth] at hg
    norm_num only [ENNReal.toReal_ofReal] at hg
    have hd : 1-(C.relW 0+C.relW 1)-C.relW 2=C.deficit := by
      simp only [Config.deficit,Config.sumRelW,Fin.sum_univ_three]
      ring
    rw [hd] at hg
    simpa only [TriangleEqualityReductions.Equality,max_eq_right hδ.le,Config.gapArea] using hg

end Quant.TriangleMixedParallelEdge

/-- info: 'Quant.TriangleMixedParallelEdge.partition_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedParallelEdge.partition_of_equality

/-- info: 'Quant.TriangleMixedParallelEdge.equality_iff_split_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedParallelEdge.equality_iff_split_edge
