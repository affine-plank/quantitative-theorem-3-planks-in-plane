/- Complete geometric families in the common-minimum mixed-maxima chart. -/
module
public import Plank.Proofs.Quant.TriangleMixedParallelEdge

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedCatalogue
open CommonVertexTranslationEquality CommonMiddleNullWindow
open TriangleMixedParallelEdge

/-- Complete exhaustion when two normals maximize at X and one at Y,
all minimize at O, and no normal ties its two maximum vertices.

The only families are an inward Y-edge band plus an ordered pair with
common extremes, or two adjacent pieces of an inward X-edge band plus
one calibrated transverse band. Zero slope parameters and arbitrary
original endpoints are included; all three actual widths are positive.
This theorem is the complete stated chart, not the full triangle catalogue. -/
theorem equality_iff_families (C : Config) (a b c : ℝ)
    (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1) (hc : 0 ≤ c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(1,c))
    (hu2 : (C.plank 2).u=(a,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔
      (a=0 ∧ (C.plank 2).lo=0 ∧ PairOrderedStack stdTriangle (C.plank 0) (C.plank 1)) ∨
      (b=0 ∧ c=0 ∧ EdgePartition C ∧ (C.plank 2).lo=a*(1-C.relW 2)) := by
  constructor
  · intro he
    by_cases ha0 : a=0
    · subst a
      exact Or.inl ⟨rfl,(TriangleMixedCalibration.edge_equality_iff C b c hb hc
        hu0 hu1 hu2 hw hδ).mp he⟩
    · have hap : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
      have hb0 : b=0 := by
        by_contra hbn
        have hbp : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hbn)
        exact TriangleMixedOneEdge.not_equality_with_boundary C a b c
          ⟨hap,ha.2⟩ ⟨hbp,hb.2⟩ hc hu0 hu1 hu2 hw hδ he
      have hc0 : c=0 := by
        by_contra hcn
        have hcp : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hcn)
        let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
        let D : Config := ⟨C.plank ∘ σ⟩
        have hD0 : D.plank 0=C.plank 1 := by simp [D,σ]
        have hD1 : D.plank 1=C.plank 0 := by simp [D,σ]
        have hD2 : D.plank 2=C.plank 2 := by simp [D,σ,Equiv.swap_apply_def]
        have hED : C.Equiv D := Relation.EqvGen.rel _ _ (Move.relabel C σ)
        have hd : D.deficit=C.deficit := by simp only [Config.deficit,← hED.sumRelW_eq]
        exact TriangleMixedOneEdge.not_equality_with_boundary D a c b
          ⟨hap,ha.2⟩ ⟨hcp,hc.2⟩ hb (by rw [hD0,hu1]) (by rw [hD1,hu0])
          (by rw [hD2,hu2]) (fun i => hw (σ i)) (hd.symm ▸ hδ)
          ((equality_iff_of_equiv hED).mp he)
      subst b
      subst c
      exact Or.inr ⟨rfl,rfl,(equality_iff_split_edge C a ha hu0 hu1 hu2 hw hδ).mp he⟩
  · rintro (⟨ha0,hl,hs⟩ | ⟨hb0,hc0,hpart,hcal⟩)
    · subst a
      exact (TriangleMixedCalibration.edge_equality_iff C b c hb hc hu0 hu1 hu2 hw hδ).mpr ⟨hl,hs⟩
    · subst b
      subst c
      exact (equality_iff_split_edge C a ha hu0 hu1 hu2 hw hδ).mpr ⟨hpart,hcal⟩

end Quant.TriangleMixedCatalogue

/-- info: 'Quant.TriangleMixedCatalogue.equality_iff_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedCatalogue.equality_iff_families
