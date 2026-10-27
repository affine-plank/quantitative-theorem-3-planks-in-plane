/- An exhaustive geometric catalogue for normalized common-minimum triples. -/
module
public import Plank.Proofs.Quant.TriangleCommonMinimumDirections

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCommonMinimumCatalogue
open Set MeasureTheory CommonMiddleAffineTransport CommonMiddleNullWindow
open TriangleCommonMinimumDirections CommonVertexTranslationEquality
open scoped BigOperators

def StackFamily (C : Config) : Prop := StackChart C ∧ OrderedStack stdTriangle C.plank

def MixedFamily (C : Config) : Prop :=
  ∃ a b c : ℝ, (0 ≤ a ∧ a < 1) ∧ (0 ≤ b ∧ b < 1) ∧ (0 ≤ c ∧ c < 1) ∧
    (C.plank 0).u=(1,b) ∧ (C.plank 1).u=(1,c) ∧ (C.plank 2).u=(a,1) ∧
    ((a=0 ∧ (C.plank 2).lo=0 ∧ PairOrderedStack stdTriangle (C.plank 0) (C.plank 1)) ∨
     (b=0 ∧ c=0 ∧ TriangleMixedParallelEdge.EdgePartition C ∧
       (C.plank 2).lo=a*(1-C.relW 2)))

def FarFamily (C : Config) : Prop :=
  ∃ a b : ℝ, (0 ≤ a ∧ a < 1) ∧ (0 ≤ b ∧ b < 1) ∧
    (C.plank 0).u=(1,b) ∧ (C.plank 1).u=(a,1) ∧ (C.plank 2).u=(1,1) ∧
    (C.plank 2).hi=1 ∧
      ((a=0 ∧ (C.plank 1).lo=0 ∧ (C.plank 0).lo=b*(1-C.relW 2-C.relW 0)) ∨
       (b=0 ∧ (C.plank 0).lo=0 ∧ (C.plank 1).lo=a*(1-C.relW 2-C.relW 1)))

/-- Four geometric types, with labels and the two nonminimum vertices
free: an ordered stack; an edge band plus an ordered pair; two adjacent
pieces of an edge band plus a calibrated band; two edge bands plus a
calibrated band. No area predicate occurs in the family definition. -/
def Catalogue (C : Config) : Prop :=
  ∃ flip : Bool, ∃ σ : Equiv.Perm (Fin 3),
    StackFamily (present C flip σ) ∨ MixedFamily (present C flip σ) ∨
      FarFamily (present C flip σ)

theorem stack_iff (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hchart : StackChart C) (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔ OrderedStack stdTriangle C.plank := by
  have hc : ∀ i, CommonExtremes stdTriangle (C.plank i) := by
    intro i
    simpa [CommonExtremes,stdTriangle,dot] using And.intro (hu i).2 (hchart i)
  have hR : 0 < ∑ i, (C.plank i).relWidth stdTriangle := by
    rw [Fin.sum_univ_three]
    exact add_pos (add_pos (hw 0) (hw 1)) (hw 2)
  have hR1 : (∑ i, (C.plank i).relWidth stdTriangle) < 1 := by
    change C.sumRelW < 1
    dsimp only [Config.deficit] at hδ
    linarith only [hδ]
  have he := CommonMiddleAffineTransport.equality_iff_orderedStack stdTriangle C.plank hc hw hR hR1
  rw [Proofs.Quant.volume_stdTriangle] at he
  norm_num only [ENNReal.toReal_ofReal] at he
  unfold TriangleEqualityReductions.Equality
  rw [max_eq_right hδ.le]
  simpa only [Config.deficit,Config.sumRelW,Config.relW,Config.gapArea,Config.uncovered] using he

theorem family_of_equality (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (hchart : StackChart C ∨ MixedChart C ∨ FarChart C)
    (he : TriangleEqualityReductions.Equality C) :
    StackFamily C ∨ MixedFamily C ∨ FarFamily C := by
  rcases hchart with hs | ⟨a,b,c,ha,hb,hc,h0,h1,h2⟩ | ⟨a,b,ha,hb,h0,h1,h2⟩
  · exact Or.inl ⟨hs,(stack_iff C hu hs hw hδ).mp he⟩
  · exact Or.inr (Or.inl ⟨a,b,c,ha,hb,hc,h0,h1,h2,
      (TriangleMixedCatalogue.equality_iff_families C a b c ha hb hc h0 h1 h2 hw hδ).mp he⟩)
  · exact Or.inr (Or.inr ⟨a,b,ha,hb,h0,h1,h2,
      (TriangleFarCatalogue.equality_iff_families C a b ha hb h0 h1 h2 hw hδ).mp he⟩)

theorem equality_of_family (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (hf : StackFamily C ∨ MixedFamily C ∨ FarFamily C) :
    TriangleEqualityReductions.Equality C := by
  rcases hf with ⟨hs,hf⟩ | ⟨a,b,c,ha,hb,hc,h0,h1,h2,hf⟩ | ⟨a,b,ha,hb,h0,h1,h2,hf⟩
  · exact (stack_iff C hu hs hw hδ).mpr hf
  · exact (TriangleMixedCatalogue.equality_iff_families C a b c ha hb hc h0 h1 h2 hw hδ).mpr hf
  · exact (TriangleFarCatalogue.equality_iff_families C a b ha hb h0 h1 h2 hw hδ).mpr hf

/-- Complete exhaustion for every normalized common-minimum direction
triple, including all edge ties and repetitions. Every band is original;
only a permutation and a triangle reflection enter the family list. -/
theorem equality_iff_catalogue (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hm : ∀ i, max (C.plank i).u.1 (C.plank i).u.2=1)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔ Catalogue C := by
  constructor
  · intro he
    obtain ⟨flip,σ,hchart⟩ := TriangleCommonMinimumDirections.exhaustive C hu hm
    refine ⟨flip,σ,family_of_equality _ (present_nonneg C hu flip σ)
      (fun i => by rw [present_width]; exact hw (σ i))
      (by rwa [present_deficit]) hchart ?_⟩
    exact (equality_iff_of_equiv (present_equiv C flip σ)).mp he
  · rintro ⟨flip,σ,hf⟩
    apply (equality_iff_of_equiv (present_equiv C flip σ)).mpr
    exact equality_of_family _ (present_nonneg C hu flip σ)
      (fun i => by rw [present_width]; exact hw (σ i))
      (by rwa [present_deficit]) hf

end Quant.TriangleCommonMinimumCatalogue

/-- info: 'Quant.TriangleCommonMinimumCatalogue.equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCommonMinimumCatalogue.equality_iff_catalogue
