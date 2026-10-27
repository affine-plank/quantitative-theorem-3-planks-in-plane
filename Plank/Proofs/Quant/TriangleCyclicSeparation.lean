/- Both pure cyclic threshold cells are strictly separated at actual equality. -/
module
public import Plank.Proofs.Quant.TriangleCyclicLowerSlack

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicSeparation
open Proofs.Basic Proofs.Transport Proofs.Symmetry CommonVertex OrdinalArea CyclicArea
open TriangleEqualityReductions TriangleEndpointPositions TriangleCyclicLowerSlack
open CyclicBadThresholds CyclicPairAreas CyclicWeightedThresholdGeometry

private def rearranged (C : Config) (σ : Equiv.Perm (Fin 3))
    (f : Fin 3 → Bool) : Config :=
  ⟨fun i => if f i then flipP (C.plank (σ i)) else C.plank (σ i)⟩

private theorem rearranged_width (C : Config) (σ : Equiv.Perm (Fin 3))
    (f : Fin 3 → Bool) (i : Fin 3) :
    (rearranged C σ f).relW i=C.relW (σ i) := by
  dsimp only [Config.relW,rearranged]
  split_ifs
  · simp only [Plank.relWidth,flipP,width_neg]
    ring
  · rfl

private theorem rearranged_deficit (C : Config) (σ : Equiv.Perm (Fin 3))
    (f : Fin 3 → Bool) : (rearranged C σ f).deficit=C.deficit := by
  simp only [Config.deficit,Config.sumRelW,rearranged_width]
  rw [Equiv.sum_comp σ]

private theorem rearranged_equality (C : Config) (σ : Equiv.Perm (Fin 3))
    (f : Fin 3 → Bool) (he : Equality C) : Equality (rearranged C σ f) := by
  have hs (i : Fin 3) : ((rearranged C σ f).plank i).set=(C.plank (σ i)).set := by
    dsimp only [rearranged]
    split_ifs
    · exact flip_set _
    · rfl
  have hg : (rearranged C σ f).gapArea=(⟨C.plank ∘ σ⟩ : Config).gapArea := by
    simp only [Config.gapArea,Config.uncovered,hs]
    rfl
  simpa only [Equality,rearranged_deficit,hg,← (Move.relabel C σ).gapArea_eq] using he

theorem upper_slack_neg (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    thresholdSlack (1-a) b c (upperLevels C c)<0 := by
  classical
  let Q := rearranged (swapped C) (Equiv.swap 0 1) ![false,false,true]
  have hQ0 : (Q.plank 0).u=(1,a) := by simp [Q,rearranged,swapped,swapP,hu1]
  have hQ1 : (Q.plank 1).u=(b,1) := by simp [Q,rearranged,swapped,swapP,hu0]
  have hQ2 : (Q.plank 2).u=(1-c,(1-c)-1) := by
    have hswap : (Equiv.swap (0 : Fin 3) 1) 2=2 := by decide
    apply Prod.ext <;> simp [Q,rearranged,swapped,swapP,flipP,hswap,hu2]
  have hpQ : ∀ i, 0 < Q.relW i := by
    intro i
    simpa only [Q,rearranged_width,swapped_width] using hp ((Equiv.swap 0 1) i)
  have hdQ : 0 < Q.deficit := by
    simpa only [Q,rearranged_deficit,swapped_deficit] using hδ
  have heQ : Equality Q := rearranged_equality _ _ _ (swapped_equality C he)
  have h := lower_slack_pos Q ha hb ⟨sub_pos.mpr hc.2,by linarith only [hc.1]⟩
    hQ0 hQ1 hQ2 hpQ hdQ heQ
  have hswap : (Equiv.swap (0 : Fin 3) 1) 2=2 := by decide
  have hid : thresholdSlack (1-b) a (1-c) (lowerLevels Q (1-c)) =
      -thresholdSlack (1-a) b c (upperLevels C c) := by
    simp [thresholdSlack,lowerLevels,upperLevels,Q,rearranged,swapped,swapP,flipP,hswap,
      k0,k1,k2]
    ring
  rw [hid] at h
  linarith only [h]

end Quant.TriangleCyclicSeparation

/-- info: 'Quant.TriangleCyclicSeparation.upper_slack_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicSeparation.upper_slack_neg
