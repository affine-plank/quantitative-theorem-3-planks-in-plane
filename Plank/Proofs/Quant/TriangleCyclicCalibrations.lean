/- Every band in a strict cyclic equality configuration is calibrated. -/
module
public import Plank.Proofs.Quant.TriangleCyclicVertexCalibration

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicCalibrations
open Proofs.Basic Proofs.Transport Proofs.Symmetry CommonVertex OrdinalArea CyclicArea
open TriangleEqualityReductions TriangleEndpointPositions TriangleCyclicVertexCalibration

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

theorem ab_calibration (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    (C.plank 0).lo=b*(1-widths C 0) ∧
      (C.plank 0).hi=b+(1-b)*widths C 0 := by
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
  have h := ac_calibration Q ha hb ⟨sub_pos.mpr hc.2,by linarith only [hc.1]⟩
    hQ0 hQ1 hQ2 hpQ hdQ heQ
  simpa [Q,rearranged,swapped,swapP,widths] using h

private def cycle : Equiv.Perm (Fin 3) :=
  ⟨![1,2,0],![2,0,1],by decide,by decide⟩

theorem bc_calibration (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    (C.plank 2).lo=-(1-c)*widths C 2 ∧
      (C.plank 2).hi=c*widths C 2 := by
  let Q := rearranged (rotated (rotated C)) cycle ![true,false,true]
  have hQ0 : (Q.plank 0).u=(1,1-a) := by
    apply Prod.ext <;> simp [Q,rearranged,cycle,rotated,rotP,flipP,hu1]
  have hQ1 : (Q.plank 1).u=(1-c,1) := by
    apply Prod.ext <;> simp [Q,rearranged,cycle,rotated,rotP,flipP,hu2]
    ring
  have hQ2 : (Q.plank 2).u=(b,b-1) := by
    apply Prod.ext <;> simp [Q,rearranged,cycle,rotated,rotP,flipP,hu0]
  have hpQ : ∀ i, 0 < Q.relW i := by
    intro i
    simpa only [Q,rearranged_width,rotated_width] using hp (cycle i)
  have hdQ : 0 < Q.deficit := by
    simpa only [Q,rearranged_deficit,rotated_deficit] using hδ
  have heQ : Equality Q := rearranged_equality _ _ _ (rotated_equality _ (rotated_equality C he))
  have h := ac_calibration Q ⟨sub_pos.mpr ha.2,by linarith only [ha.1]⟩
    ⟨sub_pos.mpr hc.2,by linarith only [hc.1]⟩ hb hQ0 hQ1 hQ2 hpQ hdQ heQ
  have hw : widths Q 1=widths C 2 := by
    dsimp [Q,rearranged,cycle,rotated,rotP,widths]
    ring
  rw [hw] at h
  have hlo : (Q.plank 1).lo=(C.plank 2).lo-(c-1) := by
    dsimp [Q,rearranged,cycle,rotated,rotP]
    rw [hu2]
    dsimp
    ring
  have hhi : (Q.plank 1).hi=(C.plank 2).hi-(c-1) := by
    dsimp [Q,rearranged,cycle,rotated,rotP]
    rw [hu2]
    dsimp
    ring
  rw [hlo,hhi] at h
  constructor <;> nlinarith only [h.1,h.2]

/-- Actual area equality and positive widths force all three exact windows;
no clipping, endpoint placement, or calibration hypothesis is supplied. -/
theorem abc_calibration (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    ((C.plank 0).lo=b*(1-widths C 0) ∧ (C.plank 0).hi=b+(1-b)*widths C 0) ∧
    ((C.plank 1).lo=a*(1-widths C 1) ∧ (C.plank 1).hi=a+(1-a)*widths C 1) ∧
    ((C.plank 2).lo=-(1-c)*widths C 2 ∧ (C.plank 2).hi=c*widths C 2) :=
  ⟨ab_calibration C hb ha hc hu0 hu1 hu2 hp hδ he,
    ac_calibration C hb ha hc hu0 hu1 hu2 hp hδ he,
    bc_calibration C hb ha hc hu0 hu1 hu2 hp hδ he⟩

end Quant.TriangleCyclicCalibrations

/-- info: 'Quant.TriangleCyclicCalibrations.abc_calibration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicCalibrations.abc_calibration
