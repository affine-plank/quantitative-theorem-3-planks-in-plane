/- Strict endpoint placement in every open triangle direction sector. -/
module
public import Plank.Proofs.Quant.TriangleEndpointNecessity

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleEndpointPositions
open Set MeasureTheory Proofs.Basic Proofs.Transport Proofs.Symmetry
open TriangleEqualityReductions

def swapped (C : Config) : Config := ⟨fun i => swapP (C.plank i)⟩
def rotated (C : Config) : Config := ⟨fun i => rotP (C.plank i)⟩
def flipped (C : Config) : Config := ⟨fun i => flipP (C.plank i)⟩

theorem swapped_move (C : Config) : Move C (swapped C) :=
  Move.swap C (fun i => (swapP (C.plank i)).u_ne_zero)

theorem rotated_move (C : Config) : Move C (rotated C) :=
  Move.rot C (fun i => (rotP (C.plank i)).u_ne_zero)

theorem swapped_width (C : Config) (i : Fin 3) : (swapped C).relW i=C.relW i := by
  simp only [Config.relW,swapped,swapP,Plank.relWidth,width_swap]

theorem rotated_width (C : Config) (i : Fin 3) : (rotated C).relW i=C.relW i := by
  simp only [Config.relW,rotated,rotP,Plank.relWidth,width_rot]
  ring

theorem flipped_width (C : Config) (i : Fin 3) : (flipped C).relW i=C.relW i := by
  simp only [Config.relW,flipped,flipP,Plank.relWidth,width_neg]
  ring

theorem swapped_deficit (C : Config) : (swapped C).deficit=C.deficit := by
  simp only [Config.deficit,Config.sumRelW,swapped_width]

theorem rotated_deficit (C : Config) : (rotated C).deficit=C.deficit := by
  simp only [Config.deficit,Config.sumRelW,rotated_width]

theorem flipped_deficit (C : Config) : (flipped C).deficit=C.deficit := by
  simp only [Config.deficit,Config.sumRelW,flipped_width]

theorem flip_set (p : Plank) : (flipP p).set=p.set := by
  ext z
  change (-p.hi ≤ dot (-p.u) z ∧ dot (-p.u) z ≤ -p.lo) ↔
    (p.lo ≤ dot p.u z ∧ dot p.u z ≤ p.hi)
  rw [dot_neg_left]
  simp only [neg_le_neg_iff,and_comm]

theorem flipped_gap (C : Config) : (flipped C).gapArea=C.gapArea := by
  simp only [Config.gapArea,Config.uncovered,flipped,flip_set]

theorem swapped_equality (C : Config) (he : Equality C) : Equality (swapped C) := by
  simpa only [Equality,swapped_deficit,← (swapped_move C).gapArea_eq] using he

theorem rotated_equality (C : Config) (he : Equality C) : Equality (rotated C) := by
  simpa only [Equality,rotated_deficit,← (rotated_move C).gapArea_eq] using he

theorem flipped_equality (C : Config) (he : Equality C) : Equality (flipped C) := by
  simpa only [Equality,flipped_deficit,flipped_gap] using he

/-- Reflect the maximum vertex to the minimum vertex and apply the proved
quadratic-cap exclusion. The original upper endpoint must be strictly inside. -/
theorem upper_lt_one (C : Config) (j : Fin 3) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (hu : (C.plank j).u=(a,1))
    (hp : 0 < C.relW j) (hδ : 0 < C.deficit) (he : Equality C) :
    (C.plank j).hi < 1 := by
  let Q := flipped (rotated (swapped C))
  have hQ : (Q.plank j).u=(1-a,1) := by
    apply Prod.ext <;> simp [Q,flipped,rotated,swapped,flipP,rotP,swapP,hu]
  have hpQ : 0 < Q.relW j := by
    simpa only [Q,flipped_width,rotated_width,swapped_width] using hp
  have hdQ : 0 < Q.deficit := by
    simpa only [Q,flipped_deficit,rotated_deficit,swapped_deficit] using hδ
  have heQ : Equality Q := flipped_equality _ (rotated_equality _ (swapped_equality C he))
  have hl := TriangleEndpointNecessity.lower_pos Q j (1-a)
    (sub_pos.mpr ha1) (by linarith only [ha]) hQ hpQ hdQ heQ
  change 0 < -((C.plank j).hi-(C.plank j).u.2) at hl
  rw [hu] at hl
  dsimp only at hl
  linarith only [hl]

theorem ac_internal (C : Config) (j : Fin 3) (a : ℝ)
    (ha : 0 < a ∧ a < 1) (hu : (C.plank j).u=(a,1))
    (hp : 0 < C.relW j) (hδ : 0 < C.deficit) (he : Equality C) :
    0 < (C.plank j).lo ∧ (C.plank j).hi < 1 :=
  ⟨TriangleEndpointNecessity.lower_pos C j a ha.1 ha.2.le hu hp hδ he,
    upper_lt_one C j a ha.1.le ha.2 hu hp hδ he⟩

theorem ab_internal (C : Config) (j : Fin 3) (b : ℝ)
    (hb : 0 < b ∧ b < 1) (hu : (C.plank j).u=(1,b))
    (hp : 0 < C.relW j) (hδ : 0 < C.deficit) (he : Equality C) :
    0 < (C.plank j).lo ∧ (C.plank j).hi < 1 := by
  apply ac_internal (swapped C) j b hb
  · simp only [swapped,swapP,hu]
  · simpa only [swapped_width] using hp
  · simpa only [swapped_deficit] using hδ
  · exact swapped_equality C he

theorem bc_internal (C : Config) (j : Fin 3) (c : ℝ)
    (hc : 0 < c ∧ c < 1) (hu : (C.plank j).u=(c,c-1))
    (hp : 0 < C.relW j) (hδ : 0 < C.deficit) (he : Equality C) :
    c-1 < (C.plank j).lo ∧ (C.plank j).hi < c := by
  let Q := rotated (rotated C)
  have hQ : (Q.plank j).u=(1-c,1) := by
    apply Prod.ext <;> simp [Q,rotated,rotP,hu]
    ring
  have hpQ : 0 < Q.relW j := by simpa only [Q,rotated_width] using hp
  have hdQ : 0 < Q.deficit := by simpa only [Q,rotated_deficit] using hδ
  have heQ : Equality Q := rotated_equality _ (rotated_equality C he)
  have hl := ac_internal Q j (1-c) ⟨sub_pos.mpr hc.2,by linarith only [hc.1]⟩ hQ hpQ hdQ heQ
  change 0 < (C.plank j).lo-(C.plank j).u.1-((C.plank j).u.2-(C.plank j).u.1) ∧
    (C.plank j).hi-(C.plank j).u.1-((C.plank j).u.2-(C.plank j).u.1) < 1 at hl
  rw [hu] at hl
  dsimp only at hl
  constructor <;> linarith only [hl.1,hl.2]

/-- Every positive cyclic equality band lies strictly inside its own
shadow interval. This rules out all six extreme-vertex contacts and every
band endpoint outside the triangle; no placement hypothesis is supplied. -/
theorem abc_internal (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    (0 < (C.plank 0).lo ∧ (C.plank 0).hi < 1) ∧
    (0 < (C.plank 1).lo ∧ (C.plank 1).hi < 1) ∧
    (c-1 < (C.plank 2).lo ∧ (C.plank 2).hi < c) :=
  ⟨ab_internal C 0 b hb hu0 (hp 0) hδ he,
    ac_internal C 1 a ha hu1 (hp 1) hδ he,
    bc_internal C 2 c hc hu2 (hp 2) hδ he⟩

end Quant.TriangleEndpointPositions

/-- info: 'Quant.TriangleEndpointPositions.abc_internal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleEndpointPositions.abc_internal
