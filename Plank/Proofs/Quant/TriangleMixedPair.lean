/- Two strictly oblique mixed directions cannot attain triangle equality. -/
module
public import Plank.Proofs.Quant.TriangleMixedStrict

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedPair
open Set MeasureTheory CommonMiddleNullWindow

/-- Splitting one of two positive bands into adjacent halves preserves its
actual union and width, so the strict mixed three-band exclusion also rules
out the entire corresponding two-band sector. -/
theorem pair_ne (p q : Plank) (a b : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hpu : p.u=(1,b)) (hqu : q.u=(a,1))
    (hp : 0 < p.relWidth stdTriangle) (hq : 0 < q.relWidth stdTriangle)
    (hR : p.relWidth stdTriangle+q.relWidth stdTriangle < 1) :
    pairGap p q ≠ (1-(p.relWidth stdTriangle+q.relWidth stdTriangle))^2*(1/2) := by
  let D : Config := ⟨splitFamily p q⟩
  have hsum : D.sumRelW=p.relWidth stdTriangle+q.relWidth stdTriangle :=
    split_sum stdTriangle p q
  have hdef : D.deficit=1-(p.relWidth stdTriangle+q.relWidth stdTriangle) := by
    rw [Config.deficit,hsum]
  have hδ : 0 < D.deficit := by rw [hdef]; linarith only [hR]
  have hw : ∀ i, 0 < D.relW i := by
    apply Proofs.Symmetry.forall_fin_three
    · change 0 < (halfLo p).relWidth stdTriangle
      rw [halfLo_relWidth]
      exact half_pos hp
    · change 0 < (halfHi p).relWidth stdTriangle
      rw [halfHi_relWidth]
      exact half_pos hp
    · exact hq
  have hgap : D.gapArea=pairGap p q := by
    change (volume (stdTriangle.set \ ⋃ i, (splitFamily p q i).set)).toReal=pairGap p q
    rw [split_union]
    rfl
  intro he
  apply TriangleMixedStrict.not_equality D a b b ha hb hb hpu hpu hqu hw hδ
  rw [TriangleEqualityReductions.Equality,hgap,max_eq_right hδ.le,hdef]
  exact he

/-- The arbitrary location and direction of a null third line cannot repair
the strict loss from the two mixed positive bands. -/
theorem not_equality_of_null (C : Config) (a b : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hw0 : 0 < C.relW 0) (hw1 : 0 < C.relW 1)
    (hn : (C.plank 2).lo=(C.plank 2).hi) (hδ : 0 < C.deficit) :
    ¬ TriangleEqualityReductions.Equality C := by
  have hw2 : C.relW 2=0 := relWidth_of_degenerate hn
  have hd : C.deficit=1-(C.relW 0+C.relW 1) := by
    simp only [Config.deficit,Config.sumRelW,Fin.sum_univ_three,hw2,add_zero]
  intro he
  apply pair_ne (C.plank 0) (C.plank 1) a b ha hb hu0 hu1 hw0 hw1
    (by change C.relW 0+C.relW 1 < 1; linarith only [hδ,hd])
  rw [TriangleEqualityReductions.Equality,gapArea_of_degenerate C hn,
    max_eq_right hδ.le,hd] at he
  exact he

end Quant.TriangleMixedPair

/-- info: 'Quant.TriangleMixedPair.pair_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedPair.pair_ne
/-- info: 'Quant.TriangleMixedPair.not_equality_of_null' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedPair.not_equality_of_null
