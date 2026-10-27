/- The complete two-band catalogue for mixed maxima and a common minimum. -/
module
public import Plank.Proofs.Quant.TriangleMixedCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedPairCatalogue
open Set MeasureTheory CommonMiddleNullWindow CommonMiddleAffineTransport
open TriangleMixedParallelEdge

theorem normalized_width (p : Plank) (b : ℝ) (hb : 0 ≤ b ∧ b < 1)
    (hu : p.u=(1,b)) : p.relWidth stdTriangle=p.hi-p.lo := by
  simp [Plank.relWidth,Proofs.Transport.stdTriangle_width_eq,hu,
    max_eq_left hb.2.le,min_eq_right hb.2.le,min_eq_left hb.1]

theorem halves_stack_iff (p : Plank) (b : ℝ) (hb : 0 ≤ b ∧ b < 1)
    (hu : p.u=(1,b)) (hp : 0 < p.relWidth stdTriangle) :
    PairOrderedStack stdTriangle (halfLo p) (halfHi p) ↔
      p.lo=b*(1-p.relWidth stdTriangle) := by
  have hs : CommonMiddleAffineTransport.slope stdTriangle p=b := by
    simp [CommonMiddleAffineTransport.slope,span,stdTriangle,hu,dot]
  have hl : lower stdTriangle p=p.lo := by simp [lower,span,stdTriangle,hu,dot]
  have hh : upper stdTriangle p=p.hi := by simp [upper,span,stdTriangle,hu,dot]
  have hw := normalized_width p b hb hu
  simp only [PairOrderedStack,slope_halfLo,slope_halfHi,hs,halfLo_relWidth,
    halfHi_relWidth,lower_halfLo,lower_halfHi,hl,hh,le_refl,true_and]
  constructor
  · rintro (⟨h0,_⟩ | ⟨h1,h0⟩)
    · nlinarith only [h0]
    · exfalso
      nlinarith only [h1,h0,hw,hp]
  · intro h
    left
    constructor <;> nlinarith only [h,hw]

theorem halves_edge_iff (p q : Plank) (hu : p.u=(1,0)) :
    EdgePartition (⟨splitFamily p q⟩ : Config) ↔ p.lo=0 := by
  have hw := normalized_width p 0 ⟨le_rfl,by norm_num⟩ hu
  change (p.lo=0 ∧ (p.lo+p.hi)/2=(p.lo+p.hi)/2 ∧
      p.hi=(halfLo p).relWidth stdTriangle+(halfHi p).relWidth stdTriangle) ∨
    ((p.lo+p.hi)/2=0 ∧ p.hi=p.lo ∧
      (p.lo+p.hi)/2=(halfLo p).relWidth stdTriangle+(halfHi p).relWidth stdTriangle) ↔ _
  rw [halfLo_relWidth,halfHi_relWidth]
  constructor
  · rintro (⟨h,_,_⟩ | ⟨h0,h1,_⟩)
    · exact h
    · linarith only [h0,h1]
  · intro h
    exact Or.inl ⟨h,rfl,by linarith only [h,hw]⟩

/-- With a common minimum but different maximum vertices, two positive
bands are sharp exactly when one is an inward edge band and the other
has its calibrated position. Arbitrary original band positions are allowed. -/
theorem equality_iff_families (p q : Plank) (a b : ℝ)
    (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1)
    (hpu : p.u=(1,b)) (hqu : q.u=(a,1))
    (hp : 0 < p.relWidth stdTriangle) (hq : 0 < q.relWidth stdTriangle)
    (hR : p.relWidth stdTriangle+q.relWidth stdTriangle < 1) :
    pairGap p q=(1-(p.relWidth stdTriangle+q.relWidth stdTriangle))^2*(1/2) ↔
      (a=0 ∧ q.lo=0 ∧ p.lo=b*(1-p.relWidth stdTriangle)) ∨
      (b=0 ∧ p.lo=0 ∧ q.lo=a*(1-q.relWidth stdTriangle)) := by
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
  have he : TriangleEqualityReductions.Equality D ↔
      pairGap p q=(1-(p.relWidth stdTriangle+q.relWidth stdTriangle))^2*(1/2) := by
    rw [TriangleEqualityReductions.Equality,hgap,max_eq_right hδ.le,hdef]
  have hf := TriangleMixedCatalogue.equality_iff_families D a b b ha hb hb hpu hpu hqu hw hδ
  rw [he] at hf
  refine hf.trans ?_
  change ((a=0 ∧ q.lo=0 ∧ PairOrderedStack stdTriangle (halfLo p) (halfHi p)) ∨
    (b=0 ∧ b=0 ∧ EdgePartition D ∧ q.lo=a*(1-q.relWidth stdTriangle))) ↔ _
  rw [halves_stack_iff p b hb hpu hp]
  constructor
  · rintro (h | ⟨hb0,_,hpart,hqlo⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hb0,(halves_edge_iff p q (by simpa [hb0] using hpu)).mp hpart,hqlo⟩
  · rintro (h | ⟨hb0,hplo,hqlo⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hb0,hb0,(halves_edge_iff p q (by simpa [hb0] using hpu)).mpr hplo,hqlo⟩

end Quant.TriangleMixedPairCatalogue

/-- info: 'Quant.TriangleMixedPairCatalogue.equality_iff_families' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedPairCatalogue.equality_iff_families
