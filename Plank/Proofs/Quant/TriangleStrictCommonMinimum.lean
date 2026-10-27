/- Exhaustion of the strictly oblique common-minimum triangle sector. -/
module
public import Plank.Proofs.Quant.TriangleMixedTransport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleStrictCommonMinimum
open Set MeasureTheory CommonVertexTranslationEquality CommonMiddleAffineTransport
open scoped BigOperators

def reflected (C : Config) : Config := ⟨fun i => swapP (C.plank i)⟩

theorem reflected_equiv (C : Config) : C.Equiv (reflected C) :=
  Relation.EqvGen.rel _ _ (Move.swap C (fun i => (swapP (C.plank i)).u_ne_zero))

theorem reflected_width (C : Config) (i : Fin 3) : (reflected C).relW i=C.relW i := by
  simp only [Config.relW,reflected,swapP,Plank.relWidth,Proofs.Transport.stdTriangle_width_eq]
  rw [max_comm (C.plank i).u.2 (C.plank i).u.1,min_comm (C.plank i).u.2 (C.plank i).u.1]

theorem not_mixed_permuted (C : Config)
    (hu : ∀ i, 0 < (C.plank i).u.1 ∧ 0 < (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C) (σ : Equiv.Perm (Fin 3))
    (h0 : (C.plank (σ 0)).u.2 < (C.plank (σ 0)).u.1)
    (h1 : (C.plank (σ 1)).u.2 < (C.plank (σ 1)).u.1)
    (h2 : (C.plank (σ 2)).u.1 < (C.plank (σ 2)).u.2) : False := by
  let D : Config := ⟨C.plank ∘ σ⟩
  have hE : C.Equiv D := Relation.EqvGen.rel _ _ (Move.relabel C σ)
  have hd : D.deficit=C.deficit := by simp only [Config.deficit,← hE.sumRelW_eq]
  exact TriangleMixedTransport.not_equality D ⟨(hu (σ 0)).2,h0⟩ ⟨(hu (σ 1)).2,h1⟩
    ⟨(hu (σ 2)).1,h2⟩ (fun i => hw (σ i)) (hd.symm ▸ hδ)
    ((equality_iff_of_equiv hE).mp he)

/-- Complete direction exhaustion in the strict common-minimum sector:
equality forces all three directions to have the same maximum vertex. -/
theorem same_maximum (C : Config)
    (hu : ∀ i, 0 < (C.plank i).u.1 ∧ 0 < (C.plank i).u.2)
    (hne : ∀ i, (C.plank i).u.1 ≠ (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C) :
    (∀ i, (C.plank i).u.2 < (C.plank i).u.1) ∨
      (∀ i, (C.plank i).u.1 < (C.plank i).u.2) := by
  have hX := not_mixed_permuted C hu hw hδ he
  have hE := reflected_equiv C
  have hd : (reflected C).deficit=C.deficit := by simp only [Config.deficit,← hE.sumRelW_eq]
  have hY (σ : Equiv.Perm (Fin 3))
      (h0 : (C.plank (σ 0)).u.1 < (C.plank (σ 0)).u.2)
      (h1 : (C.plank (σ 1)).u.1 < (C.plank (σ 1)).u.2)
      (h2 : (C.plank (σ 2)).u.2 < (C.plank (σ 2)).u.1) : False :=
    not_mixed_permuted (reflected C) (fun i => ⟨(hu i).2,(hu i).1⟩)
      (fun i => (reflected_width C i).symm ▸ hw i) (hd.symm ▸ hδ)
      ((equality_iff_of_equiv hE).mp he) σ h0 h1 h2
  rcases lt_or_gt_of_ne (hne 0) with hy0 | hx0 <;>
    rcases lt_or_gt_of_ne (hne 1) with hy1 | hx1 <;>
    rcases lt_or_gt_of_ne (hne 2) with hy2 | hx2
  · exact Or.inr (Proofs.Symmetry.forall_fin_three hy0 hy1 hy2)
  · exact (hY (Equiv.refl _) hy0 hy1 hx2).elim
  · exact (hY (Equiv.swap 1 2)
      (by simpa [Equiv.swap_apply_def] using hy0)
      (by simpa [Equiv.swap_apply_def] using hy2)
      (by simpa [Equiv.swap_apply_def] using hx1)).elim
  · exact (hX (Equiv.swap 0 2)
      (by simpa [Equiv.swap_apply_def] using hx2)
      (by simpa [Equiv.swap_apply_def] using hx1)
      (by simpa [Equiv.swap_apply_def] using hy0)).elim
  · exact (hY (Equiv.swap 0 2)
      (by simpa [Equiv.swap_apply_def] using hy2)
      (by simpa [Equiv.swap_apply_def] using hy1)
      (by simpa [Equiv.swap_apply_def] using hx0)).elim
  · exact (hX (Equiv.swap 1 2)
      (by simpa [Equiv.swap_apply_def] using hx0)
      (by simpa [Equiv.swap_apply_def] using hx2)
      (by simpa [Equiv.swap_apply_def] using hy1)).elim
  · exact (hX (Equiv.refl _) hx0 hx1 hy2).elim
  · exact Or.inl (Proofs.Symmetry.forall_fin_three hx0 hx1 hx2)

theorem common_maximum_iff (C : Config)
    (hu : ∀ i, 0 < (C.plank i).u.2)
    (hmax : ∀ i, (C.plank i).u.2 < (C.plank i).u.1)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔ OrderedStack stdTriangle C.plank := by
  have hp : ∀ i, CommonExtremes stdTriangle (C.plank i) := by
    intro i
    simpa [CommonExtremes,stdTriangle,dot] using And.intro (hu i).le (hmax i).le
  have hR : 0 < ∑ i, (C.plank i).relWidth stdTriangle := by
    rw [Fin.sum_univ_three]
    exact add_pos (add_pos (hw 0) (hw 1)) (hw 2)
  have hR1 : (∑ i, (C.plank i).relWidth stdTriangle) < 1 := by
    change C.sumRelW < 1
    dsimp only [Config.deficit] at hδ
    linarith only [hδ]
  have he := CommonMiddleAffineTransport.equality_iff_orderedStack stdTriangle C.plank hp hw hR hR1
  rw [Proofs.Quant.volume_stdTriangle] at he
  norm_num only [ENNReal.toReal_ofReal] at he
  unfold TriangleEqualityReductions.Equality
  rw [max_eq_right hδ.le]
  simpa only [Config.deficit,Config.sumRelW,Config.relW,Config.gapArea,Config.uncovered] using he

/-- The complete family list in this sector has one geometric type: an
ordered stack with common minimum and maximum vertices. The two alternatives
record which of the other two vertices is the maximum; reflection preserves
the whole configuration's area and each original relative width. -/
theorem equality_iff_stacks (C : Config)
    (hu : ∀ i, 0 < (C.plank i).u.1 ∧ 0 < (C.plank i).u.2)
    (hne : ∀ i, (C.plank i).u.1 ≠ (C.plank i).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔
      ((∀ i, (C.plank i).u.2 < (C.plank i).u.1) ∧ OrderedStack stdTriangle C.plank) ∨
      ((∀ i, (C.plank i).u.1 < (C.plank i).u.2) ∧ OrderedStack stdTriangle (reflected C).plank) := by
  have hE := reflected_equiv C
  have hd : (reflected C).deficit=C.deficit := by simp only [Config.deficit,← hE.sumRelW_eq]
  have hwe : ∀ i, 0 < (reflected C).relW i := fun i => (reflected_width C i).symm ▸ hw i
  have hright (hmax : ∀ i, (C.plank i).u.1 < (C.plank i).u.2) :
      TriangleEqualityReductions.Equality C ↔ OrderedStack stdTriangle (reflected C).plank :=
    (equality_iff_of_equiv hE).trans
      (common_maximum_iff (reflected C) (fun i => (hu i).1) hmax hwe (hd.symm ▸ hδ))
  constructor
  · intro he
    rcases same_maximum C hu hne hw hδ he with hmax | hmax
    · exact Or.inl ⟨hmax,(common_maximum_iff C (fun i => (hu i).2) hmax hw hδ).mp he⟩
    · exact Or.inr ⟨hmax,(hright hmax).mp he⟩
  · rintro (⟨hmax,hs⟩ | ⟨hmax,hs⟩)
    · exact (common_maximum_iff C (fun i => (hu i).2) hmax hw hδ).mpr hs
    · exact (hright hmax).mpr hs

/-- The same filled triangle with the two nonminimum vertices interchanged. -/
def swappedTriangle (T : Triangle) : Triangle :=
  ⟨T.A,T.C,T.B,by simpa only [Set.pair_comm T.C T.B] using T.not_collinear⟩

theorem swappedTriangle_set (T : Triangle) : (swappedTriangle T).set=T.set := by
  ext z
  change (∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+b+c=1 ∧
    z=a • T.A+b • T.C+c • T.B) ↔
    (∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+b+c=1 ∧
    z=a • T.A+b • T.B+c • T.C)
  constructor <;> rintro ⟨a,b,c,ha,hb,hc,hs,hz⟩ <;>
    refine ⟨a,c,b,ha,hc,hb,by linarith only [hs],?_⟩ <;> rw [hz] <;> abel

theorem swappedTriangle_width (T : Triangle) (p : Plank) :
    p.relWidth (swappedTriangle T)=p.relWidth T := by
  simp only [Plank.relWidth,Triangle.width,swappedTriangle]
  rw [max_comm (dot p.u T.C) (dot p.u T.B),min_comm (dot p.u T.C) (dot p.u T.B)]

open Proofs.Basic Proofs.Transport in
/-- Exhaustion stated directly for the original forms on an arbitrary triangle. -/
theorem triangle_same_maximum (T : Triangle) (p : Fin 3 → Plank)
    (hmin : ∀ i, dot (p i).u T.A < dot (p i).u T.B ∧
      dot (p i).u T.A < dot (p i).u T.C)
    (hne : ∀ i, dot (p i).u T.B ≠ dot (p i).u T.C)
    (hw : ∀ i, 0 < (p i).relWidth T) (hR : (∑ i, (p i).relWidth T) < 1)
    (he : (volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) :
    (∀ i, dot (p i).u T.C < dot (p i).u T.B) ∨
      (∀ i, dot (p i).u T.B < dot (p i).u T.C) := by
  let C := AffineTransport.pullbackConfig T p
  have hu : ∀ i, 0 < (C.plank i).u.1 ∧ 0 < (C.plank i).u.2 := by
    intro i
    simpa only [C,AffineTransport.pullbackConfig,pullbackPlank,dot_sub_right,
      sub_pos] using hmin i
  have hnu : ∀ i, (C.plank i).u.1 ≠ (C.plank i).u.2 := by
    intro i
    simpa only [C,AffineTransport.pullbackConfig,pullbackPlank,dot_sub_right,
      ne_eq,sub_left_inj] using hne i
  have hcw (i) : C.relW i=(p i).relWidth T := relWidth_pullback T (p i)
  have hδ : 0 < C.deficit := by
    rw [AffineTransport.deficit_pullbackConfig]
    exact sub_pos.mpr hR
  have hEq : TriangleEqualityReductions.Equality C := by
    rw [TriangleEqualityReductions.Equality,max_eq_right hδ.le,
      AffineTransport.deficit_pullbackConfig]
    apply mul_left_cancel₀ (abs_ne_zero.mpr (det3_ne_zero T))
    rw [AffineTransport.gapArea_transport,AffineTransport.area_triangle] at he
    change |det3 T.A T.B T.C| * C.gapArea =
      (1-∑ i, (p i).relWidth T)^2*(|det3 T.A T.B T.C| * (1/2)) at he
    rw [he]
    ring
  simpa only [C,AffineTransport.pullbackConfig,pullbackPlank,dot_sub_right,
    sub_lt_sub_iff_right] using same_maximum C hu hnu (fun i => by rw [hcw]; exact hw i) hδ hEq

/-- Complete geometric catalogue for three positive, strictly oblique
directions sharing a strict minimum vertex, on any nondegenerate triangle.
The original whole planks form an ordered stack, with either B or C as
their common maximum. No normal magnitude or band-position assumption is used. -/
theorem triangle_equality_iff_stacks (T : Triangle) (p : Fin 3 → Plank)
    (hmin : ∀ i, dot (p i).u T.A < dot (p i).u T.B ∧
      dot (p i).u T.A < dot (p i).u T.C)
    (hne : ∀ i, dot (p i).u T.B ≠ dot (p i).u T.C)
    (hw : ∀ i, 0 < (p i).relWidth T) (hR : (∑ i, (p i).relWidth T) < 1) :
    ((volume (T.set \ ⋃ i, (p i).set)).toReal =
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) ↔
      ((∀ i, dot (p i).u T.C < dot (p i).u T.B) ∧ OrderedStack T p) ∨
      ((∀ i, dot (p i).u T.B < dot (p i).u T.C) ∧ OrderedStack (swappedTriangle T) p) := by
  have hRpos : 0 < ∑ i, (p i).relWidth T := by
    rw [Fin.sum_univ_three]
    exact add_pos (add_pos (hw 0) (hw 1)) (hw 2)
  have hleft (hmax : ∀ i, dot (p i).u T.C < dot (p i).u T.B) :=
    CommonMiddleAffineTransport.equality_iff_orderedStack T p
      (fun i => ⟨(hmin i).2.le,(hmax i).le⟩) hw hRpos hR
  have hright (hmax : ∀ i, dot (p i).u T.B < dot (p i).u T.C) :
      ((volume (T.set \ ⋃ i, (p i).set)).toReal =
        (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal) ↔
        OrderedStack (swappedTriangle T) p := by
    have hr := CommonMiddleAffineTransport.equality_iff_orderedStack (swappedTriangle T) p
      (fun i => ⟨(hmin i).1.le,(hmax i).le⟩)
      (fun i => by rw [swappedTriangle_width]; exact hw i)
      (by simpa only [swappedTriangle_width] using hRpos)
      (by simpa only [swappedTriangle_width] using hR)
    simpa only [swappedTriangle_set,swappedTriangle_width] using hr
  constructor
  · intro he
    rcases triangle_same_maximum T p hmin hne hw hR he with hmax | hmax
    · exact Or.inl ⟨hmax,(hleft hmax).mp he⟩
    · exact Or.inr ⟨hmax,(hright hmax).mp he⟩
  · rintro (⟨hmax,hs⟩ | ⟨hmax,hs⟩)
    · exact (hleft hmax).mpr hs
    · exact (hright hmax).mpr hs

end Quant.TriangleStrictCommonMinimum

/-- info: 'Quant.TriangleStrictCommonMinimum.equality_iff_stacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleStrictCommonMinimum.equality_iff_stacks

/-- info: 'Quant.TriangleStrictCommonMinimum.triangle_equality_iff_stacks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleStrictCommonMinimum.triangle_equality_iff_stacks
