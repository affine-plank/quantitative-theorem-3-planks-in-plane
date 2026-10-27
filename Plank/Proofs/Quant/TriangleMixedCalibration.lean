/- Equality calibrates the isolated maximizing direction in a mixed chart. -/
module
public import Plank.Proofs.Quant.TriangleFarEdge
public import Plank.Proofs.Quant.CommonMiddleEdgeFamily

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedCalibration
open Set MeasureTheory CommonVertex CommonVertexTranslationEquality TriangleFarEdge
open CommonMiddleAffineTransport CommonMiddleNullWindow
open scoped BigOperators

/-- Two normals maximize at X and the third at Y, with the same minimum O.
At equality the isolated Y direction has its single-plank tent position.
The coefficient a may vanish; then its band is forced onto the edge OX. -/
theorem isolated_calibration (C : Config) (a b c : ℝ)
    (ha : 0 ≤ a ∧ a < 1) (hb : 0 ≤ b ∧ b < 1) (hc : 0 ≤ c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(1,c))
    (hu2 : (C.plank 2).u=(a,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C) :
    (C.plank 2).lo = a*(1-C.relW 2) ∧
      (C.plank 2).hi = a*(1-C.relW 2)+C.relW 2 := by
  have hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2 := by
    intro i
    fin_cases i
    · change 0 ≤ (C.plank 0).u.1 ∧ 0 ≤ (C.plank 0).u.2
      rw [hu0]; exact ⟨zero_le_one,hb.1⟩
    · change 0 ≤ (C.plank 1).u.1 ∧ 0 ≤ (C.plank 1).u.2
      rw [hu1]; exact ⟨zero_le_one,hc.1⟩
    · change 0 ≤ (C.plank 2).u.1 ∧ 0 ≤ (C.plank 2).u.2
      rw [hu2]; exact ⟨ha.1,zero_le_one⟩
  have hne : ∀ i, (C.plank i).u.1 ≠ (C.plank i).u.2 := by
    intro i
    fin_cases i
    · change (C.plank 0).u.1 ≠ (C.plank 0).u.2
      rw [hu0]; exact ne_of_gt hb.2
    · change (C.plank 1).u.1 ≠ (C.plank 1).u.2
      rw [hu1]; exact ne_of_gt hc.2
    · change (C.plank 2).u.1 ≠ (C.plank 2).u.2
      rw [hu2]; exact ne_of_lt ha.2
  have hs0 : steps C 0=(C.relW 0,0) := by simp [steps,hu0,not_le.mpr hb.2]
  have hs1 : steps C 1=(C.relW 1,0) := by simp [steps,hu1,not_le.mpr hc.2]
  have hs2 : steps C 2=(0,C.relW 2) := by simp [steps,hu2,ha.2.le]
  have hshift : shift (steps C) Finset.univ = (C.relW 0+C.relW 1,C.relW 2) := by
    simp only [shift,Fin.sum_univ_three,hs0,hs1,hs2,Prod.mk_add_mk,add_zero,zero_add]
  obtain ⟨i,hi,hcontact⟩ := vertical_upper_contact C hu hne hw hδ he
    (by simpa only [hshift] using hw 2)
  have hcontact2 : (C.plank 2).hi =
      dot (C.plank 2).u ((C.deficit,0)+shift (steps C) Finset.univ) := by
    fin_cases i
    · change (C.plank 0).u.1 < (C.plank 0).u.2 at hi
      rw [hu0] at hi
      exact (not_lt_of_ge hb.2.le hi).elim
    · change (C.plank 1).u.1 < (C.plank 1).u.2 at hi
      rw [hu1] at hi
      exact (not_lt_of_ge hc.2.le hi).elim
    · exact hcontact
  have hwidth : C.relW 2=(C.plank 2).hi-(C.plank 2).lo := by
    rw [Config.relW,Plank.relWidth,hu2,width_tent ha.1 ha.2.le,div_one]
  rw [hu2,hshift] at hcontact2
  simp only [dot,Prod.fst_add,Prod.snd_add,zero_add,one_mul,
    Config.deficit,Config.sumRelW,Fin.sum_univ_three] at hcontact2
  constructor <;> nlinarith only [hwidth,hcontact2]

/-- Complete placement classification when the isolated maximizing direction
is an edge normal. The third band is initially arbitrary; equality forces
it onto that edge and forces the other two bands to be an ordered pair. -/
theorem edge_equality_iff (C : Config) (b c : ℝ)
    (hb : 0 ≤ b ∧ b < 1) (hc : 0 ≤ c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(1,c))
    (hu2 : (C.plank 2).u=(0,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    TriangleEqualityReductions.Equality C ↔
      (C.plank 2).lo=0 ∧ PairOrderedStack stdTriangle (C.plank 0) (C.plank 1) := by
  have hanchored (hl : (C.plank 2).lo=0) : TriangleEqualityReductions.Equality C ↔
      PairOrderedStack stdTriangle (C.plank 0) (C.plank 1) := by
    let p : Fin 2 → Plank := ![C.plank 0,C.plank 1]
    let F := (LinearMap.snd ℝ ℝ ℝ).toAffineMap
    have hp : ∀ i, CommonExtremes stdTriangle (p i) := by
      intro i
      fin_cases i
      · change dot (C.plank 0).u (0,0) ≤ dot (C.plank 0).u (0,1) ∧
          dot (C.plank 0).u (0,1) ≤ dot (C.plank 0).u (1,0)
        simpa [hu0,dot] using And.intro hb.1 hb.2.le
      · change dot (C.plank 1).u (0,0) ≤ dot (C.plank 1).u (0,1) ∧
          dot (C.plank 1).u (0,1) ≤ dot (C.plank 1).u (1,0)
        simpa [hu1,dot] using And.intro hc.1 hc.2.le
    have hwidth : C.relW 2=(C.plank 2).hi-(C.plank 2).lo := by
      rw [Config.relW,Plank.relWidth,hu2,width_tent le_rfl zero_le_one,div_one]
    have hh : (C.plank 2).hi=C.relW 2 := by linarith only [hwidth,hl]
    have hband : (C.plank 2).set={z | 0 ≤ F z ∧ F z ≤ C.relW 2} := by
      ext z
      change ((C.plank 2).lo ≤ dot (C.plank 2).u z ∧
        dot (C.plank 2).u z ≤ (C.plank 2).hi) ↔ (0 ≤ z.2 ∧ z.2 ≤ C.relW 2)
      simp only [hl,hh,hu2,dot,zero_mul,one_mul,zero_add]
    have hgap : stdTriangle.set \ ({z | 0 ≤ F z ∧ F z ≤ C.relW 2} ∪ ⋃ i, (p i).set) =
        C.uncovered := by
      change stdTriangle.set \ _ = stdTriangle.set \ _
      congr 1
      rw [← hband,CommonMiddleSupportReduction.union_two]
      ext z
      simp only [mem_union,mem_iUnion,p,
        Matrix.cons_val_zero,Matrix.cons_val_one]
      constructor
      · rintro (hz | hz | hz)
        exacts [⟨2,hz⟩,⟨0,hz⟩,⟨1,hz⟩]
      · rintro ⟨i,hi⟩
        fin_cases i
        · exact Or.inr (Or.inl hi)
        · exact Or.inr (Or.inr hi)
        · exact Or.inl hi
    have hsum : 1-C.relW 2-((p 0).relWidth stdTriangle+(p 1).relWidth stdTriangle) =
        C.deficit := by
      change 1-C.relW 2-(C.relW 0+C.relW 1)=C.deficit
      rw [Config.deficit,Config.sumRelW,Fin.sum_univ_three]
      ring
    have htR : C.relW 2+((p 0).relWidth stdTriangle+(p 1).relWidth stdTriangle) < 1 := by
      linarith only [hsum,hδ]
    have heq := CommonMiddleEdgeFamily.equality_iff_pairStack stdTriangle
      Proofs.GapCells.isCompact_stdTriangle F rfl rfl rfl p hp
      (fun i => by fin_cases i; exact hw 0; exact hw 1) (C.relW 2) (hw 2).le htR
    rw [hgap,hsum,Proofs.Quant.volume_stdTriangle] at heq
    norm_num only [ENNReal.toReal_ofReal] at heq
    change (C.gapArea=C.deficit^2*(1/2)) ↔ PairOrderedStack stdTriangle (C.plank 0) (C.plank 1) at heq
    simpa only [TriangleEqualityReductions.Equality,max_eq_right hδ.le] using heq
  constructor
  · intro he
    have hl := (isolated_calibration C 0 b c ⟨le_rfl,zero_lt_one⟩ hb hc hu0 hu1 hu2 hw hδ he).1
    simp only [zero_mul] at hl
    exact ⟨hl,(hanchored hl).mp he⟩
  · rintro ⟨hl,hs⟩
    exact (hanchored hl).mpr hs

end Quant.TriangleMixedCalibration

/-- info: 'Quant.TriangleMixedCalibration.isolated_calibration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedCalibration.isolated_calibration
/-- info: 'Quant.TriangleMixedCalibration.edge_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedCalibration.edge_equality_iff
