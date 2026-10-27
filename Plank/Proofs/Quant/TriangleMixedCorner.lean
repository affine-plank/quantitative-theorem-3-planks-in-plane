/- A strictly coupled corner forces two overlapping source assignments. -/
module
public import Plank.Proofs.Quant.TriangleMixedCalibration

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedCorner
open Set CommonVertex CommonVertexTranslationEquality TriangleSourceBoundary
open scoped BigOperators

/-- An interior corner of the all-high source region between two mutually
coupled directions is incompatible with equality. The third direction may
be active at the same corner. -/
theorem no_corner (C : Config) (a b c : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 ≤ c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(1,c))
    (hu2 : (C.plank 2).u=(a,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit)
    (he : TriangleEqualityReductions.Equality C)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x+y < C.deficit)
    (h0 : (C.plank 0).hi=x+C.relW 0+C.relW 1+b*(y+C.relW 2))
    (h1 : (C.plank 1).hi≤x+C.relW 0+C.relW 1+c*(y+C.relW 2))
    (h2 : (C.plank 2).hi=a*(x+C.relW 0+C.relW 1)+y+C.relW 2) : False := by
  classical
  have hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2 := by
    apply Proofs.Symmetry.forall_fin_three
    · simpa only [hu0] using And.intro (show (0 : ℝ) ≤ 1 by norm_num) hb.1.le
    · simpa only [hu1] using And.intro (show (0 : ℝ) ≤ 1 by norm_num) hc.1
    · simpa only [hu2] using And.intro ha.1.le (show (0 : ℝ) ≤ 1 by norm_num)
  have hs0 : steps C 0=(C.relW 0,0) := by simp [steps,hu0,not_le.mpr hb.2]
  have hs1 : steps C 1=(C.relW 1,0) := by simp [steps,hu1,not_le.mpr hc.2]
  have hs2 : steps C 2=(0,C.relW 2) := by simp [steps,hu2,ha.2.le]
  have hall : shift (steps C) Finset.univ=(C.relW 0+C.relW 1,C.relW 2) := by
    simp only [shift,Fin.sum_univ_three,hs0,hs1,hs2,Prod.mk_add_mk,add_zero,zero_add]
  have hw0 := steps_self C hu 0
  have hw1 := steps_self C hu 1
  have hw2 := steps_self C hu 2
  simp only [hu0,hs0,dot,one_mul,mul_zero,add_zero] at hw0
  simp only [hu1,hs1,dot,one_mul,mul_zero,add_zero] at hw1
  simp only [hu2,hs2,dot,mul_zero,one_mul,zero_add] at hw2
  let m := min (C.deficit-x-y) (min (b*C.relW 2) (a*C.relW 0))
  have hm : 0 < m := lt_min (by linarith) (lt_min (mul_pos hb.1 (hw 2)) (mul_pos ha.1 (hw 0)))
  have hmδ : m ≤ C.deficit-x-y := min_le_left _ _
  have hmb : m ≤ b*C.relW 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hma : m ≤ a*C.relW 0 := (min_le_right _ _).trans (min_le_right _ _)
  have heps : ∃ ε : ℝ, 0 < ε ∧ ε < m/4 ∧
      x+ε+c*(y+ε) ≠ (C.plank 1).lo := by
    by_cases h : x+m/8+c*(y+m/8) ≠ (C.plank 1).lo
    · exact ⟨m/8,by linarith,by linarith,h⟩
    · refine ⟨m/12,by linarith,by linarith,?_⟩
      have heq := not_not.mp h
      intro heq'
      nlinarith only [heq,heq',hm,hc.1]
  obtain ⟨ε,hε,hεm,havoid⟩ := heps
  have hq : (x+ε,y+ε) ∈ RowDeletion.triangle C.deficit := by
    refine ⟨by linarith,by linarith,?_⟩
    change x+ε+(y+ε) ≤ C.deficit
    linarith only [hεm,hmδ,hm]
  have hlow0 : x+ε+C.relW 1+b*(y+ε) < (C.plank 0).lo := by
    nlinarith only [h0,hw0,hmb,hεm,hε,hb.2]
  have hlow2 : a*(x+ε+C.relW 1)+y+ε < (C.plank 2).lo := by
    nlinarith only [h2,hw2,hma,hεm,hε,ha.2]
  have hfull : (x+ε,y+ε)+shift (steps C) Finset.univ ∈
      exteriorCells C Finset.univ := by
    rw [exteriorCells,Plank.LinearBands.strictCell]
    apply Proofs.Symmetry.forall_fin_three
    · simp only [Finset.mem_univ,if_true,hall,hu0,dot,Prod.fst_add,Prod.snd_add,one_mul]
      nlinarith only [h0,hε,hb.1]
    · simp only [Finset.mem_univ,if_true,hall,hu1,dot,Prod.fst_add,Prod.snd_add,one_mul]
      nlinarith only [h1,hε,hc.1]
    · simp only [Finset.mem_univ,if_true,hall,hu2,dot,Prod.fst_add,Prod.snd_add,one_mul]
      nlinarith only [h2,hε,ha.1]
  rcases lt_or_gt_of_ne havoid with hbelow | habove
  · have hempty : (x+ε,y+ε)+shift (steps C) ∅ ∈ exteriorCells C ∅ := by
      rw [exteriorCells,Plank.LinearBands.strictCell]
      apply Proofs.Symmetry.forall_fin_three
      · simp only [Finset.notMem_empty,if_false,shift,Finset.sum_empty,add_zero,hu0,dot,one_mul]
        linarith only [hlow0,hw 1]
      · simpa only [Finset.notMem_empty,if_false,shift,Finset.sum_empty,add_zero,hu1,dot,one_mul]
          using hbelow
      · simp only [Finset.notMem_empty,if_false,shift,Finset.sum_empty,add_zero,hu2,dot,one_mul]
        nlinarith only [hlow2,ha.1,hw 1]
    have hh := source_unique C hu hδ he ∅ Finset.univ hq hempty hfull
    have hm0 : (0 : Fin 3) ∈ (∅ : Finset (Fin 3)) := hh.symm ▸ Finset.mem_univ 0
    simp at hm0
  · have hsingle : (x+ε,y+ε)+shift (steps C) {1} ∈ exteriorCells C {1} := by
      rw [exteriorCells,Plank.LinearBands.strictCell]
      apply Proofs.Symmetry.forall_fin_three
      · simpa only [Finset.mem_singleton,show (0 : Fin 3) ≠ 1 by decide,if_false,
          shift,Finset.sum_singleton,hs1,hu0,dot,Prod.fst_add,Prod.snd_add,add_zero,one_mul]
          using hlow0
      · simp only [Finset.mem_singleton,if_true,shift,Finset.sum_singleton,hs1,hu1,dot,
          Prod.fst_add,Prod.snd_add,add_zero,one_mul]
        linarith only [habove,hw1]
      · simpa only [Finset.mem_singleton,show (2 : Fin 3) ≠ 1 by decide,if_false,
          shift,Finset.sum_singleton,hs1,hu2,dot,Prod.fst_add,Prod.snd_add,add_zero,one_mul,add_assoc]
          using hlow2
    have hh := source_unique C hu hδ he {1} Finset.univ hq hsingle hfull
    have hm0 : (0 : Fin 3) ∈ ({1} : Finset (Fin 3)) := hh.symm ▸ Finset.mem_univ 0
    simp at hm0

end Quant.TriangleMixedCorner

/-- info: 'Quant.TriangleMixedCorner.no_corner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedCorner.no_corner
