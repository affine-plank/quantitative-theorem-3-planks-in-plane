/- Corner uniqueness forces individual calibration of a strict cyclic band. -/
module
public import Plank.Proofs.Quant.TriangleCyclicCornerLimits

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicVertexCalibration
open Set CommonVertex OrdinalArea CyclicArea CyclicTranslationEquality
open TriangleEqualityReductions TriangleCyclicEdgeSeeds TriangleCyclicCornerAssignments
open TriangleCyclicCornerLimits

theorem ac_calibration (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    (C.plank 1).lo=a*(1-widths C 1) ∧
      (C.plank 1).hi=a+(1-a)*widths C 1 := by
  classical
  let x := threshold C (C.deficit,0) 0
  let y := threshold C (C.deficit,0) 1
  let w := threshold C (C.deficit,0) 2
  have hr : ∀ i, 0 < widths C i := by
    intro i
    simpa only [Config.relW,Plank.relWidth,
      BalancedArea.abc_width_one C hb ha hc hu0 hu1 hu2,div_one,widths] using hp i
  have hd := CyclicArea.deficit_eq C hb ha hc hu0 hu1 hu2
  have hAB : ( (1-b)*widths C 2 ≤ x ∧ -((1-a)*widths C 2) ≤ y ∧ w < 0) ∨
      (x < (1-b)*widths C 2 ∧ a*widths C 0-(1-a)*widths C 2 ≤ y ∧ w < c*widths C 0) := by
    apply ab_limit ha hc.1
    intro ε hε
    obtain ⟨t,_,hte,htd,s,hs,hsedge⟩ := edge_seed_near_end C hb ha hc hu0 hu1 hu2 hδ he 0 ε hε
    have h := ab_patterns C b a c t hu0 hu1 hu2 hr s hs hsedge
    have ht0 : threshold C (seed C.deficit 0 t) 0=x+(C.deficit-t) := by
      dsimp only [x,threshold,base]
      rw [hu0]
      dsimp [dot,seed]
      ring
    have ht1 : threshold C (seed C.deficit 0 t) 1=y+a*(C.deficit-t) := by
      dsimp only [y,threshold,base]
      rw [hu1]
      dsimp [dot,seed]
      ring
    have ht2 : threshold C (seed C.deficit 0 t) 2=w+c*(C.deficit-t) := by
      dsimp only [w,threshold,base]
      rw [hu2]
      dsimp [dot,seed]
      ring
    refine ⟨C.deficit-t,sub_pos.mpr htd,by linarith only [hte],?_⟩
    simpa only [ht0,ht1,ht2] using h
  have hBC : (x < b*widths C 1 ∧ y ≤ a*widths C 0 ∧
      c*widths C 0-(1-c)*widths C 1 ≤ w) ∨
      (x < b*widths C 1+(1-b)*widths C 2 ∧ y ≤ a*widths C 0-(1-a)*widths C 2 ∧
        w < c*widths C 0-(1-c)*widths C 1) := by
    apply bc_limit ha hb.2
    intro ε hε
    obtain ⟨t,_,hte,htd,s,hs,hsedge⟩ := edge_seed_near_end C hb ha hc hu0 hu1 hu2 hδ he 2 ε hε
    have h := bc_patterns C b a c t hu0 hu1 hu2 hr hd s hs hsedge
    have ht0 : threshold C (seed C.deficit 2 t) 0=x+(1-b)*(C.deficit-t) := by
      dsimp only [x,threshold,base]
      rw [hu0]
      dsimp [dot,seed]
      ring
    have ht1 : threshold C (seed C.deficit 2 t) 1=y-(1-a)*(C.deficit-t) := by
      dsimp only [y,threshold,base]
      rw [hu1]
      dsimp [dot,seed]
      ring
    have ht2 : threshold C (seed C.deficit 2 t) 2=w+(C.deficit-t) := by
      dsimp only [w,threshold,base]
      rw [hu2]
      dsimp [dot,seed]
      ring
    refine ⟨C.deficit-t,sub_pos.mpr htd,by linarith only [hte],?_⟩
    simpa only [ht0,ht1,ht2] using h
  have h001 (z : ℝ × ℝ) (h : (1-b)*widths C 2 < threshold C z 0 ∧
      -((1-a)*widths C 2) < threshold C z 1 ∧ threshold C z 2 < 0) :
      z+translations C {2} ∈ exteriorCells C {2} := by
    apply (assignment_iff C b a c hu0 hu1 hu2 z {2}).mpr
    intro i
    fin_cases i
    · simpa [offset] using h.1
    · simpa [offset] using h.2.1
    · simpa [offset] using h.2.2
  have h101 (z : ℝ × ℝ) (h : threshold C z 0 < (1-b)*widths C 2 ∧
      a*widths C 0-(1-a)*widths C 2 < threshold C z 1 ∧ threshold C z 2 < c*widths C 0) :
      z+translations C {0,2} ∈ exteriorCells C {0,2} := by
    apply (assignment_iff C b a c hu0 hu1 hu2 z {0,2}).mpr
    intro i
    fin_cases i
    · simpa [offset] using h.1
    · simpa [offset] using h.2.1
    · simpa [offset] using h.2.2
  have h110 (z : ℝ × ℝ) (h : threshold C z 0 < b*widths C 1 ∧
      threshold C z 1 < a*widths C 0 ∧ c*widths C 0-(1-c)*widths C 1 < threshold C z 2) :
      z+translations C {0,1} ∈ exteriorCells C {0,1} := by
    apply (assignment_iff C b a c hu0 hu1 hu2 z {0,1}).mpr
    intro i
    fin_cases i
    · simpa [offset] using h.1
    · simpa [offset] using h.2.1
    · simpa [offset] using h.2.2
  have h111 (z : ℝ × ℝ) (h : threshold C z 0 < b*widths C 1+(1-b)*widths C 2 ∧
      threshold C z 1 < a*widths C 0-(1-a)*widths C 2 ∧
      threshold C z 2 < c*widths C 0-(1-c)*widths C 1) :
      z+translations C {0,1,2} ∈ exteriorCells C {0,1,2} := by
    apply (assignment_iff C b a c hu0 hu1 hu2 z {0,1,2}).mpr
    intro i
    fin_cases i
    · simpa [offset] using h.1
    · simpa [offset] using h.2.1
    · simpa [offset] using h.2.2
  have hy : y=a*widths C 0-(1-a)*widths C 2 := by
    apply corner_middle ha hb hc hδ (mul_pos ha.1 (hr 0))
      (mul_pos (sub_pos.mpr ha.2) (hr 2)) hAB hBC
    intro e k he0 hed hk0 hk1
    dsimp only
    intro hdup
    let z : ℝ × ℝ := (C.deficit-e,k*e)
    have hz : 0 < z.1 ∧ 0 < z.2 ∧ z.1+z.2 < C.deficit :=
      ⟨sub_pos.mpr hed,mul_pos hk0 he0,by
        dsimp [z]
        nlinarith only [mul_pos (sub_pos.mpr hk1) he0]⟩
    have ht0 : threshold C z 0=x+(1-b*k)*e := by
      dsimp only [z,x,threshold,base]
      rw [hu0]
      dsimp [dot]
      ring
    have ht1 : threshold C z 1=y+(a-k)*e := by
      dsimp only [z,y,threshold,base]
      rw [hu1]
      dsimp [dot]
      ring
    have ht2 : threshold C z 2=w+(c+(1-c)*k)*e := by
      dsimp only [z,w,threshold,base]
      rw [hu2]
      dsimp [dot]
      ring
    rw [← ht0,← ht1,← ht2] at hdup
    rcases hdup with ⟨hA,hC⟩ | ⟨hA,hD⟩ | ⟨hB,hC⟩
    · have hq := unique_at_interior C hb ha hc hu0 hu1 hu2 hδ he hz
        {2} {0,1} (h001 z hA) (h110 z hC)
      exact (by decide : ({2} : Finset (Fin 3)) ≠ {0,1}) hq
    · have hq := unique_at_interior C hb ha hc hu0 hu1 hu2 hδ he hz
        {2} {0,1,2} (h001 z hA) (h111 z hD)
      exact (by decide : ({2} : Finset (Fin 3)) ≠ {0,1,2}) hq
    · have hq := unique_at_interior C hb ha hc hu0 hu1 hu2 hδ he hz
        {0,2} {0,1} (h101 z hB) (h110 z hC)
      exact (by decide : ({0,2} : Finset (Fin 3)) ≠ {0,1}) hq
  have hlo : (C.plank 1).lo=a*(1-widths C 1) := by
    calc
      _ = a*(C.deficit+widths C 0+widths C 2) := by
        dsimp only [y,threshold,base] at hy
        rw [hu1] at hy
        dsimp [dot] at hy
        linarith only [hy]
      _ = _ := by rw [hd]; ring
  refine ⟨hlo,?_⟩
  have hw : (C.plank 1).hi=(C.plank 1).lo+widths C 1 := by dsimp [widths]; ring
  rw [hw,hlo]
  ring

end Quant.TriangleCyclicVertexCalibration

/-- info: 'Quant.TriangleCyclicVertexCalibration.ac_calibration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicVertexCalibration.ac_calibration
