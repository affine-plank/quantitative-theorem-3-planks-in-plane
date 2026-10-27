/- Strict source-edge switches follow from the unique surviving corner pairing. -/
module
public import Plank.Proofs.Quant.TriangleCyclicCalibrations

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicCornerSurvivors
open Set CommonVertex OrdinalArea CyclicArea CyclicTranslationEquality
open TriangleEqualityReductions TriangleCyclicEdgeSeeds TriangleCyclicCornerAssignments
open TriangleCyclicCornerLimits

private theorem corner_sides {a b c d p q r s t u x y w : ℝ}
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hd : 0 < d) (hr : 0 < r) (hs : 0 < s)
    (hAB : (q ≤ x ∧ -s ≤ y ∧ w < 0) ∨ (x < q ∧ r-s ≤ y ∧ w < t))
    (hBC : (x < p ∧ y ≤ r ∧ t-u ≤ w) ∨ (x < p+q ∧ y ≤ r-s ∧ w < t-u))
    (hno : ∀ e k : ℝ, 0 < e → e < d → 0 < k → k < 1 →
      let X := x+(1-b*k)*e
      let Y := y+(a-k)*e
      let W := w+(c+(1-c)*k)*e
      ¬ (((q < X ∧ -s < Y ∧ W < 0) ∧ (X < p ∧ Y < r ∧ t-u < W)) ∨
        ((q < X ∧ -s < Y ∧ W < 0) ∧ (X < p+q ∧ Y < r-s ∧ W < t-u)) ∨
        ((X < q ∧ r-s < Y ∧ W < t) ∧ (X < p ∧ Y < r ∧ t-u < W)))) :
    x<q ∧ w<t-u := by
  rcases hAB with hA | hB <;> rcases hBC with hC | hD
  · obtain ⟨e,k,he,hed,hk,hk1,hx,hy,hw⟩ := inward_box ha hb hc hd
      ⟨hA.1,hC.1⟩ ⟨hA.2.1,hC.2.1⟩ (by linarith only [hr,hs]) ⟨hC.2.2,hA.2.2⟩
    exact (hno e k he hed hk hk1 (Or.inl
      ⟨⟨hx.1,hy.1,hw.2⟩,⟨hx.2,hy.2,hw.1⟩⟩)).elim
  · obtain ⟨e,k,he,hed,hk,hk1,hx,hy,hw⟩ := inward_box ha hb hc hd
      ⟨hA.1,hD.1⟩ ⟨hA.2.1,hD.2.1⟩ (by linarith only [hr])
      (wl := w-1) ⟨by linarith,lt_min hA.2.2 hD.2.2⟩
    exact (hno e k he hed hk hk1 (Or.inr (Or.inl
      ⟨⟨hx.1,hy.1,hw.2.trans_le (min_le_left _ _)⟩,
        ⟨hx.2,hy.2,hw.2.trans_le (min_le_right _ _)⟩⟩))).elim
  · obtain ⟨e,k,he,hed,hk,hk1,hx,hy,hw⟩ := inward_box ha hb hc hd
      (xl := x-1) ⟨by linarith,lt_min hB.1 hC.1⟩
      ⟨hB.2.1,hC.2.1⟩ (by linarith only [hs]) ⟨hC.2.2,hB.2.2⟩
    exact (hno e k he hed hk hk1 (Or.inr (Or.inr
      ⟨⟨hx.2.trans_le (min_le_left _ _),hy.1,hw.2⟩,
        ⟨hx.2.trans_le (min_le_right _ _),hy.2,hw.1⟩⟩))).elim
  · exact ⟨hB.1,hD.2.2⟩


theorem upper_ab_switch (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    (C.plank 0).lo-widths C 2<C.deficit := by
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
  have hside : x<(1-b)*widths C 2 ∧ w<c*widths C 0-(1-c)*widths C 1 := by
    apply corner_sides ha hb hc hδ (mul_pos ha.1 (hr 0))
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
  have hx := hside.1
  dsimp only [x,threshold,base] at hx
  rw [hu0] at hx
  dsimp [dot] at hx
  linarith only [hx]

end Quant.TriangleCyclicCornerSurvivors

/-- info: 'Quant.TriangleCyclicCornerSurvivors.upper_ab_switch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicCornerSurvivors.upper_ab_switch
