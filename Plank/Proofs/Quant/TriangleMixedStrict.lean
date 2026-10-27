/- Strictly oblique directions with a common minimum and mixed maxima
cannot attain the triangle area bound. -/
module
public import Plank.Proofs.Quant.TriangleMixedCorner

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedStrict
open Set CommonVertex CommonVertexTranslationEquality TriangleSourceBoundary
open TriangleFarEdge TriangleMixedCalibration TriangleMixedCorner
open scoped BigOperators

/-- Three positive-width planks whose normalized normals have one common
minimum vertex and two different unique maximum vertices are never tight
when all three normals are strictly oblique. No endpoint or clipping
conditions are assumed. -/
theorem not_equality (C : Config) (a b c : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(1,c))
    (hu2 : (C.plank 2).u=(a,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    ¬ TriangleEqualityReductions.Equality C := by
  intro he
  have hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2 := by
    apply Proofs.Symmetry.forall_fin_three
    · simpa only [hu0] using And.intro (show (0 : ℝ) ≤ 1 by norm_num) hb.1.le
    · simpa only [hu1] using And.intro (show (0 : ℝ) ≤ 1 by norm_num) hc.1.le
    · simpa only [hu2] using And.intro ha.1.le (show (0 : ℝ) ≤ 1 by norm_num)
  have hne : ∀ i, (C.plank i).u.1 ≠ (C.plank i).u.2 := by
    apply Proofs.Symmetry.forall_fin_three
    · simpa only [hu0] using ne_of_gt hb.2
    · simpa only [hu1] using ne_of_gt hc.2
    · simpa only [hu2] using ne_of_lt ha.2
  have hs0 : steps C 0=(C.relW 0,0) := by simp [steps,hu0,not_le.mpr hb.2]
  have hs1 : steps C 1=(C.relW 1,0) := by simp [steps,hu1,not_le.mpr hc.2]
  have hs2 : steps C 2=(0,C.relW 2) := by simp [steps,hu2,ha.2.le]
  have hall : shift (steps C) Finset.univ=(C.relW 0+C.relW 1,C.relW 2) := by
    simp only [shift,Fin.sum_univ_three,hs0,hs1,hs2,Prod.mk_add_mk,add_zero,zero_add]
  have hsum : C.deficit+C.relW 0+C.relW 1=1-C.relW 2 := by
    rw [Config.deficit,Config.sumRelW,Fin.sum_univ_three]
    ring
  have hcal := (isolated_calibration C a b c ⟨ha.1.le,ha.2⟩
    ⟨hb.1.le,hb.2⟩ ⟨hc.1.le,hc.2⟩ hu0 hu1 hu2 hw hδ he).2
  let q0 := (C.plank 0).hi-C.relW 0-C.relW 1-b*C.relW 2
  let q1 := (C.plank 1).hi-C.relW 0-C.relW 1-c*C.relW 2
  have hq0 : q0 ≤ b*C.deficit := by
    have hh := far_upper C hu hne hw hδ he 0 ⟨le_rfl,hδ.le⟩ 0
    simp only [hu0,hall,dot,Prod.fst_add,Prod.snd_add,one_mul,sub_zero,zero_add] at hh
    dsimp only [q0]
    nlinarith only [hh]
  have hq1 : q1 ≤ c*C.deficit := by
    have hh := far_upper C hu hne hw hδ he 0 ⟨le_rfl,hδ.le⟩ 1
    simp only [hu1,hall,dot,Prod.fst_add,Prod.snd_add,one_mul,sub_zero,zero_add] at hh
    dsimp only [q1]
    nlinarith only [hh]
  have hab : 0 < 1-a*b := by nlinarith only [ha.1,ha.2,hb.1,hb.2]
  have hac : 0 < 1-a*c := by nlinarith only [ha.1,ha.2,hc.1,hc.2]
  let t0 := (q0-a*b*C.deficit)/(1-a*b)
  let t1 := (q1-a*c*C.deficit)/(1-a*c)
  have ht0eq : t0*(1-a*b)=q0-a*b*C.deficit := div_mul_cancel₀ _ (ne_of_gt hab)
  have ht1eq : t1*(1-a*c)=q1-a*c*C.deficit := div_mul_cancel₀ _ (ne_of_gt hac)
  have ht0 : t0 < C.deficit := by
    apply (div_lt_iff₀ hab).mpr
    nlinarith only [hq0,mul_pos (sub_pos.mpr hb.2) hδ]
  have ht1 : t1 < C.deficit := by
    apply (div_lt_iff₀ hac).mpr
    nlinarith only [hq1,mul_pos (sub_pos.mpr hc.2) hδ]
  let x := max t0 t1
  have hxδ : x < C.deficit := max_lt ht0 ht1
  have hxpos : 0 < x := by
    by_contra hn
    have hx : x ≤ 0 := not_lt.mp hn
    have h0nonpos : t0 ≤ 0 := (le_max_left _ _).trans hx
    have h1nonpos : t1 ≤ 0 := (le_max_right _ _).trans hx
    have hq0low : q0 ≤ a*b*C.deficit := by nlinarith only [h0nonpos,ht0eq,hab]
    have hq1low : q1 ≤ a*c*C.deficit := by nlinarith only [h1nonpos,ht1eq,hac]
    let y := (1+a)*C.deficit/2
    have hy : 0 < y := div_pos (mul_pos (by linarith only [ha.1]) hδ) (by norm_num)
    have hyδ : y < C.deficit := by dsimp only [y]; nlinarith only [ha.2,hδ]
    have hya : a*C.deficit < y := by dsimp only [y]; nlinarith only [ha.2,hδ]
    have hs : (0,y)+shift (steps C) Finset.univ ∈ exteriorCells C Finset.univ := by
      rw [exteriorCells,Plank.LinearBands.strictCell]
      apply Proofs.Symmetry.forall_fin_three
      · simp only [Finset.mem_univ,if_true,hall,hu0,dot,Prod.fst_add,Prod.snd_add,one_mul,zero_add]
        dsimp only [q0] at hq0low
        nlinarith only [hq0low,mul_pos hb.1 (sub_pos.mpr hya)]
      · simp only [Finset.mem_univ,if_true,hall,hu1,dot,Prod.fst_add,Prod.snd_add,one_mul,zero_add]
        dsimp only [q1] at hq1low
        nlinarith only [hq1low,mul_pos hc.1 (sub_pos.mpr hya)]
      · simp only [Finset.mem_univ,if_true,hall,hu2,dot,Prod.fst_add,Prod.snd_add,one_mul,zero_add]
        rw [← hsum] at hcal
        nlinarith only [hcal,hya]
    have hz : (0,y) ∈ RowDeletion.triangle C.deficit := ⟨le_rfl,hy.le,by simpa using hyδ.le⟩
    have hh := (source_faces C hu hδ he Finset.univ hz hs).1 rfl
    rw [hall] at hh
    have hw0 := hw 0
    have hw1 := hw 1
    change C.relW 0+C.relW 1=0 at hh
    linarith only [hh,hw0,hw1]
  let y := a*(C.deficit-x)
  have hy : 0 < y := mul_pos ha.1 (sub_pos.mpr hxδ)
  have hxy : x+y < C.deficit := by
    dsimp only [y]
    nlinarith only [mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hxδ)]
  have h0weak : (C.plank 0).hi ≤ x+C.relW 0+C.relW 1+b*(y+C.relW 2) := by
    have hle : t0 ≤ x := le_max_left _ _
    dsimp only [q0] at ht0eq
    dsimp only [y]
    nlinarith only [ht0eq,mul_nonneg (sub_nonneg.mpr hle) hab.le]
  have h1weak : (C.plank 1).hi ≤ x+C.relW 0+C.relW 1+c*(y+C.relW 2) := by
    have hle : t1 ≤ x := le_max_right _ _
    dsimp only [q1] at ht1eq
    dsimp only [y]
    nlinarith only [ht1eq,mul_nonneg (sub_nonneg.mpr hle) hac.le]
  have h2eq : (C.plank 2).hi=a*(x+C.relW 0+C.relW 1)+y+C.relW 2 := by
    rw [← hsum] at hcal
    dsimp only [y]
    nlinarith only [hcal]
  rcases le_total t1 t0 with horder | horder
  · have hxt : x=t0 := max_eq_left horder
    have h0eq : (C.plank 0).hi=x+C.relW 0+C.relW 1+b*(y+C.relW 2) := by
      dsimp only [q0] at ht0eq
      dsimp only [y]
      rw [hxt]
      nlinarith only [ht0eq]
    exact no_corner C a b c ha hb ⟨hc.1.le,hc.2⟩ hu0 hu1 hu2 hw hδ he
      x y hxpos.le hy.le hxy h0eq h1weak h2eq
  · have hxt : x=t1 := max_eq_right horder
    have h1eq : (C.plank 1).hi=x+C.relW 0+C.relW 1+c*(y+C.relW 2) := by
      dsimp only [q1] at ht1eq
      dsimp only [y]
      rw [hxt]
      nlinarith only [ht1eq]
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let D : Config := ⟨C.plank ∘ σ⟩
    have hD0 : D.plank 0=C.plank 1 := by simp [D,σ]
    have hD1 : D.plank 1=C.plank 0 := by simp [D,σ]
    have hD2 : D.plank 2=C.plank 2 := by simp [D,σ,Equiv.swap_apply_def]
    have hr0 : D.relW 0=C.relW 1 := congrArg (fun p => p.relWidth stdTriangle) hD0
    have hr1 : D.relW 1=C.relW 0 := congrArg (fun p => p.relWidth stdTriangle) hD1
    have hr2 : D.relW 2=C.relW 2 := congrArg (fun p => p.relWidth stdTriangle) hD2
    have hED : C.Equiv D := Relation.EqvGen.rel _ _ (Move.relabel C σ)
    have hdef : D.deficit=C.deficit := by simp only [Config.deficit,← hED.sumRelW_eq]
    have hwD : ∀ i, 0 < D.relW i := fun i => hw (σ i)
    apply no_corner D a c b ha hc ⟨hb.1.le,hb.2⟩
      (by rw [hD0,hu1]) (by rw [hD1,hu0]) (by rw [hD2,hu2]) hwD
      (hdef.symm ▸ hδ) ((equality_iff_of_equiv hED).mp he) x y hxpos.le hy.le
      (hdef.symm ▸ hxy)
    · rw [hD0,hr0,hr1,hr2]
      linarith only [h1eq]
    · rw [hD1,hr0,hr1,hr2]
      linarith only [h0weak]
    · rw [hD2,hr0,hr1,hr2]
      nlinarith only [h2eq]

end Quant.TriangleMixedStrict

/-- info: 'Quant.TriangleMixedStrict.not_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedStrict.not_equality
