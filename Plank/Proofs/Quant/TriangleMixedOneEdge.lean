/- Exhaustion of the mixed common-minimum sector with one horizontal edge normal. -/
module
public import Plank.Proofs.Quant.TriangleStrictCommonMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedOneEdge
open Set CommonVertex CommonVertexTranslationEquality TriangleSourceBoundary
open TriangleFarEdge TriangleMixedCalibration TriangleMixedCorner
open scoped BigOperators

/-- One horizontal edge normal cannot remove the strict loss caused by
two positive oblique bands with different maximum vertices. All three
band positions and positive actual widths are arbitrary. -/
theorem not_equality (C : Config) (a b : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(1,0))
    (hu2 : (C.plank 2).u=(a,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    ¬ TriangleEqualityReductions.Equality C := by
  intro he
  have hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2 := by
    apply Proofs.Symmetry.forall_fin_three
    · simpa only [hu0] using And.intro zero_le_one hb.1.le
    · simpa only [hu1] using And.intro (show (0 : ℝ) ≤ 1 by norm_num) (le_refl (0 : ℝ))
    · simpa only [hu2] using And.intro ha.1.le zero_le_one
  have hne : ∀ i, (C.plank i).u.1 ≠ (C.plank i).u.2 := by
    apply Proofs.Symmetry.forall_fin_three
    · simpa only [hu0] using ne_of_gt hb.2
    · simp only [hu1]; norm_num
    · simpa only [hu2] using ne_of_lt ha.2
  have hs0 : steps C 0=(C.relW 0,0) := by simp [steps,hu0,not_le.mpr hb.2]
  have hs1 : steps C 1=(C.relW 1,0) := by simp [steps,hu1]
  have hs2 : steps C 2=(0,C.relW 2) := by simp [steps,hu2,ha.2.le]
  have hall : shift (steps C) Finset.univ=(C.relW 0+C.relW 1,C.relW 2) := by
    simp only [shift,Fin.sum_univ_three,hs0,hs1,hs2,Prod.mk_add_mk,add_zero,zero_add]
  have hsum : C.deficit+C.relW 0+C.relW 1=1-C.relW 2 := by
    rw [Config.deficit,Config.sumRelW,Fin.sum_univ_three]
    ring
  have hw0 := steps_self C hu 0
  have hw1 := steps_self C hu 1
  simp only [hs0,hu0,dot,one_mul,mul_zero,add_zero] at hw0
  simp only [hs1,hu1,dot,one_mul,mul_zero,add_zero] at hw1
  have hcal := isolated_calibration C a b 0 ⟨ha.1.le,ha.2⟩
    ⟨hb.1.le,hb.2⟩ ⟨le_rfl,zero_lt_one⟩ hu0 hu1 hu2 hw hδ he
  rw [← hsum] at hcal
  let q0 := (C.plank 0).hi-C.relW 0-C.relW 1-b*C.relW 2
  let q1 := (C.plank 1).hi-C.relW 0-C.relW 1
  have hq0 : q0 ≤ b*C.deficit := by
    have hh := far_upper C hu hne hw hδ he 0 ⟨le_rfl,hδ.le⟩ 0
    simp only [hu0,hall,dot,Prod.fst_add,Prod.snd_add,one_mul,sub_zero,zero_add] at hh
    dsimp only [q0]
    nlinarith only [hh]
  have hq1 : q1 ≤ 0 := by
    have hh := far_upper C hu hne hw hδ he 0 ⟨le_rfl,hδ.le⟩ 1
    simp only [hu1,hall,dot,Prod.fst_add,Prod.snd_add,one_mul,zero_mul,add_zero,zero_add] at hh
    dsimp only [q1]
    linarith only [hh]
  have hab : 0 < 1-a*b := by nlinarith only [ha.1,ha.2,hb.1,hb.2]
  have hqstrict : q0 < a*b*C.deficit := by
    by_contra hn
    have hq := not_lt.mp hn
    let x := (q0-a*b*C.deficit)/(1-a*b)
    have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hq) hab.le
    have hxeq : x*(1-a*b)=q0-a*b*C.deficit := div_mul_cancel₀ _ (ne_of_gt hab)
    have hxδ : x < C.deficit := by
      apply (div_lt_iff₀ hab).mpr
      nlinarith only [hq0,mul_pos (sub_pos.mpr hb.2) hδ]
    let y := a*(C.deficit-x)
    have hy : 0 ≤ y := (mul_pos ha.1 (sub_pos.mpr hxδ)).le
    have hxy : x+y < C.deficit := by
      dsimp only [y]
      nlinarith only [mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hxδ)]
    apply no_corner C a b 0 ha hb ⟨le_rfl,zero_lt_one⟩ hu0 hu1 hu2 hw hδ he
      x y hx hy hxy
    · dsimp only [q0] at hxeq
      dsimp only [y]
      nlinarith only [hxeq]
    · dsimp only [q1] at hq1
      simpa only [zero_mul,add_zero] using (show (C.plank 1).hi ≤ x+C.relW 0+C.relW 1 by linarith only [hq1,hx])
    · dsimp only [y]
      nlinarith only [hcal.2]
  have hq1zero : q1=0 := by
    by_contra hn
    have hq1lt := lt_of_le_of_ne hq1 hn
    let y := (1+a)*C.deficit/2
    have hy : 0 < y := div_pos (mul_pos (by linarith only [ha.1]) hδ) (by norm_num)
    have hyδ : y < C.deficit := by dsimp only [y]; nlinarith only [ha.2,hδ]
    have hya : a*C.deficit < y := by dsimp only [y]; nlinarith only [ha.2,hδ]
    have hs : (0,y)+shift (steps C) Finset.univ ∈ exteriorCells C Finset.univ := by
      rw [exteriorCells,Plank.LinearBands.strictCell]
      apply Proofs.Symmetry.forall_fin_three
      · simp only [Finset.mem_univ,if_true,hall,hu0,dot,Prod.fst_add,Prod.snd_add,one_mul,zero_add]
        dsimp only [q0] at hqstrict
        nlinarith only [hqstrict,mul_pos hb.1 (sub_pos.mpr hya)]
      · simp only [Finset.mem_univ,if_true,hall,hu1,dot,Prod.fst_add,Prod.snd_add,one_mul,zero_add,zero_mul,add_zero]
        dsimp only [q1] at hq1lt
        linarith only [hq1lt]
      · simp only [Finset.mem_univ,if_true,hall,hu2,dot,Prod.fst_add,Prod.snd_add,one_mul,zero_add]
        nlinarith only [hcal.2,hya]
    have hz : (0,y) ∈ RowDeletion.triangle C.deficit := ⟨le_rfl,hy.le,by simpa using hyδ.le⟩
    have hh := (source_faces C hu hδ he Finset.univ hz hs).1 rfl
    rw [hall] at hh
    change C.relW 0+C.relW 1=0 at hh
    linarith only [hh,hw 0,hw 1]
  have hedge : (C.plank 1).lo=C.relW 0 := by
    dsimp only [q1] at hq1zero
    linarith only [hq1zero,hw1]
  have hlo : a*b*(C.deficit+C.relW 1) ≤ (C.plank 0).lo := by
    by_contra hn
    have hm : 0 < a*b*(C.deficit+C.relW 1)-(C.plank 0).lo := sub_pos.mpr (not_le.mp hn)
    let ε := min (C.relW 0) (a*b*(C.deficit+C.relW 1)-(C.plank 0).lo)/2
    have hε : 0 < ε := half_pos (lt_min (hw 0) hm)
    have hεr : ε < C.relW 0 := by
      have hh := min_le_left (C.relW 0) (a*b*(C.deficit+C.relW 1)-(C.plank 0).lo)
      dsimp only [ε]
      linarith only [hh,hw 0]
    have hεm : ε < a*b*(C.deficit+C.relW 1)-(C.plank 0).lo := by
      have hh := min_le_right (C.relW 0) (a*b*(C.deficit+C.relW 1)-(C.plank 0).lo)
      dsimp only [ε]
      linarith only [hh,hm]
    have hz : (C.relW 0-ε,a*(C.deficit+C.relW 1)) ∈ stdTriangle.set := by
      rw [Proofs.Quant.stdTriangle_set_eq]
      refine ⟨(sub_pos.mpr hεr).le,(mul_pos ha.1 (add_pos hδ (hw 1))).le,?_⟩
      change C.relW 0-ε+a*(C.deficit+C.relW 1) ≤ 1
      nlinarith only [hsum,mul_pos (sub_pos.mpr ha.2) (add_pos hδ (hw 1)),hε,hw 2]
    have hs : (C.relW 0-ε,a*(C.deficit+C.relW 1)) ∈ exteriorCells C {0} := by
      rw [exteriorCells,Plank.LinearBands.strictCell]
      apply Proofs.Symmetry.forall_fin_three
      · simp only [Finset.mem_singleton,if_true,hu0,dot,one_mul]
        nlinarith only [hεm,hw0]
      · simp only [Finset.mem_singleton,show (1 : Fin 3) ≠ 0 by decide,if_false,hu1,dot,one_mul,zero_mul,add_zero,hedge]
        linarith only [hε]
      · simp only [Finset.mem_singleton,show (2 : Fin 3) ≠ 0 by decide,if_false,hu2,dot,one_mul]
        nlinarith only [hcal.1,mul_pos ha.1 hε]
    have hh := (TriangleTranslationBoundary.common_vertex_cell_inequalities C hu hδ he {0} hz hs).1
    simp only [shift,Finset.sum_singleton,hs0] at hh
    linarith only [hh,hε]
  let m := min ((1-a)*C.deficit)
    (min (a*b*C.relW 1) (min (a*(C.relW 0+C.relW 1)) (C.relW 0)))
  have hm : 0 < m := lt_min (mul_pos (sub_pos.mpr ha.2) hδ)
    (lt_min (mul_pos (mul_pos ha.1 hb.1) (hw 1))
      (lt_min (mul_pos ha.1 (add_pos (hw 0) (hw 1))) (hw 0)))
  have hmδ : m ≤ (1-a)*C.deficit := min_le_left _ _
  have hmb : m ≤ a*b*C.relW 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hma : m ≤ a*(C.relW 0+C.relW 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hmr : m ≤ C.relW 0 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let ε := m/8
  have hε : 0 < ε := div_pos hm (by norm_num)
  have hεeq : 8*ε=m := by dsimp only [ε]; ring
  have hz : (ε,a*C.deficit+ε) ∈ RowDeletion.triangle C.deficit := by
    refine ⟨hε.le,(add_pos (mul_pos ha.1 hδ) hε).le,?_⟩
    change ε+(a*C.deficit+ε) ≤ C.deficit
    nlinarith only [hmδ,hεeq,hε]
  have hfull : (ε,a*C.deficit+ε)+shift (steps C) Finset.univ ∈ exteriorCells C Finset.univ := by
    rw [exteriorCells,Plank.LinearBands.strictCell]
    apply Proofs.Symmetry.forall_fin_three
    · simp only [Finset.mem_univ,if_true,hall,hu0,dot,Prod.fst_add,Prod.snd_add,one_mul]
      dsimp only [q0] at hqstrict
      nlinarith only [hqstrict,hε,mul_pos hb.1 hε]
    · simp only [Finset.mem_univ,if_true,hall,hu1,dot,Prod.fst_add,Prod.snd_add,one_mul,zero_mul,add_zero]
      dsimp only [q1] at hq1zero
      linarith only [hq1zero,hε]
    · simp only [Finset.mem_univ,if_true,hall,hu2,dot,Prod.fst_add,Prod.snd_add,one_mul]
      nlinarith only [hcal.2,hε,mul_pos ha.1 hε]
  have hempty : (ε,a*C.deficit+ε)+shift (steps C) ∅ ∈ exteriorCells C ∅ := by
    rw [exteriorCells,Plank.LinearBands.strictCell]
    apply Proofs.Symmetry.forall_fin_three
    · simp only [Finset.notMem_empty,if_false,shift,Finset.sum_empty,add_zero,hu0,dot,one_mul]
      nlinarith only [hlo,hmb,hεeq,hε,mul_pos (sub_pos.mpr hb.2) hε]
    · simp only [Finset.notMem_empty,if_false,shift,Finset.sum_empty,add_zero,hu1,dot,one_mul,zero_mul,hedge]
      linarith only [hmr,hεeq,hε]
    · simp only [Finset.notMem_empty,if_false,shift,Finset.sum_empty,add_zero,hu2,dot,one_mul]
      nlinarith only [hcal.1,hma,hεeq,hε,mul_pos (sub_pos.mpr ha.2) hε]
  have hh := source_unique C hu hδ he ∅ Finset.univ hz hempty hfull
  have hm0 : (0 : Fin 3) ∈ (∅ : Finset (Fin 3)) := hh.symm ▸ Finset.mem_univ 0
  simp at hm0

/-- The entire mixed sector with one strict horizontal direction, one
possibly edge-parallel horizontal direction, and one strict vertical
 direction is excluded, with arbitrary endpoints and actual widths. -/
theorem not_equality_with_boundary (C : Config) (a b c : ℝ)
    (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 ≤ c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(1,c))
    (hu2 : (C.plank 2).u=(a,1))
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    ¬ TriangleEqualityReductions.Equality C := by
  by_cases hpos : 0 < c
  · exact TriangleMixedStrict.not_equality C a b c ha hb ⟨hpos,hc.2⟩ hu0 hu1 hu2 hw hδ
  · have hc0 : c=0 := le_antisymm (not_lt.mp hpos) hc.1
    subst c
    exact not_equality C a b ha hb hu0 hu1 hu2 hw hδ

open MeasureTheory Proofs.Basic Proofs.Transport TriangleMixedTransport

/-- No normalization is assumed on the given normals. Their positive
coordinates encode a common minimum O and different unique maxima; the second horizontal
direction may be edge-parallel. -/
theorem not_equality_magnitudes (C : Config)
    (h0 : 0 < (C.plank 0).u.2 ∧ (C.plank 0).u.2 < (C.plank 0).u.1)
    (h1 : 0 ≤ (C.plank 1).u.2 ∧ (C.plank 1).u.2 < (C.plank 1).u.1)
    (h2 : 0 < (C.plank 2).u.1 ∧ (C.plank 2).u.1 < (C.plank 2).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    ¬ TriangleEqualityReductions.Equality C := by
  have hx0 : 0 < (C.plank 0).u.1 := h0.1.trans h0.2
  have hx1 : 0 < (C.plank 1).u.1 := lt_of_le_of_lt h1.1 h1.2
  have hy2 : 0 < (C.plank 2).u.2 := h2.1.trans h2.2
  let c : Fin 3 → ℝ := ![1/(C.plank 0).u.1,1/(C.plank 1).u.1,1/(C.plank 2).u.2]
  have hc : ∀ i, 0 < c i := by
    apply Proofs.Symmetry.forall_fin_three
    exacts [one_div_pos.mpr hx0,one_div_pos.mpr hx1,one_div_pos.mpr hy2]
  let D : Config := ⟨fun i => scaleP (c i) (hc i) (C.plank i)⟩
  have hwidth (i) : D.relW i=C.relW i := scale_width stdTriangle (C.plank i) (c i) (hc i)
  have hsum : D.sumRelW=C.sumRelW := by simp only [Config.sumRelW,hwidth]
  have hdef : D.deficit=C.deficit := by rw [Config.deficit,hsum]; rfl
  have hgap : D.gapArea=C.gapArea := by
    unfold Config.gapArea Config.uncovered
    simp only [D,scale_set]
  have hD0 : (D.plank 0).u=(1,(C.plank 0).u.2/(C.plank 0).u.1) := by
    change (1/(C.plank 0).u.1) • (C.plank 0).u = _
    apply Prod.ext <;> simp [div_eq_mul_inv,mul_comm,ne_of_gt hx0]
  have hD1 : (D.plank 1).u=(1,(C.plank 1).u.2/(C.plank 1).u.1) := by
    change (1/(C.plank 1).u.1) • (C.plank 1).u = _
    apply Prod.ext <;> simp [div_eq_mul_inv,mul_comm,ne_of_gt hx1]
  have hD2 : (D.plank 2).u=((C.plank 2).u.1/(C.plank 2).u.2,1) := by
    change (1/(C.plank 2).u.2) • (C.plank 2).u = _
    apply Prod.ext <;> simp [div_eq_mul_inv,mul_comm,ne_of_gt hy2]
  intro he
  apply not_equality_with_boundary D
    ((C.plank 2).u.1/(C.plank 2).u.2)
    ((C.plank 0).u.2/(C.plank 0).u.1)
    ((C.plank 1).u.2/(C.plank 1).u.1)
    ⟨div_pos h2.1 hy2,(div_lt_one hy2).mpr h2.2⟩
    ⟨div_pos h0.1 hx0,(div_lt_one hx0).mpr h0.2⟩
    ⟨div_nonneg h1.1 hx1.le,(div_lt_one hx1).mpr h1.2⟩ hD0 hD1 hD2
    (fun i => by rw [hwidth]; exact hw i) (by rwa [hdef])
  simpa only [TriangleEqualityReductions.Equality,hgap,hdef] using he

/-- On any triangle, three positive planks with a common minimum
vertex and two different strict maximum vertices, one horizontal direction
allowed to tie the minimum at the third vertex cannot attain equality.
The hypotheses state only the vertex orders of the original directions;
their magnitudes and all band positions are arbitrary. -/
theorem triangle_ne (T : Triangle) (p : Fin 3 → Plank)
    (h0 : dot (p 0).u T.A < dot (p 0).u T.C ∧ dot (p 0).u T.C < dot (p 0).u T.B)
    (h1 : dot (p 1).u T.A ≤ dot (p 1).u T.C ∧ dot (p 1).u T.C < dot (p 1).u T.B)
    (h2 : dot (p 2).u T.A < dot (p 2).u T.B ∧ dot (p 2).u T.B < dot (p 2).u T.C)
    (hw : ∀ i, 0 < (p i).relWidth T) (hR : (∑ i, (p i).relWidth T) < 1) :
    (volume (T.set \ ⋃ i, (p i).set)).toReal ≠
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal := by
  let C := AffineTransport.pullbackConfig T p
  have hc0 : 0 < (C.plank 0).u.2 ∧ (C.plank 0).u.2 < (C.plank 0).u.1 := by
    simp only [C,AffineTransport.pullbackConfig,pullbackPlank,dot_sub_right]
    constructor <;> linarith only [h0.1,h0.2]
  have hc1 : 0 ≤ (C.plank 1).u.2 ∧ (C.plank 1).u.2 < (C.plank 1).u.1 := by
    simp only [C,AffineTransport.pullbackConfig,pullbackPlank,dot_sub_right]
    constructor <;> linarith only [h1.1,h1.2]
  have hc2 : 0 < (C.plank 2).u.1 ∧ (C.plank 2).u.1 < (C.plank 2).u.2 := by
    simp only [C,AffineTransport.pullbackConfig,pullbackPlank,dot_sub_right]
    constructor <;> linarith only [h2.1,h2.2]
  have hcw (i) : C.relW i=(p i).relWidth T := relWidth_pullback T (p i)
  have hδ : 0 < C.deficit := by
    rw [AffineTransport.deficit_pullbackConfig]
    linarith only [hR]
  intro he
  apply not_equality_magnitudes C hc0 hc1 hc2 (fun i => by rw [hcw]; exact hw i) hδ
  rw [TriangleEqualityReductions.Equality,max_eq_right hδ.le,
    AffineTransport.deficit_pullbackConfig]
  apply mul_left_cancel₀ (abs_ne_zero.mpr (det3_ne_zero T))
  rw [AffineTransport.gapArea_transport,AffineTransport.area_triangle] at he
  change |det3 T.A T.B T.C| * C.gapArea =
    (1-∑ i, (p i).relWidth T)^2*(|det3 T.A T.B T.C| * (1/2)) at he
  rw [he]
  ring


end Quant.TriangleMixedOneEdge

/-- info: 'Quant.TriangleMixedOneEdge.not_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedOneEdge.not_equality

/-- info: 'Quant.TriangleMixedOneEdge.triangle_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedOneEdge.triangle_ne
