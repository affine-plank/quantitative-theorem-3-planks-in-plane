/- Geometric transport of the strict mixed triangle exclusion. -/
module
public import Plank.Proofs.Quant.TriangleMixedPair

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleMixedTransport
open Set MeasureTheory Proofs.Basic Proofs.Transport
open scoped BigOperators

theorem scale_set (p : Plank) (c : ℝ) (hc : 0 < c) : (scaleP c hc p).set=p.set := by
  ext z
  change (c*p.lo ≤ dot (c • p.u) z ∧ dot (c • p.u) z ≤ c*p.hi) ↔
    (p.lo ≤ dot p.u z ∧ dot p.u z ≤ p.hi)
  rw [dot_smul_left,mul_le_mul_iff_right₀ hc,mul_le_mul_iff_right₀ hc]

theorem scale_width (T : Triangle) (p : Plank) (c : ℝ) (hc : 0 < c) :
    (scaleP c hc p).relWidth T=p.relWidth T := by
  simp only [Plank.relWidth,scaleP,width_smul,abs_of_pos hc,← mul_sub]
  exact mul_div_mul_left _ _ (ne_of_gt hc)

/-- No normalization is assumed on the given normals. Their positive
coordinates encode a common unique minimum O and different unique maxima. -/
theorem not_equality (C : Config)
    (h0 : 0 < (C.plank 0).u.2 ∧ (C.plank 0).u.2 < (C.plank 0).u.1)
    (h1 : 0 < (C.plank 1).u.2 ∧ (C.plank 1).u.2 < (C.plank 1).u.1)
    (h2 : 0 < (C.plank 2).u.1 ∧ (C.plank 2).u.1 < (C.plank 2).u.2)
    (hw : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) :
    ¬ TriangleEqualityReductions.Equality C := by
  have hx0 : 0 < (C.plank 0).u.1 := h0.1.trans h0.2
  have hx1 : 0 < (C.plank 1).u.1 := h1.1.trans h1.2
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
  apply TriangleMixedStrict.not_equality D
    ((C.plank 2).u.1/(C.plank 2).u.2)
    ((C.plank 0).u.2/(C.plank 0).u.1)
    ((C.plank 1).u.2/(C.plank 1).u.1)
    ⟨div_pos h2.1 hy2,(div_lt_one hy2).mpr h2.2⟩
    ⟨div_pos h0.1 hx0,(div_lt_one hx0).mpr h0.2⟩
    ⟨div_pos h1.1 hx1,(div_lt_one hx1).mpr h1.2⟩ hD0 hD1 hD2
    (fun i => by rw [hwidth]; exact hw i) (by rwa [hdef])
  simpa only [TriangleEqualityReductions.Equality,hgap,hdef] using he

/-- On any triangle, three positive planks with a common strict minimum
vertex and two different strict maximum vertices cannot attain equality.
The hypotheses state only the vertex orders of the original directions;
their magnitudes and all band positions are arbitrary. -/
theorem triangle_ne (T : Triangle) (p : Fin 3 → Plank)
    (h0 : dot (p 0).u T.A < dot (p 0).u T.C ∧ dot (p 0).u T.C < dot (p 0).u T.B)
    (h1 : dot (p 1).u T.A < dot (p 1).u T.C ∧ dot (p 1).u T.C < dot (p 1).u T.B)
    (h2 : dot (p 2).u T.A < dot (p 2).u T.B ∧ dot (p 2).u T.B < dot (p 2).u T.C)
    (hw : ∀ i, 0 < (p i).relWidth T) (hR : (∑ i, (p i).relWidth T) < 1) :
    (volume (T.set \ ⋃ i, (p i).set)).toReal ≠
      (1-∑ i, (p i).relWidth T)^2*(volume T.set).toReal := by
  let C := AffineTransport.pullbackConfig T p
  have hc0 : 0 < (C.plank 0).u.2 ∧ (C.plank 0).u.2 < (C.plank 0).u.1 := by
    simp only [C,AffineTransport.pullbackConfig,pullbackPlank,dot_sub_right]
    constructor <;> linarith only [h0.1,h0.2]
  have hc1 : 0 < (C.plank 1).u.2 ∧ (C.plank 1).u.2 < (C.plank 1).u.1 := by
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
  apply not_equality C hc0 hc1 hc2 (fun i => by rw [hcw]; exact hw i) hδ
  rw [TriangleEqualityReductions.Equality,max_eq_right hδ.le,
    AffineTransport.deficit_pullbackConfig]
  apply mul_left_cancel₀ (abs_ne_zero.mpr (det3_ne_zero T))
  rw [AffineTransport.gapArea_transport,AffineTransport.area_triangle] at he
  change |det3 T.A T.B T.C| * C.gapArea =
    (1-∑ i, (p i).relWidth T)^2*(|det3 T.A T.B T.C| * (1/2)) at he
  rw [he]
  ring

end Quant.TriangleMixedTransport

/-- info: 'Quant.TriangleMixedTransport.triangle_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleMixedTransport.triangle_ne
