/- Strict extension bounds using calibrated bands inside arbitrary diagonal cuts. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralDoublePacking
public import Plank.Proofs.Quant.CrossedQuadrilateralThinExtension

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralInnerPacking
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open CrossedQuadrilateralCornerSections CrossedQuadrilateralDoublePacking
open CrossedQuadrilateralResidualArea CrossedQuadrilateralObliquePeak
open CrossedQuadrilateralThinExtension
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def axisGap (S : Shape) (lx ux ly uy : ℝ) : Set Point := S.body \
  (CrossedQuadrilateralPlacement.band false lx ux ∪
    CrossedQuadrilateralPlacement.band true ly uy)

def budget (S : Shape) (lx ux ly uy : ℝ) : ℝ :=
  (ux-lx)/(S.a+S.c)+(uy-ly)/(S.b+S.d)

/-- A zero inner width imposes no condition on the location of the actual band. -/
def Inner (p n r lo hi : ℝ) : Prop := r = 0 ∨ lo ≤ -n*r ∧ p*r ≤ hi

theorem inner_open {p n r lo hi x : ℝ} (h : Inner p n r lo hi)
    (hx : -n*r < x ∧ x < p*r) : lo ≤ x ∧ x ≤ hi := by
  rcases h with rfl | h
  · simp only [mul_zero] at hx
    exact False.elim (lt_asymm hx.1 hx.2)
  · exact ⟨h.1.trans hx.1.le,hx.2.le.trans h.2⟩

theorem axisGap_subset (S : Shape) {r s lx ux ly uy : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hx : Inner S.a S.c r lx ux)
    (hy : Inner S.b S.d s ly uy) :
    axisGap S lx ux ly uy ⊆ closedCorners S r s := by
  change axisGap S lx ux ly uy ⊆ ⋃ e : Bool × Bool, corner S r s e.1 e.2
  rw [← open_gap_eq_corners S hr hs]
  intro z hz
  refine ⟨hz.1,?_⟩
  rintro (h | h)
  · exact hz.2 (Or.inl (inner_open hx h))
  · exact hz.2 (Or.inr (inner_open hy h))

theorem strict_subset_bound (S : Shape) {k : ℝ} (hk : k ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ M < 2*(volume S.body).toReal ∧
      ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → r+s < 1 →
      ∀ A : Set Point, A ⊆ closedCorners S r s → ∀ lo hi : ℝ, lo ≤ hi →
        (volume (A ∩ band k lo hi)).toReal ≤
          (1-r-s)*M*((hi-lo)/rangeWidth S.body (direction (1,k))) := by
  obtain ⟨M,hM,hm,hbound⟩ := strict_original_bound S hk
  let w := rangeWidth S.body (direction (1,k))
  have hw : 0 < w := direction_width_pos S (by
    intro he; have hh := congrArg Prod.fst he; norm_num at hh)
  refine ⟨M*w,mul_nonneg hM hw.le,hm,?_⟩
  intro r s hr hs hrs A hA lo hi ho
  have ht : 0 ≤ 1-r-s := by linarith only [hrs]
  have hclosed (q) : sectionLength (closedCorners S r s) k q ≤ (1-r-s)*M := by
    obtain ⟨v,hv⟩ := closed_section_packing S hr hs hrs hk q
    exact hv.trans (mul_le_mul_of_nonneg_left (hbound v) ht)
  have ha := area_band_le (compact_closed S hr hs) k ((1-r-s)*M) hclosed ho
  have hmono : (volume (A ∩ band k lo hi)).toReal ≤
      (volume (closedCorners S r s ∩ band k lo hi)).toReal :=
    ENNReal.toReal_mono
      (measure_ne_top_of_subset inter_subset_left (compact_closed S hr hs).measure_ne_top)
      (measure_mono (fun _ hz => ⟨hA hz.1,hz.2⟩))
  refine (hmono.trans ha).trans_eq ?_
  change (hi-lo)*((1-r-s)*M) = (1-r-s)*(M*w)*((hi-lo)/w)
  field_simp [hw.ne']

theorem removed_pair_le {A : Set Point} (hA : volume A ≠ ⊤) (k lo hi : Fin 2 → ℝ) :
    (volume A).toReal-(volume (A \ ⋃ i, band (k i) (lo i) (hi i))).toReal ≤
      ∑ i, (volume (A ∩ band (k i) (lo i) (hi i))).toReal := by
  have hm : MeasurableSet (⋃ i, band (k i) (lo i) (hi i)) :=
    MeasurableSet.iUnion (fun i => measurable_band _ _ _)
  have hd := measureReal_sdiff_add_inter (μ := volume) (s := A) hm hA
  have hu := measureReal_iUnion_fintype_le (μ := volume)
    (fun i => A ∩ band (k i) (lo i) (hi i))
  rw [← inter_iUnion] at hu
  change (volume (A \ ⋃ i, band (k i) (lo i) (hi i))).toReal+
    (volume (A ∩ ⋃ i, band (k i) (lo i) (hi i))).toReal = (volume A).toReal at hd
  change (volume (A ∩ ⋃ i, band (k i) (lo i) (hi i))).toReal ≤
    ∑ i, (volume (A ∩ band (k i) (lo i) (hi i))).toReal at hu
  linarith only [hd,hu]

/-- The actual diagonal bands may be uncalibrated: containing smaller calibrated
open bands is enough. Both additional slopes and every actual relative width are
explicit. The only smallness condition is the displayed strict scalar inequality. -/
theorem strict_extension (S : Shape) (k : Fin 2 → ℝ) (hk : ∀ i, k i ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ B < 2*(volume S.body).toReal ∧
      ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → r+s < 1 →
      ∀ lx ux ly uy : ℝ, lx ≤ ux → ly ≤ uy → budget S lx ux ly uy < 1 →
      Inner S.a S.c r lx ux → Inner S.b S.d s ly uy →
      ∀ lo hi : Fin 2 → ℝ, (∀ i, lo i ≤ hi i) → 0 < total S k lo hi →
      total S k lo hi*(volume S.body).toReal <
        2*(1-budget S lx ux ly uy)*(volume S.body).toReal-(1-r-s)*B →
      (1-budget S lx ux ly uy-total S k lo hi)^2*(volume S.body).toReal <
        (volume (axisGap S lx ux ly uy \ ⋃ i, band (k i) (lo i) (hi i))).toReal := by
  choose M hM hstrict hbound using fun i => strict_subset_bound S (hk i)
  let B := max (M 0) (M 1)
  have hMB (i : Fin 2) : M i ≤ B := by
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  refine ⟨B,(hM 0).trans (hMB 0),max_lt (hstrict 0) (hstrict 1),?_⟩
  intro r s hr hs hrs lx ux ly uy hx hy hb hix hiy lo hi ho ht hsmall
  have hsub := axisGap_subset S hr hs hix hiy
  have hf : volume (axisGap S lx ux ly uy) ≠ ⊤ :=
    measure_ne_top_of_subset sdiff_subset (compact_body S).measure_ne_top
  have hrem : 0 ≤ 1-r-s := by linarith only [hrs]
  have hw (i : Fin 2) : 0 < rangeWidth S.body (direction (1,k i)) :=
    direction_width_pos S (by intro he; have hh := congrArg Prod.fst he; norm_num at hh)
  have hwidth (i : Fin 2) : 0 ≤ (hi i-lo i)/rangeWidth S.body (direction (1,k i)) :=
    div_nonneg (sub_nonneg.mpr (ho i)) (hw i).le
  have hu := (removed_pair_le hf k lo hi).trans
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (hbound i r s hr hs hrs _ hsub (lo i) (hi i) (ho i)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hMB i) hrem) (hwidth i))))
  rw [← Finset.mul_sum] at hu
  change (volume (axisGap S lx ux ly uy)).toReal-
    (volume (axisGap S lx ux ly uy \ ⋃ i, band (k i) (lo i) (hi i))).toReal ≤
      (1-r-s)*B*total S k lo hi at hu
  have hl := CrossedQuadrilateralPlacement.arbitrary_placement_lower_bound S lx ux ly uy hx hy hb
  have he : 1-(ux-lx)/(S.a+S.c)-(uy-ly)/(S.b+S.d) = 1-budget S lx ux ly uy := by
    unfold budget
    ring
  rw [he] at hl
  change (1-budget S lx ux ly uy)^2*(volume S.body).toReal ≤
    (volume (axisGap S lx ux ly uy)).toReal at hl
  have hp := mul_pos ht (sub_pos.mpr hsmall)
  nlinarith only [hu,hl,hp]

end Quant.CrossedQuadrilateralInnerPacking

/-- info: 'Quant.CrossedQuadrilateralInnerPacking.strict_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralInnerPacking.strict_extension
