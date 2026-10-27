/- Actual oblique sections and packing of separated half-body profiles. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralReflections

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralObliqueSections
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralPlacement

/-- Coordinate on the line `x+k*y=q`; the coefficient of x is one. -/
def fiber (A : Set Point) (k q : ℝ) : Set ℝ := {y | (q-k*y,y) ∈ A}
def sectionLength (A : Set Point) (k q : ℝ) : ℝ := (volume (fiber A k q)).toReal

theorem compact_section (S : Shape) {A : Set Point} (hA : IsClosed A) (hsub : A ⊆ S.body)
    (k q : ℝ) : IsCompact (fiber A k q) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc : IsCompact (Icc (-S.d) S.b))
    (hA.preimage (show Continuous (fun y : ℝ => (q-k*y,y)) by fun_prop))
  intro y hy
  exact (coordinate_box S (hsub hy)).2

def lower (S : Shape) : Set Point := S.body ∩ {z | z.2 ≤ 0}
def upper (S : Shape) : Set Point := S.body ∩ {z | 0 ≤ z.2}

theorem lower_closed (S : Shape) : IsClosed (lower S) :=
  (compact_body S).isClosed.inter (isClosed_le continuous_snd continuous_const)
theorem upper_closed (S : Shape) : IsClosed (upper S) :=
  (compact_body S).isClosed.inter (isClosed_le continuous_const continuous_snd)

theorem lower_length_antitone (S : Shape) {k : ℝ} (hk : 0 ≤ k) :
    AntitoneOn (sectionLength (lower S) k) (Ici 0) := by
  intro a ha b _ hab
  change 0 ≤ a at ha
  apply ENNReal.toReal_mono (compact_section S (lower_closed S) inter_subset_left k a).measure_ne_top
  apply measure_mono
  rintro y ⟨hbody,hy⟩
  have hka : k*y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk hy
  have hxa : 0 ≤ a-k*y := by linarith only [ha,hka]
  have hxab : a-k*y ≤ b-k*y := sub_le_sub_right hab _
  have hzero := zero_x_mem S hbody
  have hm : (a-k*y,y) ∈ S.body := by
    by_cases hb : b-k*y = 0
    · have hz : a-k*y = 0 := le_antisymm (by simpa only [hb] using hxab) hxa
      simpa only [hz] using hzero
    · have hp : 0 < b-k*y := lt_of_le_of_ne (hxa.trans hxab) (Ne.symm hb)
      have hh := contract_x_mem S hbody
        (div_nonneg hxa hp.le) ((div_le_one hp).mpr hxab)
      simpa only [div_mul_cancel₀ _ hb] using hh
  exact ⟨hm,hy⟩

theorem upper_length_monotone (S : Shape) {k : ℝ} (hk : 0 ≤ k) :
    MonotoneOn (sectionLength (upper S) k) (Iic 0) := by
  intro a _ b hb hab
  change b ≤ 0 at hb
  apply ENNReal.toReal_mono (compact_section S (upper_closed S) inter_subset_left k b).measure_ne_top
  apply measure_mono
  rintro y ⟨hbody,hy⟩
  have hka : 0 ≤ k*y := mul_nonneg hk hy
  have hxb : b-k*y ≤ 0 := by linarith only [hb,hka]
  have hxab : a-k*y ≤ b-k*y := sub_le_sub_right hab _
  have hzero := zero_x_mem S hbody
  have hm : (b-k*y,y) ∈ S.body := by
    by_cases ha : a-k*y = 0
    · have hz : b-k*y = 0 := le_antisymm hxb (by simpa only [ha] using hxab)
      simpa only [hz] using hzero
    · have hn : a-k*y < 0 := lt_of_le_of_ne (hxab.trans hxb) ha
      have hh := contract_x_mem S hbody
        (div_nonneg_of_nonpos hxb hn.le) ((div_le_one_of_neg hn).mpr hxab)
      simpa only [div_mul_cancel₀ _ ha] using hh
  exact ⟨hm,hy⟩

theorem length_split (S : Shape) (k q : ℝ) :
    sectionLength S.body k q = sectionLength (lower S) k q+sectionLength (upper S) k q := by
  have hu : fiber S.body k q = fiber (lower S) k q ∪ fiber (upper S) k q := by
    ext y
    simp only [fiber,lower,upper,mem_ofPred_eq,mem_inter_iff,mem_union]
    exact ⟨fun h => (le_total y 0).imp (fun hy => ⟨h,hy⟩) (fun hy => ⟨h,hy⟩),
      fun h => h.elim And.left And.left⟩
  have hl := compact_section S (lower_closed S) inter_subset_left k q
  have hh := compact_section S (upper_closed S) inter_subset_left k q
  have hd : AEDisjoint volume (fiber (lower S) k q) (fiber (upper S) k q) := by
    apply measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
    rintro y ⟨⟨_,hy⟩,⟨_,hy'⟩⟩
    exact le_antisymm hy hy'
  rw [sectionLength,hu,measure_union₀ hh.measurableSet.nullMeasurableSet hd,
    ENNReal.toReal_add hl.measure_ne_top hh.measure_ne_top]
  rfl

/-- Separating profiles with opposite monotonicity cannot increase their
combined fiber maximum. The witness is an actual fiber of the original body. -/
theorem separated_sections (S : Shape) {k a b : ℝ} (hk : 0 ≤ k) (hab : a ≤ b) :
    ∃ q : ℝ, sectionLength (lower S) k b+sectionLength (upper S) k a ≤
      sectionLength S.body k q := by
  by_cases hb : b ≤ 0
  · refine ⟨b,?_⟩
    rw [length_split]
    exact add_le_add le_rfl (upper_length_monotone S hk (hab.trans hb) hb hab)
  · by_cases ha : 0 ≤ a
    · refine ⟨a,?_⟩
      rw [length_split]
      exact add_le_add (lower_length_antitone S hk ha (ha.trans hab) hab) le_rfl
    · refine ⟨0,?_⟩
      rw [length_split]
      exact add_le_add (lower_length_antitone S hk (by simp) (le_of_not_ge hb) (le_of_not_ge hb))
        (upper_length_monotone S hk (le_of_not_ge ha) (by simp) (le_of_not_ge ha))

end Quant.CrossedQuadrilateralObliqueSections

/-- info: 'Quant.CrossedQuadrilateralObliqueSections.separated_sections' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralObliqueSections.separated_sections
