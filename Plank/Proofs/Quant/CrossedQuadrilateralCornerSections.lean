/- Section measures of the four homothetic corner pieces. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralCoreProfiles

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralCornerSections
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralObliqueSections
open CrossedQuadrilateralCalibratedSections CrossedQuadrilateralCoreProfiles
open scoped BigOperators Function

theorem closed_corner (S : Shape) (r s : ℝ) (i j : Bool) : IsClosed (corner S r s i j) :=
  (isClosed_le continuous_const (continuous_fst.div_const _)).inter
    ((isClosed_le continuous_const (continuous_snd.div_const _)).inter
      (isClosed_le ((continuous_fst.div_const _).add (continuous_snd.div_const _)) continuous_const))

theorem closed_core (S : Shape) (i j : Bool) : IsClosed (core S i j) :=
  closed_corner S 0 0 i j

theorem fiber_homothet (A : Set Point) (ξ η δ k q : ℝ) (hδ : δ ≠ 0) :
    fiber ((fun z : Point => (ξ,η)+δ • z) '' A) k q =
      (fun y : ℝ => η+δ*y) '' fiber A k ((q-ξ-k*η)/δ) := by
  ext y
  constructor
  · rintro ⟨z,hz,he⟩
    have hx : ξ+δ*z.1 = q-k*y := congrArg Prod.fst he
    have hy : η+δ*z.2 = y := congrArg Prod.snd he
    have hh : z.1+k*z.2 = (q-ξ-k*η)/δ := by
      apply (eq_div_iff hδ).mpr
      linear_combination hx+k*hy
    have hcoord : (q-ξ-k*η)/δ-k*z.2=z.1 := by linarith only [hh]
    refine ⟨z.2,?_,hy⟩
    change ((q-ξ-k*η)/δ-k*z.2,z.2) ∈ A
    simpa only [hcoord] using hz
  · rintro ⟨y,hy,rfl⟩
    refine ⟨((q-ξ-k*η)/δ-k*y,y),hy,?_⟩
    ext
    · change ξ+δ*((q-ξ-k*η)/δ-k*y)=q-k*(η+δ*y)
      field_simp [hδ]
      ring
    · rfl

theorem length_corner (S : Shape) {r s : ℝ} (hrs : r+s < 1) (k q : ℝ) (i j : Bool) :
    sectionLength (corner S r s i j) k q = (1-r-s)*
      sectionLength (core S i j) k ((q-(S.X i*r+k*(S.Y j*s)))/(1-r-s)) := by
  have ht : 0 < 1-r-s := by linarith only [hrs]
  rw [corner_eq_image S hrs,sectionLength,fiber_homothet _ _ _ _ _ _ ht.ne',
    length_translate_scale _ _ _ ht.le]
  change (1-r-s)*sectionLength (core S i j) k
    ((q-S.X i*r-k*(S.Y j*s))/(1-r-s)) = _
  rw [show (q-S.X i*r-k*(S.Y j*s))/(1-r-s) =
    (q-(S.X i*r+k*(S.Y j*s)))/(1-r-s) by ring]

theorem signed_zero {p n x : ℝ} (hp : 0 < p) (hn : 0 < n)
    {i j : Bool} (hne : i ≠ j)
    (hi : 0 ≤ x/(if i then p else -n))
    (hj : 0 ≤ x/(if j then p else -n)) : x = 0 := by
  have hz (hx : 0 ≤ x/p) (hy : 0 ≤ x/(-n)) : x=0 := by
    rw [le_div_iff₀ hp,zero_mul] at hx
    rw [le_div_iff_of_neg (neg_lt_zero.mpr hn),zero_mul] at hy
    exact le_antisymm hy hx
  cases i <;> cases j
  · exact False.elim (hne rfl)
  · exact hz hj hi
  · exact hz hi hj
  · exact False.elim (hne rfl)

theorem core_fibers_aedisjoint (S : Shape) {k : ℝ} (hk : k ≠ 0) (q : ℝ) :
    Pairwise (AEDisjoint volume on fun e : Bool × Bool => fiber (core S e.1 e.2) k q) := by
  intro e f hne
  by_cases hx : e.1=f.1
  · have hy : e.2 ≠ f.2 := fun hy => hne (Prod.ext hx hy)
    apply measure_mono_null (t := ({0} : Set ℝ)) ?_ (measure_singleton 0)
    intro y hy'
    exact signed_zero S.hb S.hd hy hy'.1.2.1 hy'.2.2.1
  · apply measure_mono_null (t := ({q/k} : Set ℝ)) ?_ (measure_singleton (q/k))
    intro y hy
    have hh : q-k*y=0 := signed_zero S.ha S.hc hx hy.1.1 hy.2.1
    change y=q/k
    apply (eq_div_iff hk).mpr
    nlinarith only [hh]

theorem body_length_sum (S : Shape) {k : ℝ} (hk : k ≠ 0) (q : ℝ) :
    sectionLength S.body k q = ∑ e : Bool × Bool, sectionLength (core S e.1 e.2) k q := by
  have he : fiber S.body k q = ⋃ e : Bool × Bool, fiber (core S e.1 e.2) k q := by
    ext y
    simp only [fiber,mem_ofPred_eq,body_eq_cores,mem_iUnion,Prod.exists]
  have hc (e : Bool × Bool) := compact_section S (closed_core S e.1 e.2)
    (core_subset_body S e.1 e.2) k q
  have hu : volume (⋃ e : Bool × Bool, fiber (core S e.1 e.2) k q) =
      ∑ e : Bool × Bool, volume (fiber (core S e.1 e.2) k q) := by
    simpa using measure_biUnion_finset₀ (μ := volume) (s := Finset.univ)
      (f := fun e : Bool × Bool => fiber (core S e.1 e.2) k q)
      (fun _ _ _ _ h => core_fibers_aedisjoint S hk q h)
      (fun e _ => (hc e).measurableSet.nullMeasurableSet)
  rw [sectionLength,he,hu,ENNReal.toReal_sum (fun e _ => (hc e).measure_ne_top)]
  rfl

def closedCorners (S : Shape) (r s : ℝ) : Set Point :=
  ⋃ e : Bool × Bool, corner S r s e.1 e.2

theorem corners_length_le (S : Shape) (r s k q : ℝ) :
    sectionLength (closedCorners S r s) k q ≤
      ∑ e : Bool × Bool, sectionLength (corner S r s e.1 e.2) k q := by
  have he : fiber (closedCorners S r s) k q =
      ⋃ e : Bool × Bool, fiber (corner S r s e.1 e.2) k q := by
    ext y
    simp only [fiber,closedCorners,mem_ofPred_eq,mem_iUnion]
  rw [sectionLength,he]
  exact measureReal_iUnion_fintype_le (μ := volume)
    (fun e : Bool × Bool => fiber (corner S r s e.1 e.2) k q)

end Quant.CrossedQuadrilateralCornerSections

/-- info: 'Quant.CrossedQuadrilateralCornerSections.body_length_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralCornerSections.body_length_sum
