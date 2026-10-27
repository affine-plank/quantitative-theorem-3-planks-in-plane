/- An exact geometric equality criterion for one plank on an arbitrary
finite-dimensional convex body. The two exterior caps must exhaust translated copies
of the contracted body. No triangular or polyhedral body is assumed. -/
module

public import Plank.Proofs.AffineWidth
public import Plank.Measure.LinearBands
public import Plank.Measure.ConvexBody
public import Plank.Proofs.Quant.TranslationEquality

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalOnePlankEquality

open Set MeasureTheory Function
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The lower and upper pieces of the body contracted by `1-r`, translated
toward its two support points, and restricted to the corresponding gap side. -/
def homotheticCaps (K : Set E) (f : E →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (a b : E) (r : ℝ) : Set E :=
  ({x | x-r • b ∈ (1-r) • K} ∩ {x | f x < lo}) ∪
    ({x | x-r • a ∈ (1-r) • K} ∩ {x | hi < f x})

/-- Exhaustive self-similarity criterion, for any chosen maximum and minimum
support points. The right side contains only the body, affine cuts and
homotheties; it imposes no volume equation. Classifying the shapes satisfying
this self-similarity is a separate geometric problem. -/
theorem equality_iff_homothetic_caps (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : E →ᵃ[ℝ] ℝ)
    (lo hi : ℝ) (ho : lo ≤ hi) (hW : 0 < Body.width K f)
    (hr1 : (hi-lo)/Body.width K f < 1)
    (a b : E) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x) :
    (μ (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
        (1-(hi-lo)/Body.width K f)^Module.finrank ℝ E*(μ K).toReal ↔
      homotheticCaps K f lo hi a b ((hi-lo)/Body.width K f) =ᵐ[μ]
        (K \ {x | lo ≤ f x ∧ f x ≤ hi}) := by
  classical
  let r := (hi-lo)/Body.width K f
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr ho) hW.le
  have hq : 0 ≤ 1-r := sub_nonneg.mpr hr1.le
  have hspan : Body.width K f = f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
  have hpaid : r*(f a-f b) = hi-lo := by
    rw [← hspan]
    exact div_mul_cancel₀ _ hW.ne'
  have hcomb (x z : E) : f ((1-r) • x+r • z) = (1-r)*f x+r*f z := by
    simpa only [AffineMap.lineMap_apply_module,AffineMap.lineMap_apply_ring,smul_eq_mul]
      using f.apply_lineMap x z r
  let core : Set E := (1-r) • K
  let v : Bool → E := fun s => if s then r • a else r • b
  let cells : Bool → Set E := fun s => if s then {x | hi < f x} else {x | f x < lo}
  let gap := K \ {x | lo ≤ f x ∧ f x ≤ hi}
  have hcore : IsCompact core := hK.image (f := fun x : E => (1-r) • x) (by fun_prop)
  have hcells (s) : MeasurableSet (cells s) := by
    cases s
    · exact measurableSet_lt (f.continuous_of_finiteDimensional).measurable measurable_const
    · exact measurableSet_lt measurable_const (f.continuous_of_finiteDimensional).measurable
  have hdis : Pairwise (Disjoint on cells) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    cases i <;> cases j
    · exact hij rfl
    · change f x < lo at hx
      change hi < f x at hy
      linarith only [hx,hy,ho]
    · change hi < f x at hx
      change f x < lo at hy
      linarith only [hx,hy,ho]
    · exact hij rfl
  have hgapfin : μ gap ≠ ⊤ :=
    ne_top_of_le_ne_top hK.measure_ne_top (measure_mono sdiff_subset)
  have hbad : μ {x : E | f (x+r • b) = lo} = 0 := by
    change μ ((fun x => x+r • b) ⁻¹' {x | f x = lo}) = 0
    rw [measure_preimage_add_right]
    have hf : f.linear.toContinuousLinearMap ≠ 0 := by
      intro hz
      have hz' : f.linear = 0 := by
        simpa using congrArg ContinuousLinearMap.toLinearMap hz
      obtain ⟨c,he⟩ := f.linear_eq_zero_iff_exists_const.mp hz'
      have hzero : Body.width K f = 0 := by
        rw [hspan,he]
        simp
      exact hW.ne' hzero
    have hlevel : {x | f x = lo} =
        {x | f.linear.toContinuousLinearMap x = lo-f 0} := by
      ext x
      have he : f x = f.linear x+f 0 := congrFun f.decomp x
      change f x = lo ↔ f.linear x = lo-f 0
      rw [he]
      exact eq_sub_iff_add_eq.symm
    rw [hlevel]
    exact LinearBands.measure_level_zero μ _ hf _
  have hassign : ∀ᵐ x ∂μ, x ∈ core → ∃ s, x+v s ∈ cells s := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hbad] with x hx hxcore
    obtain ⟨z,hz,rfl⟩ := hxcore
    have hne' : f ((1-r) • z+r • b) ≠ lo := hx
    rcases lt_or_gt_of_ne hne' with hl | hl
    · exact ⟨false,hl⟩
    · refine ⟨true,?_⟩
      change hi < f ((1-r) • z+r • a)
      rw [hcomb] at hl ⊢
      nlinarith only [hl,hpaid]
  have hinside : ∀ s x, x ∈ core → x+v s ∈ cells s → x+v s ∈ gap := by
    intro s x hx hs
    obtain ⟨z,hz,rfl⟩ := hx
    cases s
    · refine ⟨hconv hz hb hq hr (sub_add_cancel 1 r),?_⟩
      change f ((1-r) • z+r • b) < lo at hs
      exact fun h => hs.not_ge h.1
    · refine ⟨hconv hz ha hq hr (sub_add_cancel 1 r),?_⟩
      change hi < f ((1-r) • z+r • a) at hs
      exact fun h => hs.not_ge h.2
  have hunique : Pairwise (Disjoint on Quant.TranslationEquality.sourcePiece core v cells) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨z,hz,hxrep⟩ := hx.1
    have hx' := hx.2
    have hy' := hy.2
    rw [← hxrep] at hx' hy'
    cases i <;> cases j
    · exact hij rfl
    · change f ((1-r) • z+r • b) < lo at hx'
      change hi < f ((1-r) • z+r • a) at hy'
      rw [hcomb] at hx' hy'
      nlinarith only [hx',hy',hpaid]
    · change hi < f ((1-r) • z+r • a) at hx'
      change f ((1-r) • z+r • b) < lo at hy'
      rw [hcomb] at hx' hy'
      nlinarith only [hx',hy',hpaid]
    · exact hij rfl
  have hcarea : (μ core).toReal = (1-r)^Module.finrank ℝ E*(μ K).toReal := by
    rw [μ.addHaar_smul_of_nonneg hq,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hq _)]
  have he := Quant.TranslationEquality.measure_eq_iff μ core hcore.measurableSet
    v cells hcells hdis gap hgapfin hassign hinside
  have hpieces : (⋃ s, Quant.TranslationEquality.targetPiece core v cells s) =
      homotheticCaps K f lo hi a b r := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨s,hs⟩
      cases s
      · exact Or.inl hs
      · exact Or.inr hs
    · rintro (hx | hx)
      · exact ⟨false,hx⟩
      · exact ⟨true,hx⟩
  rw [hpieces] at he
  have huniq : Pairwise (AEDisjoint μ on Quant.TranslationEquality.sourcePiece core v cells) :=
    fun _ _ hij => (hunique hij).aedisjoint
  rw [and_iff_right huniq] at he
  change (μ gap).toReal = (1-r)^Module.finrank ℝ E*(μ K).toReal ↔ _
  rw [← hcarea,eq_comm,ENNReal.toReal_eq_toReal_iff' hcore.measure_ne_top hgapfin]
  exact he

/-- A closed, entirely geometric covering condition: the original plank
together with the correctly sided pieces of its two support homothets. -/
def closedHomotheticCover (K : Set E) (f : E →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (a b : E) (r : ℝ) : Set E :=
  {x | lo ≤ f x ∧ f x ≤ hi} ∪
    (({x | x-r • b ∈ (1-r) • K} ∩ {x | f x ≤ lo}) ∪
      ({x | x-r • a ∈ (1-r) • K} ∩ {x | hi ≤ f x}))

/-- For a positive-volume body the criterion is an actual closed cover,
including all body-boundary points. No almost-everywhere condition remains. -/
theorem equality_iff_homothetic_cover (μ : Measure E) [μ.IsAddHaarMeasure] {K : Set E} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (μ K).toReal)
    (f : E →ᵃ[ℝ] ℝ) (lo hi : ℝ) (ho : lo ≤ hi) (hW : 0 < Body.width K f)
    (hr1 : (hi-lo)/Body.width K f < 1)
    (a b : E) (ha : a ∈ K) (hb : b ∈ K)
    (hmax : ∀ x ∈ K, f x ≤ f a) (hmin : ∀ x ∈ K, f b ≤ f x) :
    (μ (K \ {x | lo ≤ f x ∧ f x ≤ hi})).toReal =
        (1-(hi-lo)/Body.width K f)^Module.finrank ℝ E*(μ K).toReal ↔
      K ⊆ closedHomotheticCover K f lo hi a b ((hi-lo)/Body.width K f) := by
  let r := (hi-lo)/Body.width K f
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr ho) hW.le
  have hq : 0 ≤ 1-r := sub_nonneg.mpr hr1.le
  have hcore : IsCompact ((1-r) • K) :=
    hK.image (f := fun x : E => (1-r) • x) (by fun_prop)
  have hcopy (z : E) (hz : z ∈ K) (x : E) (hx : x-r • z ∈ (1-r) • K) : x ∈ K := by
    obtain ⟨y,hy,he⟩ := hx
    change (1-r) • y = x-r • z at he
    have hh := hconv hy hz hq hr (sub_add_cancel 1 r)
    rwa [he,sub_add_cancel] at hh
  have hclosed : IsClosed (closedHomotheticCover K f lo hi a b r) := by
    have hp (z : E) : IsClosed {x : E | x-r • z ∈ (1-r) • K} :=
      hcore.isClosed.preimage (by fun_prop)
    exact ((isClosed_le continuous_const (f.continuous_of_finiteDimensional)).inter
      (isClosed_le (f.continuous_of_finiteDimensional) continuous_const)).union
        (((hp b).inter (isClosed_le (f.continuous_of_finiteDimensional) continuous_const)).union
          ((hp a).inter (isClosed_le continuous_const (f.continuous_of_finiteDimensional))))
  rw [equality_iff_homothetic_caps μ hK hconv f lo hi ho hW hr1 a b ha hb hmax hmin]
  constructor
  · intro he
    have hnull : μ ((K \ {x | lo ≤ f x ∧ f x ≤ hi}) \
        homotheticCaps K f lo hi a b r) = 0 := ae_le_set.mp he.symm.le
    have hsub : (K \ closedHomotheticCover K f lo hi a b r) ⊆
        ((K \ {x | lo ≤ f x ∧ f x ≤ hi}) \ homotheticCaps K f lo hi a b r) := by
      intro x hx
      refine ⟨⟨hx.1,fun hh => hx.2 (Or.inl hh)⟩,?_⟩
      rintro (hl | hh)
      · exact hx.2 (Or.inr (Or.inl ⟨hl.1,(show f x < lo from hl.2).le⟩))
      · exact hx.2 (Or.inr (Or.inr ⟨hh.1,(show hi < f x from hh.2).le⟩))
    apply (ConvexBodyMeasure.measure_sdiff_eq_zero_iff_subset μ hK hconv hV hclosed).mp
    rw [measure_mono_null hsub hnull,ENNReal.toReal_zero]
  · intro hcover
    have he : homotheticCaps K f lo hi a b r = K \ {x | lo ≤ f x ∧ f x ≤ hi} := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hx with hl | hh
        · exact ⟨hcopy b hb x hl.1,fun hp => hl.2.not_ge hp.1⟩
        · exact ⟨hcopy a ha x hh.1,fun hp => hh.2.not_ge hp.2⟩
      · intro x hx
        rcases hcover hx.1 with hp | hl | hh
        · exact (hx.2 hp).elim
        · refine Or.inl ⟨hl.1,?_⟩
          change f x < lo
          apply lt_of_le_of_ne (show f x ≤ lo from hl.2)
          intro he
          exact hx.2 ⟨he.symm.le,he.le.trans ho⟩
        · refine Or.inr ⟨hh.1,?_⟩
          change hi < f x
          apply lt_of_le_of_ne (show hi ≤ f x from hh.2)
          intro he
          exact hx.2 ⟨ho.trans he.le,he.symm.le⟩
    exact Filter.Eventually.of_forall fun x => congrArg (fun S => x ∈ S) he

end Plank.FiniteDimensionalOnePlankEquality

/-- info: 'Plank.FiniteDimensionalOnePlankEquality.equality_iff_homothetic_caps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FiniteDimensionalOnePlankEquality.equality_iff_homothetic_caps
/-- info: 'Plank.FiniteDimensionalOnePlankEquality.equality_iff_homothetic_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FiniteDimensionalOnePlankEquality.equality_iff_homothetic_cover
