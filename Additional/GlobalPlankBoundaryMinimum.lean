/- Global body minimality excludes positive planks reaching a support level.
The homothetic competitor uses the same indexed family and no induction. -/
module

public import GlobalPlankBodyMinimum
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalPlankBoundaryMinimum

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum

/-- A contraction with the matching volume power and a sufficiently increased
relative deficit strictly improves every negative normalized margin. -/
theorem contraction_margin_lt {G H V W R S B q : ℝ} {d : ℕ}
    (hd : 0<d) (hq : 0<q) (hq1 : q<1) (hV : 0<V)
    (hW : W=q^d*V) (hG : H≤G) (hR : R≤B)
    (hdef : (B-R)/q≤B-S) (hneg : G/V-(B-R)^d<0) :
    H/W-(B-S)^d<G/V-(B-R)^d := by
  have hp : 0<q^d := pow_pos hq d
  have hp1 : q^d<1 := pow_lt_one₀ hq.le hq1 hd.ne'
  have hg : H/W≤(G/V)/q^d := by
    rw [hW]
    calc
      _≤G/(q^d*V) := div_le_div_of_nonneg_right hG (mul_pos hp hV).le
      _=(G/V)/q^d := by field_simp
  have hh : (B-R)^d/q^d≤(B-S)^d := by
    rw [←div_pow]
    exact pow_le_pow_left₀ (div_nonneg (sub_nonneg.mpr hR) hq.le) hdef d
  have hm : H/W-(B-S)^d≤(G/V-(B-R)^d)/q^d := by
    rw [sub_div]
    linarith only [hg,hh]
  apply hm.trans_lt
  apply (div_lt_iff₀ hp).mpr
  nlinarith only [hneg,hp1]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem form_homothety (f : E →ᵃ[ℝ] ℝ) (z x : E) (q : ℝ) :
    f (AffineMap.homothety z q x)=f z+q*(f x-f z) := by
  change f (q • (x-z)+z)=_
  rw [add_comm,Body.map_add_smul_sub]

/-- Every directional width scales with the same contraction factor. -/
theorem width_homothety {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) (z : E) {q : ℝ} (hq : 0≤q) :
    Body.width (AffineMap.homothety z q '' K) f=q*Body.width K f := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne f.continuous_of_finiteDimensional
  rw [Body.width_eq_of_realisers ha hb hmax hmin,
    Body.width_eq_of_realisers (K := AffineMap.homothety z q '' K) (f := f)
      (a := AffineMap.homothety z q a)
      (b := AffineMap.homothety z q b) ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ ?_ ?_]
  · rw [form_homothety,form_homothety]; ring
  · rintro _ ⟨x,hx,rfl⟩
    rw [form_homothety,form_homothety]
    nlinarith only [mul_le_mul_of_nonneg_left (hmax x hx) hq]
  · rintro _ ⟨x,hx,rfl⟩
    rw [form_homothety,form_homothety]
    nlinarith only [mul_le_mul_of_nonneg_left (hmin x hx) hq]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional ℝ E] in
/-- Collapsing one window inside a homothet removes its original relative
width before dividing the remaining budget by the contraction factor. -/
theorem budget_collapse {K C : Set E} (f : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (i : ι) {q : ℝ}
    (hscale : ∀ j, Body.width C (f j)=q*Body.width K (f j)) :
    budget C f (Function.update lo i (hi i)) hi=
      (budget K f lo hi-(hi i-lo i)/Body.width K (f i))/q := by
  classical
  let r : ι → ℝ := fun j => (hi j-lo j)/Body.width K (f j)
  have ht (j) : (hi j-Function.update lo i (hi i) j)/Body.width C (f j)=
      (if j=i then 0 else r j)/q := by
    rw [hscale j]
    by_cases he : j=i
    · subst j; simp
    · simp [he,r,div_mul_eq_div_div,div_right_comm]
  unfold budget
  simp_rw [ht]
  rw [←Finset.sum_div]
  congr 1
  have hs := Finset.sum_erase_add (Finset.univ : Finset ι) r (Finset.mem_univ i)
  have he : (∑ j : ι, if j=i then 0 else r j)=∑ j ∈ Finset.univ.erase i, r j := by
    simp [Finset.sum_ite,Finset.filter_ne']
  rw [he]
  change (∑ j ∈ Finset.univ.erase i, r j)=(∑ j, r j)-r i
  linarith only [hs]

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Positive-volume homothets carry exactly the ambient-dimensional power. -/
theorem volume_homothety (z : E) {q : ℝ} (hq : 0≤q) (K : Set E) :
    μ.real (AffineMap.homothety z q '' K)=q^(Module.finrank ℝ E)*μ.real K := by
  simp only [Measure.real,Measure.addHaar_image_homothety,ENNReal.toReal_mul,
    abs_of_nonneg (pow_nonneg hq _),ENNReal.toReal_ofReal (pow_nonneg hq _)]

omit [DecidableEq ι] in
/-- At a negative all-body minimum, no positive-width plank can begin at or
below the lower support level. The exponent is the ambient dimension.
The competitor keeps the index type and collapses this one window. -/
theorem no_lower_support (hd : 0<Module.finrank ℝ E)
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ j, lo j≤hi j) (hW : ∀ j, 0<Body.width K (f j))
    {B : ℝ} (hB : B≤1) (hbudget : budget K f lo hi≤B)
    (hneg : margin μ K f lo hi (Module.finrank ℝ E) B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi (Module.finrank ℝ E) B)
    (i : ι) (hpos : lo i<hi i) (hlower : ∀ x∈K, lo i≤f i x) : False := by
  classical
  let R := budget K f lo hi
  let r := (hi i-lo i)/Body.width K (f i)
  have hr : 0<r := div_pos (sub_pos.mpr hpos) (hW i)
  have hrR : r≤R := Finset.single_le_sum
    (fun j _ => div_nonneg (sub_nonneg.mpr (horder j)) (hW j).le) (Finset.mem_univ i)
  have hRB : R<B := by
    by_contra! hn
    have he : B-R=0 := sub_eq_zero.mpr (le_antisymm hn hbudget)
    have hh : μ.real (K\covered f lo hi)/μ.real K<0 := by
      simpa only [margin,show budget K f lo hi=R from rfl,he,
        zero_pow hd.ne',sub_zero] using hneg
    exact (not_lt_of_ge (div_nonneg measureReal_nonneg hV.le)) hh
  let q := 1-r
  have hq : 0<q := sub_pos.mpr (hrR.trans_lt (hRB.trans_le hB))
  have hq1 : q<1 := by dsimp [q]; linarith only [hr]
  have hne : K.Nonempty := by
    by_contra hn
    simp [not_nonempty_iff_eq_empty.mp hn,Measure.real] at hV
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (f i).continuous_of_finiteDimensional
  have hpaid : r*(f i a-f i b)=hi i-lo i := by
    rw [←Body.width_eq_of_realisers ha hb hmax hmin]
    exact div_mul_cancel₀ _ (hW i).ne'
  let C := AffineMap.homothety a q '' K
  have hCK : C⊆K := by
    rintro _ ⟨x,hx,rfl⟩
    change q • (x-a)+a∈K
    rw [add_comm]
    exact hc.add_smul_sub_mem ha hx ⟨hq.le,hq1.le⟩
  have hC : IsCompact C := hK.image (AffineMap.homothety_continuous a q)
  have hCc : Convex ℝ C := hc.affine_image _
  have hscale (j) : Body.width C (f j)=q*Body.width K (f j) :=
    width_homothety hK hne (f j) a hq.le
  have hCW (j) : 0<Body.width C (f j) := by rw [hscale]; exact mul_pos hq (hW j)
  have hCV : μ.real C=q^(Module.finrank ℝ E)*μ.real K := volume_homothety μ a hq.le K
  have hCVpos : 0<μ.real C := by rw [hCV]; exact mul_pos (pow_pos hq _) hV
  have hbeyond : ∀ x∈C, hi i≤f i x := by
    rintro _ ⟨x,hx,rfl⟩
    rw [form_homothety]
    have hh := mul_le_mul_of_nonneg_left (hmin x hx) hq.le
    have hl := hlower b hb
    dsimp only [q] at hh ⊢
    nlinarith only [hpaid,hh,hl]
  let lo' := Function.update lo i (hi i)
  have ho (j) : lo' j≤hi j := by
    by_cases he : j=i
    · subst j; simp [lo']
    · simpa [lo',he] using horder j
  have hbud : budget C f lo' hi=(R-r)/q := budget_collapse f lo hi i hscale
  have hnew : budget C f lo' hi≤B := by
    rw [hbud]
    apply (div_le_iff₀ hq).mpr
    dsimp [q]
    have hR1 : R≤1 := hbudget.trans hB
    nlinarith only [hbudget,hr.le,hB,hR1]
  have hdef : (B-R)/q≤B-budget C f lo' hi := by
    rw [hbud,le_sub_iff_add_le,←add_div,div_le_iff₀ hq]
    dsimp [q]
    nlinarith only [hr.le,hB]
  have hgap : C\covered f lo' hi⊆K\covered f lo hi := by
    rintro x ⟨hx,hout⟩
    refine ⟨hCK hx,?_⟩
    intro hin
    apply hout
    obtain ⟨j,hj⟩ := mem_iUnion.mp hin
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    by_cases he : j=i
    · subst j
      exact ⟨by simpa [lo'] using hbeyond x hx,hj.2⟩
    · simpa [lo',he] using hj
  have hle := measureReal_mono (μ := μ) hgap
    (measure_ne_top_of_subset sdiff_subset hK.measure_ne_top)
  have hlt := contraction_margin_lt hd hq hq1 hV hCV hle hbudget hdef hneg
  exact (not_lt_of_ge (hglobal C f lo' hi hC hCc hCVpos hCW ho hnew)) hlt

omit [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] in
theorem budget_reverse {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    budget K (fun j => -f j) (fun j => -hi j) (fun j => -lo j)=budget K f lo hi := by
  unfold budget
  apply Finset.sum_congr rfl
  intro j _
  rw [Body.width_neg hK hne (f j).continuous_of_finiteDimensional]
  congr 1
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DecidableEq ι] [Fintype ι] in
theorem covered_reverse (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    covered (fun j => -f j) (fun j => -hi j) (fun j => -lo j)=covered f lo hi := by
  ext x
  simp only [covered,mem_iUnion,mem_ofPred_eq,AffineMap.coe_neg,Pi.neg_apply,neg_le_neg_iff,and_comm]

omit [BorelSpace E] [μ.IsAddHaarMeasure] [DecidableEq ι] in
theorem margin_reverse {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (d : ℕ) (B : ℝ) :
    margin μ K (fun j => -f j) (fun j => -hi j) (fun j => -lo j) d B=
      margin μ K f lo hi d B := by
  rw [margin,margin,covered_reverse,budget_reverse hK hne]

omit [BorelSpace E] [μ.IsAddHaarMeasure] [DecidableEq ι] in
theorem global_minimum_reverse {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (d : ℕ) (B : ℝ)
    (hm : IsGlobalMinimum μ K f lo hi d B) :
    IsGlobalMinimum μ K (fun j => -f j) (fun j => -hi j) (fun j => -lo j) d B := by
  intro C g a b hC hCc hCV hCW ho hbudget
  rw [margin_reverse μ hK hne]
  exact hm C g a b hC hCc hCV hCW ho hbudget

omit [DecidableEq ι] in
/-- The upper-support exclusion follows by reversing all physical forms.
Neither endpoint exclusion invokes a bound for fewer planks. -/
theorem no_upper_support (hd : 0<Module.finrank ℝ E)
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ j, lo j≤hi j) (hW : ∀ j, 0<Body.width K (f j))
    {B : ℝ} (hB : B≤1) (hbudget : budget K f lo hi≤B)
    (hneg : margin μ K f lo hi (Module.finrank ℝ E) B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi (Module.finrank ℝ E) B)
    (i : ι) (hpos : lo i<hi i) (hupper : ∀ x∈K, f i x≤hi i) : False := by
  have hne : K.Nonempty := by
    by_contra hn
    simp [not_nonempty_iff_eq_empty.mp hn,Measure.real] at hV
  apply no_lower_support μ hd hK hc hV (fun j => -f j) (fun j => -hi j)
    (fun j => -lo j) (fun j => neg_le_neg (horder j))
    (fun j => by rw [Body.width_neg hK hne (f j).continuous_of_finiteDimensional]; exact hW j)
    hB (by rwa [budget_reverse hK hne]) (by rwa [margin_reverse μ hK hne])
    (global_minimum_reverse μ hK hne f lo hi _ B hglobal) i (neg_lt_neg hpos)
  intro x hx
  simpa only [AffineMap.coe_neg,Pi.neg_apply] using neg_le_neg (hupper x hx)

omit [DecidableEq ι] in
/-- Every positive-width window at a negative all-body minimum cuts strictly
inside the body's range. Zero-width windows are allowed and not constrained. -/
theorem active_window_interior (hd : 0<Module.finrank ℝ E)
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ j, lo j≤hi j) (hW : ∀ j, 0<Body.width K (f j))
    {B : ℝ} (hB : B≤1) (hbudget : budget K f lo hi≤B)
    (hneg : margin μ K f lo hi (Module.finrank ℝ E) B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi (Module.finrank ℝ E) B)
    (i : ι) (hpos : lo i<hi i) :
    (∃ x∈K, f i x<lo i) ∧ (∃ y∈K, hi i<f i y) := by
  constructor
  · by_contra! h
    exact no_lower_support μ hd hK hc hV f lo hi horder hW hB hbudget hneg hglobal i hpos h
  · by_contra! h
    exact no_upper_support μ hd hK hc hV f lo hi horder hW hB hbudget hneg hglobal i hpos h

end Plank.GlobalPlankBoundaryMinimum

