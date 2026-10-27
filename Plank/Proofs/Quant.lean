module
/-
# Proofs/Quant — the measure-theoretic input to the ledger

Mirror of `Plank/Quant.lean`.  Guard G2 keeps this file from naming the
topic file's definitions (`Quant.capArea`, `Quant.dDef`, …), so the
content is stated over `Plank.Core` vocabulary only and the topic file
does the (purely algebraic) bookkeeping on top of it:

§1 the standard triangle in coordinates, and measurability of triangles
   and planks;
§2 its area is `1/2`, by Fubini over the vertical slices;
§3 three-set inclusion–exclusion inside the triangle, in real-valued
   form — the exact identity that funds `Quant.ledger`.
-/
public import Plank.Proofs.GapCells
public import Plank.Proofs.Symmetry
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section


public section

noncomputable section

open Proofs.Basic Proofs.Transport Proofs.GapCells MeasureTheory

namespace Proofs.Quant

/-! ## §1  The triangle in coordinates -/

/-- The standard triangle is the coordinate region `x, y ≥ 0`,
`x + y ≤ 1`. -/
theorem stdTriangle_set_eq :
    stdTriangle.set = {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1} := by
  ext ⟨x, y⟩
  simp only [Triangle.set, Set.mem_setOf_eq, Membership.mem, stdTriangle, Prod.ext_iff,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, hx, hy⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨1 - x - y, x, y, by linarith, hx, hy, by ring, by ring, by ring⟩

/-- Membership in a plank, in coordinates. -/
theorem plank_set_eq (p : Plank) :
    p.set = {P : ℝ × ℝ | p.lo ≤ dot p.u P ∧ dot p.u P ≤ p.hi} := rfl

theorem isClosed_stdTriangle_set : IsClosed stdTriangle.set := by
  rw [stdTriangle_set_eq]
  have h : {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
      = {p : ℝ × ℝ | 0 ≤ p.1} ∩ ({p : ℝ × ℝ | 0 ≤ p.2} ∩ {p : ℝ × ℝ | p.1 + p.2 ≤ 1}) := rfl
  rw [h]
  refine (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (by fun_prop) continuous_const))

theorem measurableSet_stdTriangle : MeasurableSet stdTriangle.set :=
  isClosed_stdTriangle_set.measurableSet

theorem isClosed_plank_set (p : Plank) : IsClosed p.set := by
  rw [plank_set_eq]
  have h : {P : ℝ × ℝ | p.lo ≤ dot p.u P ∧ dot p.u P ≤ p.hi}
      = {P : ℝ × ℝ | p.lo ≤ dot p.u P} ∩ {P : ℝ × ℝ | dot p.u P ≤ p.hi} := rfl
  rw [h]
  exact (isClosed_le continuous_const (continuous_dot p.u)).inter
    (isClosed_le (continuous_dot p.u) continuous_const)

theorem measurableSet_plank (p : Plank) : MeasurableSet p.set :=
  (isClosed_plank_set p).measurableSet

/-! ## §2  The area of the standard triangle -/

/-- **The triangle has area `1/2`**, by Fubini: the slice over `x` is the
segment `[0, 1 − x]`, of length `(1 − x)₊`. -/
theorem volume_stdTriangle : volume stdTriangle.set = ENNReal.ofReal (1 / 2) := by
  rw [stdTriangle_set_eq, Measure.volume_eq_prod,
    Measure.prod_apply (by rw [← stdTriangle_set_eq]; exact measurableSet_stdTriangle)]
  -- the vertical slice at `x` is `[0, 1 − x]`, empty once `x` leaves `[0,1]`
  have hslice : ∀ x : ℝ,
      (volume (Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}))
        = Set.indicator (Set.Icc (0:ℝ) 1) (fun t => ENNReal.ofReal (1 - t)) x := by
    intro x
    rcases lt_or_ge x 0 with hx | hx
    · have he : (Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}) = ∅ := by
        ext y; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h; linarith
      have hnot : x ∉ Set.Icc (0:ℝ) 1 := by
        simp only [Set.mem_Icc, not_and, not_le]
        intro h; linarith
      rw [he, measure_empty, Set.indicator_of_notMem hnot]
    · have he : (Prod.mk x ⁻¹' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1})
          = Set.Icc 0 (1 - x) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
        constructor
        · rintro ⟨-, h1, h2⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h2⟩; exact ⟨hx, h1, by linarith⟩
      rw [he, Real.volume_Icc]
      rcases le_or_gt x 1 with hx1 | hx1
      · rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨hx, hx1⟩)]; norm_num
      · have hnot : x ∉ Set.Icc (0:ℝ) 1 := by
          simp only [Set.mem_Icc, not_and, not_le]
          intro _; linarith
        rw [Set.indicator_of_notMem hnot, sub_zero]
        exact ENNReal.ofReal_eq_zero.mpr (by linarith)
  simp only [hslice]
  rw [lintegral_indicator measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous fun t : ℝ => 1 - t).integrableOn_Icc (a := 0) (b := 1))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        simp only [Pi.zero_apply]
        have := ht.2
        linarith)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id]
  norm_num

/-! ## §3  Inclusion–exclusion inside the triangle -/

/-- Anything cut out of a finite set has finite area. -/
theorem volume_ne_top_of_subset {S T : Set (ℝ × ℝ)} (hT : volume T ≠ ⊤) (h : S ⊆ T) :
    volume S ≠ ⊤ := ne_top_of_le_ne_top hT (measure_mono h)

/-- Every cap of the triangle has finite area. -/
theorem volume_cap_ne_top (S : Set (ℝ × ℝ)) : volume (S ∩ stdTriangle.set) ≠ ⊤ := by
  refine volume_ne_top_of_subset ?_ Set.inter_subset_right
  rw [volume_stdTriangle]; exact ENNReal.ofReal_ne_top

/-- **Inclusion–exclusion for three sets of finite area**, in
real-valued form (where the alternating signs are honest subtraction). -/
theorem measureReal_union_three {S₀ S₁ S₂ : Set (ℝ × ℝ)}
    (h₁ : MeasurableSet S₁) (h₂ : MeasurableSet S₂)
    (f₀ : volume S₀ ≠ ⊤) (f₁ : volume S₁ ≠ ⊤) (f₂ : volume S₂ ≠ ⊤) :
    (volume (S₀ ∪ S₁ ∪ S₂)).toReal
      = (volume S₀).toReal + (volume S₁).toReal + (volume S₂).toReal
        - (volume (S₀ ∩ S₁)).toReal - (volume (S₀ ∩ S₂)).toReal - (volume (S₁ ∩ S₂)).toReal
        + (volume (S₀ ∩ S₁ ∩ S₂)).toReal := by
  have fu01 : volume (S₀ ∪ S₁) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨f₀, f₁⟩) (measure_union_le S₀ S₁)
  have fu : volume (S₀ ∪ S₁ ∪ S₂) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨fu01, f₂⟩) (measure_union_le _ S₂)
  have fi01 : volume (S₀ ∩ S₁) ≠ ⊤ := volume_ne_top_of_subset f₀ Set.inter_subset_left
  have fi02 : volume (S₀ ∩ S₂) ≠ ⊤ := volume_ne_top_of_subset f₀ Set.inter_subset_left
  have fi12 : volume (S₁ ∩ S₂) ≠ ⊤ := volume_ne_top_of_subset f₁ Set.inter_subset_left
  have fi012 : volume (S₀ ∩ S₁ ∩ S₂) ≠ ⊤ :=
    volume_ne_top_of_subset fi01 Set.inter_subset_left
  have fm : volume ((S₀ ∪ S₁) ∩ S₂) ≠ ⊤ := volume_ne_top_of_subset f₂ Set.inter_subset_right
  -- the two-set law, three times
  have e1 : volume (S₀ ∪ S₁) + volume (S₀ ∩ S₁) = volume S₀ + volume S₁ :=
    measure_union_add_inter S₀ h₁
  have e2 : volume (S₀ ∪ S₁ ∪ S₂) + volume ((S₀ ∪ S₁) ∩ S₂)
      = volume (S₀ ∪ S₁) + volume S₂ := measure_union_add_inter (S₀ ∪ S₁) h₂
  have e3 : volume (S₀ ∩ S₂ ∪ S₁ ∩ S₂) + volume (S₀ ∩ S₂ ∩ (S₁ ∩ S₂))
      = volume (S₀ ∩ S₂) + volume (S₁ ∩ S₂) := measure_union_add_inter _ (h₁.inter h₂)
  have hd : (S₀ ∪ S₁) ∩ S₂ = S₀ ∩ S₂ ∪ S₁ ∩ S₂ := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_union]; tauto
  have hi : S₀ ∩ S₂ ∩ (S₁ ∩ S₂) = S₀ ∩ S₁ ∩ S₂ := by
    ext x; simp only [Set.mem_inter_iff]; tauto
  rw [hd] at e2
  rw [hd] at fm
  rw [hi] at e3
  have t1 := congrArg ENNReal.toReal e1
  have t2 := congrArg ENNReal.toReal e2
  have t3 := congrArg ENNReal.toReal e3
  rw [ENNReal.toReal_add fu01 fi01, ENNReal.toReal_add f₀ f₁] at t1
  rw [ENNReal.toReal_add fu fm, ENNReal.toReal_add fu01 f₂] at t2
  rw [ENNReal.toReal_add fm fi012, ENNReal.toReal_add fi02 fi12] at t3
  linarith

/-- **The gap ledger's measure-theoretic core**: the uncovered area of
the triangle, by inclusion–exclusion over the three planks. -/
theorem gap_inclusion_exclusion (C : Config) :
    (volume (stdTriangle.set \ ⋃ i, (C.plank i).set)).toReal
      = 1 / 2
        - ((volume ((C.plank 0).set ∩ stdTriangle.set)).toReal
          + (volume ((C.plank 1).set ∩ stdTriangle.set)).toReal
          + (volume ((C.plank 2).set ∩ stdTriangle.set)).toReal)
        + ((volume ((C.plank 0).set ∩ (C.plank 1).set ∩ stdTriangle.set)).toReal
          + (volume ((C.plank 0).set ∩ (C.plank 2).set ∩ stdTriangle.set)).toReal
          + (volume ((C.plank 1).set ∩ (C.plank 2).set ∩ stdTriangle.set)).toReal)
        - (volume ((C.plank 0).set ∩ (C.plank 1).set ∩ (C.plank 2).set
            ∩ stdTriangle.set)).toReal := by
  have hTfin : volume stdTriangle.set ≠ ⊤ := by
    rw [volume_stdTriangle]; exact ENNReal.ofReal_ne_top
  have hTre : (volume stdTriangle.set).toReal = 1 / 2 := by
    rw [volume_stdTriangle, ENNReal.toReal_ofReal (by norm_num)]
  -- the union of three planks, spelled out
  have hU : (⋃ i, (C.plank i).set)
      = (C.plank 0).set ∪ (C.plank 1).set ∪ (C.plank 2).set := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;> subst h
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  -- the covered part, sorted into the three caps
  have hcov : stdTriangle.set ∩ (⋃ i, (C.plank i).set)
      = ((C.plank 0).set ∩ stdTriangle.set) ∪ ((C.plank 1).set ∩ stdTriangle.set)
        ∪ ((C.plank 2).set ∩ stdTriangle.set) := by
    rw [hU]; ext x; simp only [Set.mem_inter_iff, Set.mem_union]; tauto
  have hmeas : MeasurableSet (⋃ i, (C.plank i).set) :=
    MeasurableSet.iUnion fun i => measurableSet_plank _
  have hsplit := measure_diff_add_inter stdTriangle.set hmeas (μ := volume)
  rw [hcov] at hsplit
  have fdiff : volume (stdTriangle.set \ ⋃ i, (C.plank i).set) ≠ ⊤ :=
    volume_ne_top_of_subset hTfin Set.diff_subset
  have fcap : ∀ i : Fin 3, volume ((C.plank i).set ∩ stdTriangle.set) ≠ ⊤ := fun i =>
    volume_ne_top_of_subset hTfin Set.inter_subset_right
  have fun3 : volume (((C.plank 0).set ∩ stdTriangle.set) ∪ ((C.plank 1).set ∩ stdTriangle.set)
      ∪ ((C.plank 2).set ∩ stdTriangle.set)) ≠ ⊤ :=
    volume_ne_top_of_subset hTfin (by
      rintro x ((hx | hx) | hx) <;> exact hx.2)
  have ts := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_add fdiff fun3] at ts
  -- inclusion–exclusion on the three caps
  have hie := measureReal_union_three (S₀ := (C.plank 0).set ∩ stdTriangle.set)
    (S₁ := (C.plank 1).set ∩ stdTriangle.set) (S₂ := (C.plank 2).set ∩ stdTriangle.set)
    ((measurableSet_plank _).inter measurableSet_stdTriangle)
    ((measurableSet_plank _).inter measurableSet_stdTriangle)
    (fcap 0) (fcap 1) (fcap 2)
  -- the pair and triple intersections of caps are the caps of intersections
  have p01 : ((C.plank 0).set ∩ stdTriangle.set) ∩ ((C.plank 1).set ∩ stdTriangle.set)
      = (C.plank 0).set ∩ (C.plank 1).set ∩ stdTriangle.set := by
    ext x; simp only [Set.mem_inter_iff]; tauto
  have p02 : ((C.plank 0).set ∩ stdTriangle.set) ∩ ((C.plank 2).set ∩ stdTriangle.set)
      = (C.plank 0).set ∩ (C.plank 2).set ∩ stdTriangle.set := by
    ext x; simp only [Set.mem_inter_iff]; tauto
  have p12 : ((C.plank 1).set ∩ stdTriangle.set) ∩ ((C.plank 2).set ∩ stdTriangle.set)
      = (C.plank 1).set ∩ (C.plank 2).set ∩ stdTriangle.set := by
    ext x; simp only [Set.mem_inter_iff]; tauto
  -- (`p01` has already fired inside the triple term)
  have p012 : ((C.plank 0).set ∩ (C.plank 1).set ∩ stdTriangle.set)
      ∩ ((C.plank 2).set ∩ stdTriangle.set)
      = (C.plank 0).set ∩ (C.plank 1).set ∩ (C.plank 2).set ∩ stdTriangle.set := by
    ext x; simp only [Set.mem_inter_iff]; tauto
  rw [p01, p02, p12, p012] at hie
  rw [hTre] at ts
  linarith

/-! ## §4  The CAL-δ stacking and its gap

The attainment witness for the equality chapter, ported from the
ancestor's `KPlankAttain` (the `(SM-ATTAIN)` package).  Three strips
with slope-sorted normals `(1, −cⱼ)`, `0 ≤ c₀ ≤ c₁ ≤ c₂`, each carrying
relative width `wⱼ`, placed at the *calibrated* levels `lev`: strip `j`
starts at normalised height `W_{<j} + δ·m(cⱼ)`, where `m(c) = c/(1+c)`
is where the shared vertex `(0,0)` sits in the strip functional's range
over the triangle.  Sweeping along `x + y = σ` turns the whole
configuration into three intervals on a segment: below `σ = t` they
overlap and cover, above it they are disjoint and leave exactly `σ − t`
free.  Integrating that ramp gives `δ²/2`. -/

/-! ### The one-dimensional core -/

/-- Three consecutive closed intervals have total length the sum of
their lengths: they overlap in at most two points. -/
theorem volume_union_three_Icc {p₁ q₁ p₂ q₂ p₃ q₃ : ℝ}
    (h1 : p₁ ≤ q₁) (h2 : q₁ ≤ p₂) (h3 : p₂ ≤ q₂) (h4 : q₂ ≤ p₃) (h5 : p₃ ≤ q₃) :
    volume (Set.Icc p₁ q₁ ∪ Set.Icc p₂ q₂ ∪ Set.Icc p₃ q₃)
      = ENNReal.ofReal ((q₁ - p₁) + (q₂ - p₂) + (q₃ - p₃)) := by
  have hs12 : Set.Icc p₁ q₁ ∩ Set.Icc p₂ q₂ ⊆ Set.Icc p₂ q₁ := fun x hx => ⟨hx.2.1, hx.1.2⟩
  have hs3 : (Set.Icc p₁ q₁ ∪ Set.Icc p₂ q₂) ∩ Set.Icc p₃ q₃ ⊆ Set.Icc p₃ q₂ := by
    rintro x ⟨h | h, hx3⟩
    · exact ⟨hx3.1, by linarith [h.2]⟩
    · exact ⟨hx3.1, h.2⟩
  have hz1 : volume (Set.Icc p₂ q₁) = 0 := by
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
  have hz2 : volume (Set.Icc p₃ q₂) = 0 := by
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
  have hd12 : volume (Set.Icc p₁ q₁ ∩ Set.Icc p₂ q₂) = 0 := measure_mono_null hs12 hz1
  have hd3 : volume ((Set.Icc p₁ q₁ ∪ Set.Icc p₂ q₂) ∩ Set.Icc p₃ q₃) = 0 :=
    measure_mono_null hs3 hz2
  rw [measure_union₀ measurableSet_Icc.nullMeasurableSet hd3,
    measure_union₀ measurableSet_Icc.nullMeasurableSet hd12,
    Real.volume_Icc, Real.volume_Icc, Real.volume_Icc,
    ← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith)]

/-- **The free length**: three disjoint closed intervals inside `[0,L]`
leave `L` minus their total length free. -/
theorem volume_Icc_sdiff_three {L p₁ q₁ p₂ q₂ p₃ q₃ : ℝ}
    (h0 : 0 ≤ p₁) (h1 : p₁ ≤ q₁) (h2 : q₁ ≤ p₂) (h3 : p₂ ≤ q₂)
    (h4 : q₂ ≤ p₃) (h5 : p₃ ≤ q₃) (h6 : q₃ ≤ L) :
    volume (Set.Icc (0:ℝ) L \ (Set.Icc p₁ q₁ ∪ Set.Icc p₂ q₂ ∪ Set.Icc p₃ q₃))
      = ENNReal.ofReal (L - ((q₁ - p₁) + (q₂ - p₂) + (q₃ - p₃))) := by
  have hsub : (Set.Icc p₁ q₁ ∪ Set.Icc p₂ q₂ ∪ Set.Icc p₃ q₃) ⊆ Set.Icc (0:ℝ) L := by
    rintro x ((hx | hx) | hx) <;> exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hU := volume_union_three_Icc h1 h2 h3 h4 h5
  have hmeas : NullMeasurableSet (Set.Icc p₁ q₁ ∪ Set.Icc p₂ q₂ ∪ Set.Icc p₃ q₃) volume :=
    ((measurableSet_Icc.union measurableSet_Icc).union measurableSet_Icc).nullMeasurableSet
  rw [measure_diff hsub hmeas (by rw [hU]; exact ENNReal.ofReal_ne_top), hU,
    Real.volume_Icc, sub_zero, ← ENNReal.ofReal_sub _ (by linarith)]

/-- **The covering branch**: when the intervals overlap and reach past
both ends they cover `[0,L]`. -/
theorem Icc_subset_union_three {L p₁ q₁ p₂ q₂ p₃ q₃ : ℝ}
    (h0 : p₁ ≤ 0) (h1 : p₂ ≤ q₁) (h2 : p₃ ≤ q₂) (h3 : L ≤ q₃) :
    Set.Icc (0:ℝ) L ⊆ Set.Icc p₁ q₁ ∪ Set.Icc p₂ q₂ ∪ Set.Icc p₃ q₃ := by
  rintro x ⟨hx0, hxL⟩
  rcases le_or_gt x q₁ with h | h
  · exact Or.inl (Or.inl ⟨by linarith, h⟩)
  rcases le_or_gt x q₂ with h' | h'
  · exact Or.inl (Or.inr ⟨by linarith, h'⟩)
  · exact Or.inr ⟨by linarith, by linarith⟩

/-! ### The calibrated levels -/

/-- `m(c) = c/(1+c)`: where the shared vertex `(0,0)` sits in the
normalised range of `dot (1,−c)` over the triangle. -/
def mm (c : ℝ) : ℝ := c / (1 + c)

/-- The raw face level of the strip with normal `(1,−c)`, prefix mass
`W` and total mass `t` — the normalised level `W + δ·m(c)` read back
through `dot (1,−c)`. -/
def lev (c W t : ℝ) : ℝ := W * (1 + c) - c * t

theorem mm_mul {c : ℝ} (hc : 0 ≤ c) : mm c * (1 + c) = c := by
  have h : (1:ℝ) + c ≠ 0 := by positivity
  rw [mm]; field_simp

theorem mm_nonneg {c : ℝ} (hc : 0 ≤ c) : 0 ≤ mm c :=
  div_nonneg hc (by linarith)

theorem mm_le_one {c : ℝ} (hc : 0 ≤ c) : mm c ≤ 1 := by
  rw [mm, div_le_one (by linarith)]; linarith

theorem mm_mono {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) : mm c ≤ mm d := by
  rw [mm, mm, div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith

theorem lev_le_lev {c : ℝ} (hc : 0 ≤ c) {w : ℝ} (hw : 0 ≤ w) (W t : ℝ) :
    lev c W t ≤ lev c (W + w) t := by unfold lev; nlinarith

/-- The triangle's width along a slope-sorted normal. -/
theorem width_dir {c : ℝ} (hc : 0 ≤ c) : stdTriangle.width (1, -c) = 1 + c := by
  simp only [Triangle.width, stdTriangle, dot]
  rw [show (1:ℝ) * 0 + -c * 0 = 0 by ring, show (1:ℝ) * 1 + -c * 0 = 1 by ring,
    show (1:ℝ) * 0 + -c * 1 = -c by ring,
    max_eq_left (by linarith : (-c : ℝ) ≤ 1),
    max_eq_right (by norm_num : (0:ℝ) ≤ 1),
    min_eq_right (by linarith : (-c : ℝ) ≤ 1),
    min_eq_right (by linarith : (-c : ℝ) ≤ 0)]
  ring

/-! ### The stacking and its sweep -/

/-- The strip with normal `(1,−c)` between two raw levels. -/
def slab (c lo hi : ℝ) : Set (ℝ × ℝ) :=
  {P : ℝ × ℝ | lo ≤ dot (1, -c) P ∧ dot (1, -c) P ≤ hi}

theorem measurableSet_slab (c lo hi : ℝ) : MeasurableSet (slab c lo hi) := by
  have h : slab c lo hi = {P : ℝ × ℝ | lo ≤ dot (1, -c) P}
      ∩ {P : ℝ × ℝ | dot (1, -c) P ≤ hi} := rfl
  rw [h]
  exact ((isClosed_le continuous_const (continuous_dot _)).inter
    (isClosed_le (continuous_dot _) continuous_const)).measurableSet

/-- **The slice of a strip**: on the line `x + y = σ`, parametrised by
`u = x`, the calibrated strip is the interval
`[W + m(c)(σ−t), W + w + m(c)(σ−t)]`. -/
theorem mem_slab_iff {c : ℝ} (hc : 0 ≤ c) (W w t σ u : ℝ) :
    (u, σ - u) ∈ slab c (lev c W t) (lev c (W + w) t)
      ↔ u ∈ Set.Icc (W + mm c * (σ - t)) (W + w + mm c * (σ - t)) := by
  have h1c : (0:ℝ) < 1 + c := by linarith
  have hk : mm c * (σ - t) * (1 + c) = c * (σ - t) := by
    rw [mul_right_comm, mm_mul hc]
  simp only [slab, dot, Set.mem_setOf_eq, Set.mem_Icc, lev]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨by nlinarith [ha, hk, h1c], by nlinarith [hb, hk, h1c]⟩
  · rintro ⟨ha, hb⟩
    exact ⟨by nlinarith [mul_le_mul_of_nonneg_right ha h1c.le, hk],
      by nlinarith [mul_le_mul_of_nonneg_right hb h1c.le, hk]⟩

/-- The three-strip **CAL-δ stacking**. -/
def stack (c₀ c₁ c₂ w₀ w₁ w₂ : ℝ) : Set (ℝ × ℝ) :=
  slab c₀ (lev c₀ 0 (w₀ + w₁ + w₂)) (lev c₀ (0 + w₀) (w₀ + w₁ + w₂))
    ∪ slab c₁ (lev c₁ w₀ (w₀ + w₁ + w₂)) (lev c₁ (w₀ + w₁) (w₀ + w₁ + w₂))
    ∪ slab c₂ (lev c₂ (w₀ + w₁) (w₀ + w₁ + w₂))
        (lev c₂ (w₀ + w₁ + w₂) (w₀ + w₁ + w₂))

theorem measurableSet_stack (c₀ c₁ c₂ w₀ w₁ w₂ : ℝ) :
    MeasurableSet (stack c₀ c₁ c₂ w₀ w₁ w₂) :=
  ((measurableSet_slab _ _ _).union (measurableSet_slab _ _ _)).union
    (measurableSet_slab _ _ _)

/-- The gap set of the stacking. -/
def gapS (c₀ c₁ c₂ w₀ w₁ w₂ : ℝ) : Set (ℝ × ℝ) :=
  stdTriangle.set \ stack c₀ c₁ c₂ w₀ w₁ w₂

theorem measurableSet_gapS (c₀ c₁ c₂ w₀ w₁ w₂ : ℝ) :
    MeasurableSet (gapS c₀ c₁ c₂ w₀ w₁ w₂) :=
  measurableSet_stdTriangle.diff (measurableSet_stack _ _ _ _ _ _)

/-- The shear chart `(σ,u) ↦ (u, σ−u)`: first coordinate the sweep level
`x + y`, second the abscissa.  `|det| = 1`. -/
def shear : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (z.2, z.1 - z.2)
  map_add' z z' := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨trivial, by ring⟩
  map_smul' r z := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply,
      Prod.smul_mk, Prod.mk.injEq]
    exact ⟨trivial, by ring⟩

theorem det_shear : LinearMap.det shear = -1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, shear, Module.Basis.finTwoProd]

theorem volume_preimage_shear (A : Set (ℝ × ℝ)) :
    volume (⇑shear ⁻¹' A) = volume A := by
  rw [Measure.addHaar_preimage_linearMap volume (by rw [det_shear]; norm_num),
    det_shear]
  norm_num

/-- **The sweep identity**: the shear is unimodular, so Fubini along
`x + y` costs no Jacobian. -/
theorem volume_eq_lintegral_slice {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    volume A = ∫⁻ σ, volume {u : ℝ | (u, σ - u) ∈ A} := by
  have hm : MeasurableSet (⇑shear ⁻¹' A) :=
    hA.preimage (LinearMap.continuous_of_finiteDimensional shear).measurable
  rw [← volume_preimage_shear, Measure.volume_eq_prod, Measure.prod_apply hm]
  rfl

/-- **The sweep slice of the gap**: on `x + y = σ` with `σ ≤ 1`, the free
set is `[0,σ]` minus the three calibrated intervals. -/
theorem slice_eq {c₀ c₁ c₂ : ℝ} (h0 : 0 ≤ c₀) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂)
    (w₀ w₁ w₂ : ℝ) {σ : ℝ} (hσ : σ ≤ 1) :
    {u : ℝ | (u, σ - u) ∈ gapS c₀ c₁ c₂ w₀ w₁ w₂}
      = Set.Icc 0 σ \ (Set.Icc (0 + mm c₀ * (σ - (w₀ + w₁ + w₂)))
            (0 + w₀ + mm c₀ * (σ - (w₀ + w₁ + w₂)))
          ∪ Set.Icc (w₀ + mm c₁ * (σ - (w₀ + w₁ + w₂)))
            (w₀ + w₁ + mm c₁ * (σ - (w₀ + w₁ + w₂)))
          ∪ Set.Icc (w₀ + w₁ + mm c₂ * (σ - (w₀ + w₁ + w₂)))
            (w₀ + w₁ + w₂ + mm c₂ * (σ - (w₀ + w₁ + w₂)))) := by
  ext u
  have e0 := mem_slab_iff h0 0 w₀ (w₀ + w₁ + w₂) σ u
  have e1 := mem_slab_iff h1 w₀ w₁ (w₀ + w₁ + w₂) σ u
  have e2 := mem_slab_iff h2 (w₀ + w₁) w₂ (w₀ + w₁ + w₂) σ u
  simp only [gapS, stack, Set.mem_setOf_eq, Set.mem_diff, Set.mem_union,
    stdTriangle_set_eq, e0, e1, e2, Set.mem_Icc]
  constructor
  · rintro ⟨⟨ha, hb, -⟩, hd⟩
    exact ⟨⟨ha, by linarith⟩, hd⟩
  · rintro ⟨⟨ha, hb⟩, hd⟩
    exact ⟨⟨ha, by linarith, by linarith⟩, hd⟩

/-- Above the top vertex level the slice is empty. -/
theorem slice_empty (c₀ c₁ c₂ w₀ w₁ w₂ : ℝ) {σ : ℝ} (hσ : 1 < σ) :
    {u : ℝ | (u, σ - u) ∈ gapS c₀ c₁ c₂ w₀ w₁ w₂} = ∅ := by
  ext u
  simp only [gapS, Set.mem_setOf_eq, Set.mem_diff, stdTriangle_set_eq,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨-, -, hc⟩
  exact absurd (by linarith : σ ≤ 1) (not_le.mpr hσ)

/-- **The free profile**: the sweep profile of the gap is the ramp
`σ ↦ σ − t` supported on `[t, 1]`.  The three intervals are disjoint
above `t` and overlapping below it. -/
theorem volume_slice {c₀ c₁ c₂ : ℝ} (hc0 : 0 ≤ c₀) (hc01 : c₀ ≤ c₁)
    (hc12 : c₁ ≤ c₂) {w₀ w₁ w₂ : ℝ} (hw0 : 0 ≤ w₀) (hw1 : 0 ≤ w₁)
    (hw2 : 0 ≤ w₂) (σ : ℝ) :
    volume {u : ℝ | (u, σ - u) ∈ gapS c₀ c₁ c₂ w₀ w₁ w₂}
      = (Set.Icc (w₀ + w₁ + w₂) 1).indicator
          (fun s => ENNReal.ofReal (s - (w₀ + w₁ + w₂))) σ := by
  have hc1 : (0:ℝ) ≤ c₁ := le_trans hc0 hc01
  have hc2 : (0:ℝ) ≤ c₂ := le_trans hc1 hc12
  rcases lt_or_ge 1 σ with hσ | hσ
  · rw [slice_empty c₀ c₁ c₂ w₀ w₁ w₂ hσ, measure_empty,
      Set.indicator_of_notMem (by
        simp only [Set.mem_Icc, not_and, not_le]
        intro _; linarith)]
  rw [slice_eq hc0 hc1 hc2 w₀ w₁ w₂ hσ]
  set r := σ - (w₀ + w₁ + w₂) with hr
  rcases le_or_gt 0 r with hr0 | hr0
  · rw [volume_Icc_sdiff_three
      (by nlinarith [mm_nonneg hc0] : (0:ℝ) ≤ 0 + mm c₀ * r)
      (by linarith : 0 + mm c₀ * r ≤ 0 + w₀ + mm c₀ * r)
      (by nlinarith [mm_mono hc0 hc01] : 0 + w₀ + mm c₀ * r ≤ w₀ + mm c₁ * r)
      (by linarith : w₀ + mm c₁ * r ≤ w₀ + w₁ + mm c₁ * r)
      (by nlinarith [mm_mono hc1 hc12] : w₀ + w₁ + mm c₁ * r ≤ w₀ + w₁ + mm c₂ * r)
      (by linarith : w₀ + w₁ + mm c₂ * r ≤ w₀ + w₁ + w₂ + mm c₂ * r)
      (by nlinarith [mm_le_one hc2] : w₀ + w₁ + w₂ + mm c₂ * r ≤ σ),
      Set.indicator_of_mem (by exact ⟨by linarith, hσ⟩)]
    congr 1
    ring
  · rw [Set.diff_eq_empty.mpr (Icc_subset_union_three
        (by nlinarith [mm_nonneg hc0] : 0 + mm c₀ * r ≤ 0)
        (by nlinarith [mm_mono hc0 hc01] : w₀ + mm c₁ * r ≤ 0 + w₀ + mm c₀ * r)
        (by nlinarith [mm_mono hc1 hc12] :
          w₀ + w₁ + mm c₂ * r ≤ w₀ + w₁ + mm c₁ * r)
        (by nlinarith [mm_le_one hc2] : σ ≤ w₀ + w₁ + w₂ + mm c₂ * r)),
      measure_empty,
      Set.indicator_of_notMem (by
        simp only [Set.mem_Icc, not_and, not_le]
        intro h; linarith)]

/-- The ramp's integral. -/
theorem lintegral_ramp {t : ℝ} (ht1 : t ≤ 1) :
    ∫⁻ σ, (Set.Icc t 1).indicator (fun s => ENNReal.ofReal (s - t)) σ
      = ENNReal.ofReal ((1 - t) ^ 2 / 2) := by
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht1]
    congr 1
    rw [show (fun σ : ℝ => σ - t) = (fun σ : ℝ => (fun x : ℝ => x) (σ - t)) from rfl,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) t, integral_id]
    ring
  · exact ((by fun_prop : Continuous fun σ : ℝ => σ - t)).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have : (0:ℝ) ≤ x - t := by linarith [hx.1]
    simpa using this

/-- **The attainment identity**: at the CAL-δ levels the uncovered area
is exactly `δ²·|T| = (1−t)²/2`. -/
theorem volume_gapS {c₀ c₁ c₂ : ℝ} (hc0 : 0 ≤ c₀) (hc01 : c₀ ≤ c₁)
    (hc12 : c₁ ≤ c₂) {w₀ w₁ w₂ : ℝ} (hw0 : 0 ≤ w₀) (hw1 : 0 ≤ w₁)
    (hw2 : 0 ≤ w₂) (ht : w₀ + w₁ + w₂ ≤ 1) :
    volume (gapS c₀ c₁ c₂ w₀ w₁ w₂)
      = ENNReal.ofReal ((1 - (w₀ + w₁ + w₂)) ^ 2 / 2) := by
  rw [volume_eq_lintegral_slice (measurableSet_gapS _ _ _ _ _ _),
    lintegral_congr (volume_slice hc0 hc01 hc12 hw0 hw1 hw2), lintegral_ramp ht]

/-! ### The stacking as a configuration -/

/-- The stacked strip has relative width exactly `w`. -/
theorem relWidth_lev {c : ℝ} (hc : 0 ≤ c) (W w t : ℝ) :
    (lev c (W + w) t - lev c W t) / stdTriangle.width (1, -c) = w := by
  rw [width_dir hc, lev, lev]
  field_simp
  ring

/-- **The CAL-δ stacking as a `Config`**: three genuine planks, slope
sorted, at the calibrated levels. -/
def stackConfig (c₀ c₁ c₂ w₀ w₁ w₂ : ℝ) (h0 : 0 ≤ c₀) (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂)
    (k0 : 0 ≤ w₀) (k1 : 0 ≤ w₁) (k2 : 0 ≤ w₂) : Config :=
  ⟨![⟨(1, -c₀), lev c₀ 0 (w₀ + w₁ + w₂), lev c₀ (0 + w₀) (w₀ + w₁ + w₂),
        by simp [Prod.ext_iff], lev_le_lev h0 k0 _ _⟩,
     ⟨(1, -c₁), lev c₁ w₀ (w₀ + w₁ + w₂), lev c₁ (w₀ + w₁) (w₀ + w₁ + w₂),
        by simp [Prod.ext_iff], lev_le_lev h1 k1 _ _⟩,
     ⟨(1, -c₂), lev c₂ (w₀ + w₁) (w₀ + w₁ + w₂), lev c₂ (w₀ + w₁ + w₂) (w₀ + w₁ + w₂),
        by simp [Prod.ext_iff], lev_le_lev h2 k2 _ _⟩]⟩

variable {c₀ c₁ c₂ w₀ w₁ w₂ : ℝ} {h0 : 0 ≤ c₀} {h1 : 0 ≤ c₁} {h2 : 0 ≤ c₂}
  {k0 : 0 ≤ w₀} {k1 : 0 ≤ w₁} {k2 : 0 ≤ w₂}

theorem stackConfig_u (i : Fin 3) :
    ((stackConfig c₀ c₁ c₂ w₀ w₁ w₂ h0 h1 h2 k0 k1 k2).plank i).u
      = (1, -(![c₀, c₁, c₂] i)) := by
  rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;> subst h <;> rfl

theorem stackConfig_relW (i : Fin 3) :
    (stackConfig c₀ c₁ c₂ w₀ w₁ w₂ h0 h1 h2 k0 k1 k2).relW i = ![w₀, w₁, w₂] i := by
  rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;> subst h
  · exact relWidth_lev h0 0 w₀ _
  · exact relWidth_lev h1 w₀ w₁ _
  · exact relWidth_lev h2 (w₀ + w₁) w₂ _

theorem stackConfig_uncovered :
    (stackConfig c₀ c₁ c₂ w₀ w₁ w₂ h0 h1 h2 k0 k1 k2).uncovered
      = gapS c₀ c₁ c₂ w₀ w₁ w₂ := by
  simp only [Config.uncovered, gapS]
  congr 1
  ext x
  simp only [Set.mem_iUnion, stack, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    rcases (by decide : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2) i with h | h | h <;> subst h
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · rintro ((h | h) | h)
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]

/-- **Attainment**: the stacking's gap area is exactly `δ²/2`. -/
theorem stackConfig_gapArea (hc01 : c₀ ≤ c₁) (hc12 : c₁ ≤ c₂)
    (ht : w₀ + w₁ + w₂ ≤ 1) :
    (stackConfig c₀ c₁ c₂ w₀ w₁ w₂ h0 h1 h2 k0 k1 k2).gapArea
      = (1 - (w₀ + w₁ + w₂)) ^ 2 / 2 := by
  rw [Config.gapArea, stackConfig_uncovered, volume_gapS h0 hc01 hc12 k0 k1 k2 ht,
    ENNReal.toReal_ofReal (by positivity)]

end Proofs.Quant
