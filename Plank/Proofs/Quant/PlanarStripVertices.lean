/- A planar strip containing three extreme points of a polygon contains a
whole defining face. The proof uses vertical sections, not a cyclic order. -/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarStripVertices

open Set

abbrev Plane := ℝ × ℝ

def Upper (K : Set Plane) (u : Plane) : Prop :=
  ∀ z ∈ K, z.1 = u.1 → z.2 ≤ u.2

def Lower (K : Set Plane) (u : Plane) : Prop :=
  ∀ z ∈ K, z.1 = u.1 → u.2 ≤ z.2

/-- An extreme point is an endpoint of its vertical section. -/
theorem extreme_upper_or_lower {K : Set Plane} {u : Plane}
    (hu : u ∈ K.extremePoints ℝ) : Upper K u ∨ Lower K u := by
  by_contra! hn
  obtain ⟨q, hq, hqx, hqy⟩ := show ∃ q ∈ K, q.1 = u.1 ∧ u.2 < q.2 by
    simpa only [Upper, not_forall, not_le, exists_prop] using hn.1
  obtain ⟨p, hp, hpx, hpy⟩ := show ∃ p ∈ K, p.1 = u.1 ∧ p.2 < u.2 by
    simpa only [Lower, not_forall, not_le, exists_prop] using hn.2
  let t := (u.2 - p.2) / (q.2 - p.2)
  have hd : 0 < q.2 - p.2 := by linarith
  have ht0 : 0 < t := div_pos (by linarith) hd
  have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith)
  have ht : t * (q.2 - p.2) = u.2 - p.2 := div_mul_cancel₀ _ hd.ne'
  have he : AffineMap.lineMap p q t = u := by
    rw [AffineMap.lineMap_apply_module']
    apply Prod.ext
    · change t * (q.1 - p.1) + p.1 = u.1
      rw [hqx, hpx]; ring
    · change t * (q.2 - p.2) + p.2 = u.2
      linarith only [ht]
  have hpu := hu.2 hp hq (he ▸ lineMap_mem_openSegment ℝ p q ⟨ht0, ht1⟩)
  have := congrArg Prod.snd hpu
  linarith

/-- On a vertical line an affine form has its vertical linear coefficient. -/
theorem vertical_difference (f : Plane →ᵃ[ℝ] ℝ) {p q : Plane} (hx : p.1 = q.1) :
    f p - f q = (p.2 - q.2) * f.linear (0, 1) := by
  have he : p - q = (p.2 - q.2) • ((0, 1) : Plane) := by
    ext <;> simp [hx]
  have h := f.linearMap_vsub p q
  change f.linear (p - q) = f p - f q at h
  rw [he, map_smul] at h
  exact h.symm

variable {ι : Type*}

/-- A maximum of a vertical polygon section activates an upward-facing row. -/
theorem exists_upper_active_row (s : Finset ι) (f : ι → Plane →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) {K : Set Plane}
    (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i)
    {p : Plane} (hp : p ∈ K) (hupper : Upper K p) :
    ∃ i ∈ s, f i p = b i ∧ 0 < (f i).linear (0, 1) := by
  classical
  by_contra! hn
  let A := s.filter fun i => 0 < (f i).linear (0, 1)
  let T : Set ℝ := ⋂ i ∈ A, {t | f i (p.1, p.2 + t) < b i}
  have hT : IsOpen T := isOpen_biInter_finset fun i _ =>
    isOpen_lt ((f i).continuous_of_finiteDimensional.comp (by fun_prop)) continuous_const
  have hzero : (0 : ℝ) ∈ T := by
    simp only [T, mem_iInter, mem_ofPred_eq]
    intro i hi
    obtain ⟨his, hip⟩ := Finset.mem_filter.mp hi
    have hne : f i p ≠ b i := fun he => not_lt_of_ge (hn i his he) hip
    simpa only [add_zero, Prod.eta] using lt_of_le_of_ne ((hrep p).mp hp i his) hne
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hzero)
  have hmem : r / 2 ∈ T := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith)
  let q : Plane := (p.1, p.2 + r / 2)
  have hq : q ∈ K := by
    apply (hrep q).mpr
    intro i hi
    by_cases hpos : 0 < (f i).linear (0, 1)
    · exact (mem_iInter.mp (mem_iInter.mp hmem i)
        (Finset.mem_filter.mpr ⟨hi, hpos⟩)).le
    · have he := vertical_difference (f i) (show q.1 = p.1 from rfl)
      have hmul := mul_nonpos_of_nonneg_of_nonpos (half_pos hr).le (le_of_not_gt hpos)
      have hfeas := (hrep p).mp hp i hi
      dsimp [q] at he
      nlinarith
  have hh := hupper q hq rfl
  dsimp [q] at hh
  linarith

/-- An upper extreme point cannot sit strictly between two points of a
common upward-facing supporting line. -/
theorem not_straddle_upper_extreme {K : Set Plane} (hc : Convex ℝ K)
    (f : Plane →ᵃ[ℝ] ℝ) (b : ℝ) (hside : ∀ x ∈ K, f x ≤ b)
    (hup : 0 < f.linear (0, 1)) {u p q : Plane}
    (hu : u ∈ K.extremePoints ℝ) (hupper : Upper K u)
    (hp : p ∈ K) (hq : q ∈ K) (hfp : f p = b) (hfq : f q = b)
    (hpu : p.1 < u.1) (huq : u.1 < q.1) : False := by
  let t := (u.1 - p.1) / (q.1 - p.1)
  have hd : 0 < q.1 - p.1 := by linarith
  have ht0 : 0 < t := div_pos (by linarith) hd
  have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith)
  have ht : t * (q.1 - p.1) = u.1 - p.1 := div_mul_cancel₀ _ hd.ne'
  let r := AffineMap.lineMap p q t
  have hrseg : r ∈ openSegment ℝ p q := lineMap_mem_openSegment ℝ p q ⟨ht0, ht1⟩
  have hrK : r ∈ K := hc.openSegment_subset hp hq hrseg
  have hrx : r.1 = u.1 := by
    change (AffineMap.lineMap p q t).1 = u.1
    rw [AffineMap.lineMap_apply_module']
    change t * (q.1 - p.1) + p.1 = u.1
    linarith only [ht]
  have hfr : f r = b := by
    dsimp [r]
    rw [f.apply_lineMap, hfp, hfq, AffineMap.lineMap_same_apply]
  have hval := vertical_difference f hrx.symm
  have hsu := hside u hu.1
  have hmul : (u.2 - r.2) * f.linear (0, 1) ≤ 0 := by linarith
  have hyr : u.2 ≤ r.2 := by
    by_contra! hgt
    exact (mul_pos (sub_pos.mpr hgt) hup).not_ge hmul
  have hru : r = u := Prod.ext hrx (le_antisymm (hupper r hrK hrx) hyr)
  have hpu' := hu.2 hp hq (hru ▸ hrseg)
  have := congrArg Prod.fst hpu'
  linarith

/-- Two upper extreme points force a whole defining face between their
horizontal coordinates. No irredundance or boundary order is needed. -/
theorem face_between_upper_extremes (s : Finset ι) (f : ι → Plane →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) {K : Set Plane} (hK : IsCompact K) (hc : Convex ℝ K)
    (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i)
    {u v : Plane} (hu : u ∈ K.extremePoints ℝ) (hv : v ∈ K.extremePoints ℝ)
    (hupp : Upper K u) (hvpp : Upper K v) (huv : u.1 < v.1) :
    ∃ i ∈ s, ∀ x ∈ K, f i x = b i → u.1 ≤ x.1 ∧ x.1 ≤ v.1 := by
  let c := (u.1 + v.1) / 2
  let M := K ∩ {x : Plane | x.1 = c}
  have hM : IsCompact M := hK.inter_right (isClosed_eq continuous_fst continuous_const)
  have hMne : M.Nonempty := by
    refine ⟨AffineMap.lineMap u v (1 / 2 : ℝ), ?_, ?_⟩
    · exact hc.openSegment_subset hu.1 hv.1
        (lineMap_mem_openSegment ℝ u v (by norm_num))
    · change (AffineMap.lineMap u v (1 / 2 : ℝ)).1 = c
      rw [AffineMap.lineMap_apply_module']
      change (1 / 2 : ℝ) * (v.1 - u.1) + u.1 = (u.1 + v.1) / 2
      ring
  obtain ⟨p, hp, hmax⟩ := hM.exists_isMaxOn hMne continuous_snd.continuousOn
  have hupper : Upper K p := by
    intro x hx hxp
    exact hmax ⟨hx, hxp.trans hp.2⟩
  obtain ⟨i, hi, hfi, hip⟩ := exists_upper_active_row s f b hrep hp.1 hupper
  have hup : u.1 < p.1 := by have := hp.2; dsimp [c] at this; linarith
  have hpv : p.1 < v.1 := by have := hp.2; dsimp [c] at this; linarith
  refine ⟨i, hi, ?_⟩
  intro x hx hfx
  constructor
  · by_contra! hxu
    exact not_straddle_upper_extreme hc (f i) (b i)
      (fun y hy => (hrep y).mp hy i hi) hip hu hupp hx hp.1 hfx hfi hxu hup
  · by_contra! hvx
    exact not_straddle_upper_extreme hc (f i) (b i)
      (fun y hy => (hrep y).mp hy i hi) hip hv hvpp hp.1 hx hfi hfx hpv hvx

/-- If no defining face lies in the strip, it contains at most one upper
extreme point. -/
theorem upper_extremes_subsingleton (s : Finset ι) (f : ι → Plane →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) {K : Set Plane} (hK : IsCompact K) (hc : Convex ℝ K)
    (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i) (a c : ℝ)
    (hface : ∀ i ∈ s, ¬∀ x ∈ K, f i x = b i → a ≤ x.1 ∧ x.1 ≤ c) :
    {u | u ∈ K.extremePoints ℝ ∧ a ≤ u.1 ∧ u.1 ≤ c ∧ Upper K u}.Subsingleton := by
  intro u hu v hv
  rcases lt_trichotomy u.1 v.1 with hlt | heq | hgt
  · obtain ⟨i, hi, h⟩ := face_between_upper_extremes s f b hK hc hrep hu.1 hv.1
      hu.2.2.2 hv.2.2.2 hlt
    exact (hface i hi (fun x hx hf =>
      ⟨hu.2.1.trans (h x hx hf).1, (h x hx hf).2.trans hv.2.2.1⟩)).elim
  · exact Prod.ext heq (le_antisymm (hv.2.2.2 u hu.1.1 heq)
      (hu.2.2.2 v hv.1.1 heq.symm))
  · obtain ⟨i, hi, h⟩ := face_between_upper_extremes s f b hK hc hrep hv.1 hu.1
      hv.2.2.2 hu.2.2.2 hgt
    exact (hface i hi (fun x hx hf =>
      ⟨hv.2.1.trans (h x hx hf).1, (h x hx hf).2.trans hu.2.2.1⟩)).elim

/-- Reflection gives the corresponding assertion for lower extreme points. -/
theorem lower_extremes_subsingleton (s : Finset ι) (f : ι → Plane →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) {K : Set Plane} (hK : IsCompact K) (hc : Convex ℝ K)
    (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i) (a c : ℝ)
    (hface : ∀ i ∈ s, ¬∀ x ∈ K, f i x = b i → a ≤ x.1 ∧ x.1 ≤ c) :
    {u | u ∈ K.extremePoints ℝ ∧ a ≤ u.1 ∧ u.1 ≤ c ∧ Lower K u}.Subsingleton := by
  let N : Plane ≃ₗ[ℝ] Plane := LinearEquiv.neg ℝ
  let M := N '' K
  let g (i) := (f i).comp N.toAffineEquiv.toAffineMap
  have hmem (x : Plane) : x ∈ M ↔ -x ∈ K := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [N] using hy
    · intro hx
      exact ⟨-x, hx, by simp [N]⟩
  have hM : IsCompact M := hK.image N.continuous_of_finiteDimensional
  have hcM : Convex ℝ M := hc.linear_image N.toLinearMap
  have hrepM (x : Plane) : x ∈ M ↔ ∀ i ∈ s, g i x ≤ b i := by
    rw [hmem, hrep]
    rfl
  have hfaceM : ∀ i ∈ s, ¬∀ x ∈ M, g i x = b i → -c ≤ x.1 ∧ x.1 ≤ -a := by
    intro i hi hn
    apply hface i hi
    intro x hx hfx
    have hxM : -x ∈ M := (hmem (-x)).mpr (by simpa using hx)
    have hgx : g i (-x) = b i := by simpa [g, N] using hfx
    have hh := hn (-x) hxM hgx
    change -c ≤ -x.1 ∧ -x.1 ≤ -a at hh
    constructor <;> linarith [hh.1, hh.2]
  have hsub := upper_extremes_subsingleton s g b hM hcM hrepM (-c) (-a) hfaceM
  have htransform (u : Plane)
      (hu : u ∈ K.extremePoints ℝ ∧ a ≤ u.1 ∧ u.1 ≤ c ∧ Lower K u) :
      -u ∈ M.extremePoints ℝ ∧ -c ≤ (-u).1 ∧ (-u).1 ≤ -a ∧ Upper M (-u) := by
    refine ⟨?_, by change -c ≤ -u.1; linarith [hu.2.2.1],
      by change -u.1 ≤ -a; linarith [hu.2.1], ?_⟩
    · rw [← image_extremePoints N K]
      exact ⟨u, hu.1, rfl⟩
    · intro x hx hxu
      have hxK := (hmem x).mp hx
      have hfirst : (-x).1 = u.1 := by change -x.1 = u.1; change x.1 = -u.1 at hxu; linarith
      have hh := hu.2.2.2 (-x) hxK hfirst
      change u.2 ≤ -x.2 at hh
      change x.2 ≤ -u.2
      linarith
  intro u hu v hv
  exact neg_injective (hsub (htransform u hu) (htransform v hv))

/-- A strip in a compact planar halfspace intersection has at most two
extreme points unless it contains a whole defining face. -/
theorem strip_extremes_finite_ncard_le_two (s : Finset ι)
    (f : ι → Plane →ᵃ[ℝ] ℝ) (b : ι → ℝ) {K : Set Plane}
    (hK : IsCompact K) (hc : Convex ℝ K)
    (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i) (a c : ℝ)
    (hface : ∀ i ∈ s, ¬∀ x ∈ K, f i x = b i → a ≤ x.1 ∧ x.1 ≤ c) :
    (K.extremePoints ℝ ∩ {x | a ≤ x.1 ∧ x.1 ≤ c}).Finite ∧
      (K.extremePoints ℝ ∩ {x | a ≤ x.1 ∧ x.1 ≤ c}).ncard ≤ 2 := by
  let U := {u | u ∈ K.extremePoints ℝ ∧ a ≤ u.1 ∧ u.1 ≤ c ∧ Upper K u}
  let L := {u | u ∈ K.extremePoints ℝ ∧ a ≤ u.1 ∧ u.1 ≤ c ∧ Lower K u}
  have hU : U.Subsingleton := upper_extremes_subsingleton s f b hK hc hrep a c hface
  have hL : L.Subsingleton := lower_extremes_subsingleton s f b hK hc hrep a c hface
  have hsub : K.extremePoints ℝ ∩ {x | a ≤ x.1 ∧ x.1 ≤ c} ⊆ U ∪ L := by
    intro x hx
    rcases extreme_upper_or_lower hx.1 with hu | hl
    · exact Or.inl ⟨hx.1, hx.2.1, hx.2.2, hu⟩
    · exact Or.inr ⟨hx.1, hx.2.1, hx.2.2, hl⟩
  have hfin := hU.finite.union hL.finite
  refine ⟨hfin.subset hsub, (ncard_le_ncard hsub hfin).trans ?_⟩
  exact (ncard_union_le U L).trans (Nat.add_le_add
    ((ncard_le_one hU.finite).mpr hU) ((ncard_le_one hL.finite).mpr hL))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- Transport the section argument through any linear planar chart whose
first coordinate is the plank form, up to a constant. -/
theorem strip_extremes_finite_ncard_le_two_of_chart
    (A : Plane ≃ₗ[ℝ] E) (g : E →ᵃ[ℝ] ℝ) (k : ℝ)
    (hA : ∀ x, g (A x) = x.1 + k)
    (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ) (b : ι → ℝ) {K : Set E}
    (hK : IsCompact K) (hc : Convex ℝ K)
    (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i) (a c : ℝ)
    (hface : ∀ i ∈ s, ¬∀ x ∈ K, f i x = b i → a ≤ g x ∧ g x ≤ c) :
    (K.extremePoints ℝ ∩ {x | a ≤ g x ∧ g x ≤ c}).Finite ∧
      (K.extremePoints ℝ ∩ {x | a ≤ g x ∧ g x ≤ c}).ncard ≤ 2 := by
  let C := A.symm '' K
  let F (i) := (f i).comp A.toAffineEquiv.toAffineMap
  have hmem (x : Plane) : x ∈ C ↔ A x ∈ K := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨A x, hx, A.symm_apply_apply x⟩
  have hC : IsCompact C := hK.image A.symm.continuous_of_finiteDimensional
  have hcC : Convex ℝ C := hc.linear_image A.symm.toLinearMap
  have hrepC (x : Plane) : x ∈ C ↔ ∀ i ∈ s, F i x ≤ b i := by
    rw [hmem, hrep]
    rfl
  have hfaceC : ∀ i ∈ s, ¬∀ x ∈ C, F i x = b i → a-k ≤ x.1 ∧ x.1 ≤ c-k := by
    intro i hi hn
    apply hface i hi
    intro x hx hfx
    have hxC : A.symm x ∈ C := ⟨x, hx, rfl⟩
    have hFx : F i (A.symm x) = b i := by simpa [F] using hfx
    have hh := hn (A.symm x) hxC hFx
    have hg := hA (A.symm x)
    rw [A.apply_symm_apply] at hg
    constructor <;> linarith [hh.1, hh.2]
  obtain ⟨hfinite, hcard⟩ :=
    strip_extremes_finite_ncard_le_two s F b hC hcC hrepC (a-k) (c-k) hfaceC
  have he : K.extremePoints ℝ ∩ {x | a ≤ g x ∧ g x ≤ c} =
      A '' (C.extremePoints ℝ ∩ {x | a-k ≤ x.1 ∧ x.1 ≤ c-k}) := by
    ext x
    constructor
    · intro hx
      refine ⟨A.symm x, ⟨?_, ?_⟩, A.apply_symm_apply x⟩
      · rw [← image_extremePoints A.symm K]
        exact ⟨x, hx.1, rfl⟩
      · have hg := hA (A.symm x)
        rw [A.apply_symm_apply] at hg
        constructor <;> linarith [hx.2.1, hx.2.2]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · have hext : A y ∈ (A '' C).extremePoints ℝ := by
          rw [← image_extremePoints A C]
          exact ⟨y, hy.1, rfl⟩
        have heq : A '' C = K := by
          ext z
          constructor
          · rintro ⟨w, hw, rfl⟩
            exact (hmem w).mp hw
          · intro hz
            exact ⟨A.symm z, ⟨z, hz, rfl⟩, A.apply_symm_apply z⟩
        rwa [heq] at hext
      · change a ≤ g (A y) ∧ g (A y) ≤ c
        rw [hA]
        constructor <;> linarith [hy.2.1, hy.2.2]
  rw [he, ncard_image_of_injective _ A.injective]
  exact ⟨hfinite.image A, hcard⟩

end Plank.PlanarStripVertices
