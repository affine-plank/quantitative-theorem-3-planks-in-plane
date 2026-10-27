/- Width-dependent cap/window contraction; reexports the elementary core API. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalCapWindowCore
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalCapWindowScaling

open Set MeasureTheory
open scoped Pointwise

variable {d : ℕ}

/-- The actual gap outside one canonical closed window. -/
def gap (K : Set (Point d)) (f : Point d →ᵃ[ℝ] ℝ) (c r : ℝ) : ℝ :=
  (volume (K \ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal

theorem gap_eq_sub_window {K : Set (Point d)} (hK : IsCompact K)
    (f : Point d →ᵃ[ℝ] ℝ) (c r : ℝ) :
    gap K f c r = (volume K).toReal-
      (volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal := by
  have hm : MeasurableSet {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r} :=
    ((isClosed_le continuous_const (continuous_form f)).inter
      (isClosed_le (continuous_form f) continuous_const)).measurableSet
  have h := measureReal_sdiff_add_inter (μ := volume) (s := K) hm hK.measure_ne_top
  change gap K f c r+
    (volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal =
      (volume K).toReal at h
  linarith only [h]

/-- The gap is the sum of the two cap volumes; their boundary levels are null. -/
theorem gap_eq_caps {K : Set (Point d)} (hK : IsCompact K)
    (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    gap K f c r = (volume (cap K f ((1-r)*c))).toReal+
      (volume (cap K (reflect f) ((1-r)*(1-c)))).toReal := by
  rw [gap_eq_sub_window hK]
  have h := cap_window_partition hK f hf
    (show (1-r)*c ≤ c+(1-c)*r by nlinarith only [hr])
  rw [show 1-(c+(1-c)*r) = (1-r)*(1-c) by ring] at h
  linarith only [h]

/-- A cap retains at least the homothetic power of its anchor volume. -/
theorem cap_power_lower_bound {K : Set (Point d)} (hK : IsCompact K)
    (hc : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hzero : ∃ x ∈ K, f x=0)
    {c r : ℝ} (hc0 : 0 ≤ c) (hr : r ∈ Icc 0 1) :
    (1-r)^(d+1)*(volume (cap K f c)).toReal ≤
      (volume (cap K f ((1-r)*c))).toReal := by
  have h := pow_le_pow_left₀
    (mul_nonneg (sub_nonneg.mpr hr.2) (volumeRoot_nonneg (cap K f c)))
    (root_cap_contract hK hc f hzero hc0 hr) (d+1)
  simpa only [mul_pow, volumeRoot_pow] using h

/-- A zero-width window removes only a null affine level. -/
theorem gap_zero {K : Set (Point d)} (hK : IsCompact K)
    (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ) :
    gap K f c 0=(volume K).toReal := by
  rw [gap_eq_caps hK f hf c le_rfl]
  simpa only [sub_zero,one_mul] using cap_partition hK f hf c

/-- The actual one-window excess is nonnegative in every positive dimension. -/
theorem gap_excess_nonneg {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c r : ℝ} (hc : c ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    0 ≤ gap K f c r-(1-r)^(d+1)*(volume K).toReal := by
  have hgzero : ∃ x ∈ K, reflect f x=0 := by
    obtain ⟨x,hx,hfx⟩ := hone
    exact ⟨x,hx,by simp only [reflect_apply,hfx,sub_self]⟩
  have hm := cap_power_lower_bound hK hconv f hzero hc.1 hr
  have hp := cap_power_lower_bound hK hconv (reflect f) hgzero (sub_nonneg.mpr hc.2) hr
  rw [gap_eq_caps hK f hf c hr.1, ← cap_partition hK f hf c]
  nlinarith only [hm, hp]

/-- Moving both endpoints towards a larger point increases a power difference
by at least the factor by which their distance contracts. -/
theorem pow_difference_mix {u v w t : ℝ} (hw : 0 ≤ w) (hwv : w ≤ v)
    (hvu : v ≤ u) (ht : t ∈ Icc 0 1) (n : ℕ) :
    t*(v^n-w^n) ≤ ((1-t)*u+t*v)^n-((1-t)*u+t*w)^n := by
  have hv := hw.trans hwv
  have hvU : v ≤ (1-t)*u+t*v := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hvu)]
  have hwW : w ≤ (1-t)*u+t*w := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hwv.trans hvu))]
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow := pow_le_pow_left₀ hv hvU n
    have hdiff := sub_nonneg.mpr (pow_le_pow_left₀ hw hwv n)
    have hleft := mul_le_mul_of_nonneg_left hpow (mul_nonneg ht.1 (sub_nonneg.mpr hwv))
    have hright := mul_le_mul hwW ih (mul_nonneg ht.1 hdiff) (hw.trans hwW)
    simp only [pow_succ]
    nlinarith only [hleft,hright]

/-- The actual cap excess contracts linearly in every positive dimension. -/
theorem cap_contraction_linear {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Point d →ᵃ[ℝ] ℝ) (hzero : ∃ x ∈ K, f x=0)
    {c t r : ℝ} (hc0 : 0 ≤ c) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    t*(volume (cap K f ((1-r)*c))).toReal+
      ((1-t*r)^(d+1)-t*(1-r)^(d+1))*(volume (cap K f c)).toReal ≤
      (volume (cap K f ((1-t*r)*c))).toReal := by
  let u := volumeRoot (cap K f c)
  let v := volumeRoot (cap K f ((1-r)*c))
  have hu : 0 ≤ u := volumeRoot_nonneg _
  have hw : 0 ≤ (1-r)*u := mul_nonneg (sub_nonneg.mpr hr.2) hu
  have hwv : (1-r)*u ≤ v := root_cap_contract hK hc f hzero hc0 hr
  have hrc : (1-r)*c ≤ c := by nlinarith only [mul_nonneg hr.1 hc0]
  have hvu : v ≤ u := volumeRoot_mono (compact_cap hK f c) (by
    intro x hx
    exact ⟨hx.1,hx.2.trans hrc⟩)
  obtain ⟨x,hx,hfx⟩ := hzero
  have hmix := root_cap_mix hK hc f
    (show (cap K f c).Nonempty from ⟨x,hx,hfx.le.trans hc0⟩)
    (show (cap K f ((1-r)*c)).Nonempty from
      ⟨x,hx,hfx.le.trans (mul_nonneg (sub_nonneg.mpr hr.2) hc0)⟩)
    (sub_nonneg.mpr ht.2) ht.1 (by ring)
  rw [show (1-t)*c+t*((1-r)*c)=(1-t*r)*c by ring] at hmix
  have hp := pow_le_pow_left₀
    (add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hu)
      (mul_nonneg ht.1 (volumeRoot_nonneg _))) hmix (d+1)
  have hdiff := pow_difference_mix hw hwv hvu ht (d+1)
  rw [show (1-t)*u+t*((1-r)*u)=(1-t*r)*u by ring, mul_pow, mul_pow] at hdiff
  dsimp only [u,v] at hp hdiff
  simp only [volumeRoot_pow] at hp hdiff
  nlinarith only [hp,hdiff]

/-- Linear contraction of the actual one-window excess, including scale zero. -/
theorem gap_excess_contraction_linear {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    t*(gap K f c r-(1-r)^(d+1)*(volume K).toReal) ≤
      gap K f c (t*r)-(1-t*r)^(d+1)*(volume K).toReal := by
  have hgzero : ∃ x ∈ K, reflect f x=0 := by
    obtain ⟨x,hx,hfx⟩ := hone
    exact ⟨x,hx,by simp only [reflect_apply,hfx,sub_self]⟩
  have hm := cap_contraction_linear hK hconv f hzero hc.1 ht hr
  have hp := cap_contraction_linear hK hconv (reflect f) hgzero
    (sub_nonneg.mpr hc.2) ht hr
  have he := cap_partition hK f hf c
  rw [gap_eq_caps hK f hf c hr.1, gap_eq_caps hK f hf c (mul_nonneg ht.1 hr.1)]
  rw [← he]
  nlinarith only [hm,hp]

/-- The gap excess above the one-plank power law contracts by at least `t^(d+1)`.
All terms are actual volumes; no piecewise polynomial volume model is assumed. -/
theorem gap_excess_contraction {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    t^(d+1)*(gap K f c r-(1-r)^(d+1)*(volume K).toReal) ≤
      gap K f c (t*r)-(1-t*r)^(d+1)*(volume K).toReal := by
  have h := gap_excess_contraction_linear hK hconv f hf hzero hone hc ht hr
  have he := gap_excess_nonneg hK hconv f hf hzero hone hc hr
  have htp : t^(d+1) ≤ t := by
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1 ht.2) ht.1).trans_eq (one_mul t)
  nlinarith only [h, mul_le_mul_of_nonneg_right htp he]

/-- The actual three-dimensional window estimate, including zero widths
and support-flush positions. This is a volume statement about the convex body. -/
theorem window_contraction_three {K : Set (Point 2)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point 2 →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (volume (K ∩ {x | (1-t*r)*c ≤ f x ∧ f x ≤ c+(1-c)*(t*r)})).toReal ≤
      t^3*(volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal+
        3*t*r*(1-t)*(1+t-t*r)*(volume K).toReal := by
  have h := window_contraction hK hconv f hf hzero hone hc ht hr
  norm_num only at h
  convert h using 1
  ring

/-- A nonnegative affine function of the natural root, raised back to that
natural power, is concave. The binomial expansion uses only powers in `[0,1]`. -/
theorem concaveOn_root_affine_pow (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (n : ℕ) (hn : n ≠ 0) :
    ConcaveOn ℝ (Ici 0) (fun x : ℝ => (a+b*x^((n : ℝ)⁻¹))^n) := by
  have hnp : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  let q (k : ℕ) : ℝ := a^(n-k)*b^k*(n.choose k : ℝ)
  have expand (x : ℝ) (hx : 0 ≤ x) :
      (a+b*x^((n : ℝ)⁻¹))^n =
        ∑ k ∈ Finset.range (n+1), q k*x^((k : ℝ)/(n : ℝ)) := by
    rw [add_comm a, add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_pow, ← Real.rpow_mul_natCast hx]
    rw [show (n : ℝ)⁻¹*(k : ℝ) = (k : ℝ)/(n : ℝ) by ring]
    dsimp only [q]
    ring
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy α β hα hβ hsum
  simp only [smul_eq_mul]
  rw [expand x hx, expand y hy,
    expand (α*x+β*y) (add_nonneg (mul_nonneg hα hx) (mul_nonneg hβ hy)),
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkp : (k : ℝ)/(n : ℝ) ≤ 1 :=
    (div_le_one hnp).mpr (by exact_mod_cast hkn)
  have h := (Real.concaveOn_rpow (div_nonneg (Nat.cast_nonneg k) hnp.le) hkp).2
    hx hy hα hβ hsum
  simp only [smul_eq_mul] at h
  have hq : 0 ≤ q k := by dsimp only [q]; positivity
  nlinarith only [mul_le_mul_of_nonneg_left h hq]

/-- The chord inequality for the root-affine power, without division. -/
theorem pow_difference_mix_chord {u v w t : ℝ} (hw : 0 ≤ w) (hwv : w ≤ v)
    (hvu : v ≤ u) (ht : t ∈ Icc 0 1) (n : ℕ) (hn : n ≠ 0) :
    (u^n-((1-t)*u+t*w)^n)*(v^n-w^n) ≤
      (u^n-w^n)*(((1-t)*u+t*v)^n-((1-t)*u+t*w)^n) := by
  rcases eq_or_lt_of_le hwv with rfl | hwv
  · simp
  rcases eq_or_lt_of_le hvu with rfl | hvu
  · rw [show (1-t)*v+t*v=v by ring]
    exact le_of_eq (mul_comm _ _)
  have hv := hw.trans hwv.le
  have hu := hv.trans hvu.le
  have h := (concaveOn_root_affine_pow ((1-t)*u) t
    (mul_nonneg (sub_nonneg.mpr ht.2) hu) ht.1 n hn).neg.secant_mono_aux1
    (show w^n ∈ Ici (0 : ℝ) from pow_nonneg hw n)
    (show u^n ∈ Ici (0 : ℝ) from pow_nonneg hu n)
    (pow_lt_pow_left₀ hwv hw hn) (pow_lt_pow_left₀ hvu hv hn)
  simp only [Pi.neg_apply, Real.pow_rpow_inv_natCast hw hn,
    Real.pow_rpow_inv_natCast hv hn, Real.pow_rpow_inv_natCast hu hn] at h
  rw [show (1-t)*u+t*u=u by ring] at h
  nlinarith only [h]

/-- Relative loss of a power under mixing towards its larger endpoint. -/
theorem pow_loss_mix_ratio {u v t r : ℝ} (hu : 0 ≤ u)
    (hl : (1-r)*u ≤ v) (hv : v ≤ u) (ht : t ∈ Icc 0 1)
    (hr : r ∈ Icc 0 1) (n : ℕ) (hn : n ≠ 0) :
    (1-(1-r)^n)*(u^n-((1-t)*u+t*v)^n) ≤
      (1-(1-t*r)^n)*(u^n-v^n) := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · have hv0 : v=0 := le_antisymm hv (by simpa using hl)
    simp [hv0, hn]
  have h := pow_difference_mix_chord
    (mul_nonneg (sub_nonneg.mpr hr.2) hu.le) hl hv ht n hn
  rw [show (1-t)*u+t*((1-r)*u)=(1-t*r)*u by ring] at h
  simp only [mul_pow] at h
  have hp : u^n*((1-(1-r)^n)*(u^n-((1-t)*u+t*v)^n)) ≤
      u^n*((1-(1-t*r)^n)*(u^n-v^n)) := by nlinarith only [h]
  exact le_of_mul_le_mul_left hp (pow_pos hu n)

/-- Multiplicative contraction of the volume removed from an anchor cap.
All factors are polynomial; no positive-volume or positive-width premise is needed. -/
theorem cap_contraction_ratio {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Point d →ᵃ[ℝ] ℝ) (hzero : ∃ x ∈ K, f x=0)
    {c t r : ℝ} (hc0 : 0 ≤ c) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (1-(1-r)^(d+1))*((volume (cap K f c)).toReal-
      (volume (cap K f ((1-t*r)*c))).toReal) ≤
    (1-(1-t*r)^(d+1))*((volume (cap K f c)).toReal-
      (volume (cap K f ((1-r)*c))).toReal) := by
  obtain ⟨x,hx,hfx⟩ := hzero
  have hne (s : ℝ) (hs : 0 ≤ s) : (cap K f s).Nonempty := ⟨x,hx,hfx.le.trans hs⟩
  have hn (s : ℝ) := volumeRoot_nonneg (cap K f s)
  have hrn := sub_nonneg.mpr hr.2
  have htn := sub_nonneg.mpr ht.2
  have hm := root_cap_mix hK hc f (hne c hc0)
    (hne ((1-r)*c) (mul_nonneg hrn hc0)) htn ht.1 (by ring)
  rw [show (1-t)*c+t*((1-r)*c)=(1-t*r)*c by ring] at hm
  have hu : volumeRoot (cap K f ((1-r)*c)) ≤ volumeRoot (cap K f c) := by
    apply volumeRoot_mono (compact_cap hK f c)
    intro y hy
    refine ⟨hy.1, ?_⟩
    change f y ≤ c
    apply le_trans hy.2
    nlinarith only [mul_nonneg hr.1 hc0]
  have h := pow_loss_mix_ratio (hn c)
    (root_cap_contract hK hc f ⟨x,hx,hfx⟩ hc0 hr) hu ht hr (d+1) (Nat.succ_ne_zero d)
  have hp := pow_le_pow_left₀
    (add_nonneg (mul_nonneg htn (hn c)) (mul_nonneg ht.1 (hn _))) hm (d+1)
  have hq : 0 ≤ 1-(1-r)^(d+1) :=
    sub_nonneg.mpr (pow_le_one₀ hrn (by linarith only [hr.1]))
  have hmul := mul_le_mul_of_nonneg_left hp hq
  simp only [volumeRoot_pow] at h hmul
  nlinarith only [h, hmul]

/-- Multiplicative scaling of actual covered volume in every positive dimension.
Attained values zero and one need not be extreme; all zero-width cases are included. -/
theorem window_contraction_ratio {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (1-(1-r)^(d+1))*
      (volume (K ∩ {x | (1-t*r)*c ≤ f x ∧ f x ≤ c+(1-c)*(t*r)})).toReal ≤
    (1-(1-t*r)^(d+1))*
      (volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal := by
  have hgzero : ∃ x ∈ K, reflect f x=0 := by
    obtain ⟨x,hx,hfx⟩ := hone
    exact ⟨x,hx,by simp only [reflect_apply,hfx,sub_self]⟩
  have hm := cap_contraction_ratio hK hconv f hzero hc.1 ht hr
  have hp := cap_contraction_ratio hK hconv (reflect f) hgzero
    (sub_nonneg.mpr hc.2) ht hr
  have hb (s : ℝ) (hs0 : 0 ≤ s) :
      (volume (cap K f ((1-s)*c))).toReal+
        (volume (cap K (reflect f) ((1-s)*(1-c)))).toReal =
      (volume K).toReal-
        (volume (K ∩ {x | (1-s)*c ≤ f x ∧ f x ≤ c+(1-c)*s})).toReal := by
    have h := cap_window_partition hK f hf
      (show (1-s)*c ≤ c+(1-c)*s by nlinarith only [hs0])
    rw [show 1-(c+(1-c)*s)=(1-s)*(1-c) by ring] at h
    linarith only [h]
  have he := cap_partition hK f hf c
  have h : (1-(1-r)^(d+1))*
      (((volume (cap K f c)).toReal+(volume (cap K (reflect f) (1-c))).toReal)-
       ((volume (cap K f ((1-t*r)*c))).toReal+
        (volume (cap K (reflect f) ((1-t*r)*(1-c)))).toReal)) ≤
      (1-(1-t*r)^(d+1))*
      (((volume (cap K f c)).toReal+(volume (cap K (reflect f) (1-c))).toReal)-
       ((volume (cap K f ((1-r)*c))).toReal+
        (volume (cap K (reflect f) ((1-r)*(1-c)))).toReal)) := by
    nlinarith only [hm, hp]
  rw [he, hb r hr.1, hb (t*r) (mul_nonneg ht.1 hr.1)] at h
  simpa only [sub_sub_cancel] using h

/-- Covered volume divided by the conical loss polynomial is nondecreasing.
The positive-width domain is explicit; the polynomial endpoint above includes zero. -/
theorem window_volume_ratio_monotone {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c : ℝ} (hc : c ∈ Icc 0 1) :
    MonotoneOn (fun r : ℝ =>
      (volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal/
        (1-(1-r)^(d+1))) (Ioc 0 1) := by
  intro r hr s hs hrs
  have ht : r/s ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr.1.le hs.1.le, (div_le_one hs.1).mpr hrs⟩
  have h := window_contraction_ratio hK hconv f hf hzero hone hc ht ⟨hs.1.le,hs.2⟩
  rw [div_mul_cancel₀ r hs.1.ne'] at h
  have hq (z : ℝ) (hz : z ∈ Ioc (0 : ℝ) 1) : 0 < 1-(1-z)^(d+1) :=
    sub_pos.mpr (pow_lt_one₀ (sub_nonneg.mpr hz.2)
      (by linarith only [hz.1]) (Nat.succ_ne_zero d))
  exact (div_le_div_iff₀ (hq r hr) (hq s hs)).mpr (by nlinarith only [h])

/-- The covered-volume ratio is equivalently a ratio inequality for excess. -/
theorem gap_excess_contraction_ratio {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (1-(1-t*r)^(d+1))*(gap K f c r-(1-r)^(d+1)*(volume K).toReal) ≤
      (1-(1-r)^(d+1))*(gap K f c (t*r)-(1-t*r)^(d+1)*(volume K).toReal) := by
  have h := window_contraction_ratio hK hconv f hf hzero hone hc ht hr
  simp only [gap_eq_sub_window hK]
  nlinarith only [h]

/-- The exact excess retained by expansion from width `r` to `r/t`.
At zero width, use the dimension-uniform coefficient. -/
def excessWeight (d : ℕ) (t r : ℝ) : ℝ :=
  if r=0 then 1-t^d else
    1-(t^(d+1)-(t-r)^(d+1))/(1-(1-r)^(d+1))

/-- Clearing the width denominator also includes width zero. -/
theorem excessWeight_mul (t : ℝ) {r : ℝ} (hr : r ∈ Icc 0 1) :
    excessWeight d t r*(1-(1-r)^(d+1))=
      1-(1-r)^(d+1)-(t^(d+1)-(t-r)^(d+1)) := by
  by_cases hz : r=0
  · simp [hz,excessWeight]
  have hp : (1-r)^(d+1)<1 := pow_lt_one₀ (sub_nonneg.mpr hr.2)
    (sub_lt_self _ (lt_of_le_of_ne hr.1 (Ne.symm hz))) (Nat.succ_ne_zero d)
  rw [excessWeight,ite_eq_right hz,sub_mul,one_mul,div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hp))]

/-- Expansion controls the actual covered volume directly. -/
theorem window_expansion_bound {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Ioc 0 1)
    (hr : 0 ≤ r) (hrt : r ≤ t) :
    (1-excessWeight d t r)*(volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal ≤
      t^(d+1)*(volume (K ∩ {x | (1-r/t)*c ≤ f x ∧ f x ≤ c+(1-c)*(r/t)})).toReal := by
  by_cases hz : r=0
  · subst r
    have h := gap_eq_sub_window hK f c 0
    rw [gap_zero hK f hf c] at h
    have ha : (volume (K ∩ {x | (1-(0 : ℝ))*c ≤ f x ∧ f x ≤ c+(1-c)*0})).toReal=0 := by
      linarith only [h]
    simp only [mul_zero] at ha
    simp only [zero_div,mul_zero,ha,le_refl]
  have hq : 0 < 1-(1-r)^(d+1) := sub_pos.mpr (pow_lt_one₀
    (sub_nonneg.mpr (hrt.trans ht.2))
    (sub_lt_self _ (lt_of_le_of_ne hr (Ne.symm hz))) (Nat.succ_ne_zero d))
  have h := window_contraction_ratio hK hconv f hf hzero hone hc
    ⟨ht.1.le,ht.2⟩ ⟨div_nonneg hr ht.1.le,(div_le_one ht.1).mpr hrt⟩
  have hid : t*(r/t)=r := by field_simp [ne_of_gt ht.1]
  simp only [hid] at h
  have hmul := mul_le_mul_of_nonneg_left h (pow_nonneg ht.1.le (d+1))
  have hp : t^(d+1)*(1-(1-r/t)^(d+1))=t^(d+1)-(t-r)^(d+1) := by
    rw [mul_sub,mul_one,← mul_pow]
    congr 2
    field_simp [ne_of_gt ht.1]
  rw [excessWeight,ite_eq_right hz,sub_sub_cancel,div_mul_eq_mul_div,div_le_iff₀ hq]
  rw [← mul_assoc,hp] at hmul
  nlinarith only [hmul]

/-- The exact weight dominates the dimension-uniform surplus coefficient. -/
theorem excessWeight_contracted_ge {t r : ℝ} (ht : t ∈ Icc 0 1)
    (hr : r ∈ Icc 0 1) : 1-t^d ≤ excessWeight d t (t*r) := by
  by_cases hz : t*r=0
  · simp [excessWeight,hz]
  have htrpos : 0 < t*r := lt_of_le_of_ne (mul_nonneg ht.1 hr.1) (Ne.symm hz)
  have htr1 : t*r ≤ 1 := (mul_le_mul_of_nonneg_left hr.2 ht.1).trans
    (by simpa only [mul_one] using ht.2)
  have hqpos : 0 < 1-(1-t*r)^(d+1) :=
    sub_pos.mpr (pow_lt_one₀ (sub_nonneg.mpr htr1)
      (by linarith only [htrpos]) (Nat.succ_ne_zero d))
  have hq := (convexOn_pow (𝕜 := ℝ) (d+1)).2
    (show (1 : ℝ) ∈ Ici 0 by norm_num)
    (show 1-r ∈ Ici (0 : ℝ) from sub_nonneg.mpr hr.2)
    (sub_nonneg.mpr ht.2) ht.1 (by ring)
  simp only [smul_eq_mul,one_pow] at hq
  rw [show (1-t)*1+t*(1-r)=1-t*r by ring] at hq
  have hm := mul_le_mul_of_nonneg_left
    (show t*(1-(1-r)^(d+1)) ≤ 1-(1-t*r)^(d+1) by linarith only [hq])
    (pow_nonneg ht.1 d)
  have hh : t^(d+1)*(1-(1-r)^(d+1))/(1-(1-t*r)^(d+1)) ≤ t^d := by
    apply (div_le_iff₀ hqpos).mpr
    simpa only [pow_succ,mul_assoc] using hm
  rw [excessWeight,ite_eq_right hz,show t-t*r=t*(1-r) by ring,mul_pow]
  rw [show t^(d+1)-t^(d+1)*(1-r)^(d+1)=t^(d+1)*(1-(1-r)^(d+1)) by ring]
  exact sub_le_sub_left hh 1

/-- The same weight comparison in the original widths, including scale zero. -/
theorem excessWeight_ge {t r : ℝ} (ht : t ∈ Icc 0 1)
    (hr : 0 ≤ r) (hrt : r ≤ t) : 1-t^d ≤ excessWeight d t r := by
  by_cases hz : t=0
  · have hrzero : r=0 := le_antisymm (by simpa only [hz] using hrt) hr
    simp [hrzero,excessWeight]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have h := excessWeight_contracted_ge (d := d) ht
    (show r/t ∈ Icc (0 : ℝ) 1 from
      ⟨div_nonneg hr ht.1,(div_le_one htpos).mpr hrt⟩)
  simpa only [mul_div_cancel₀ r hz] using h

/-- The planar coefficient is the earlier rational width weight. -/
theorem excessWeight_two (t : ℝ) {r : ℝ} (hr : r ∈ Icc 0 1) :
    excessWeight 1 t r=(1-t)*(2/(2-r)) := by
  by_cases hz : r=0
  · norm_num [excessWeight,hz]
  have h2 : 2-r ≠ 0 := by linarith only [hr.2]
  rw [excessWeight,ite_eq_right hz]
  norm_num only
  rw [show 1-(1-r)^2=r*(2-r) by ring]
  field_simp [hz,h2]
  ring

/-- The spatial coefficient retains the exact quadratic width dependence. -/
theorem excessWeight_three (t : ℝ) {r : ℝ} (hr : r ∈ Icc 0 1) :
    excessWeight 2 t r=(1-t)*(3*(1+t-r)/(3-3*r+r^2)) := by
  by_cases hz : r=0
  · norm_num [excessWeight,hz]
    ring
  have hd : 0 < 3-3*r+r^2 := by nlinarith only [sq_nonneg (1-r),hr.2]
  rw [excessWeight,ite_eq_right hz]
  norm_num only
  rw [show 1-(1-r)^3=r*(3-3*r+r^2) by ring]
  let a := 3-3*r+r^2
  have ha : a ≠ 0 := ne_of_gt hd
  change 1-(t^3-(t-r)^3)/(r*a)=(1-t)*(3*(1+t-r)/a)
  field_simp [hz,ha]
  dsimp only [a]
  ring

/-- One weighted excess law works in every positive dimension, including
zero scale and zero width. Its weight is exactly the covered-volume ratio. -/
theorem gap_excess_contraction_weighted {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    t^(d+1)*(gap K f c r-(1-r)^(d+1)*(volume K).toReal)+
      excessWeight d t (t*r)*(gap K f c (t*r)-(1-t*r)^(d+1)*(volume K).toReal) ≤
      gap K f c (t*r)-(1-t*r)^(d+1)*(volume K).toReal := by
  by_cases htzero : t=0
  · simp [htzero,gap_zero hK f hf c,excessWeight]
  by_cases hrzero : r=0
  · simp [hrzero,gap_zero hK f hf c,excessWeight]
  have htrpos : 0 < t*r := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm htzero))
    (lt_of_le_of_ne hr.1 (Ne.symm hrzero))
  have htr1 : t*r ≤ 1 := (mul_le_mul_of_nonneg_left hr.2 ht.1).trans
    (by simpa only [mul_one] using ht.2)
  have hd : 0 < 1-(1-t*r)^(d+1) :=
    sub_pos.mpr (pow_lt_one₀ (sub_nonneg.mpr htr1)
      (by linarith only [htrpos]) (Nat.succ_ne_zero d))
  let E := gap K f c r-(1-r)^(d+1)*(volume K).toReal
  let E' := gap K f c (t*r)-(1-t*r)^(d+1)*(volume K).toReal
  let q := 1-(1-t*r)^(d+1)
  let Q := 1-(1-r)^(d+1)
  have h := gap_excess_contraction_ratio hK hconv f hf hzero hone hc ht hr
  change q*E ≤ Q*E' at h
  rw [excessWeight,ite_eq_right (ne_of_gt htrpos),show t-t*r=t*(1-r) by ring,mul_pow]
  rw [show t^(d+1)-t^(d+1)*(1-r)^(d+1)=t^(d+1)*(1-(1-r)^(d+1)) by ring]
  change t^(d+1)*E+(1-t^(d+1)*Q/q)*E' ≤ E'
  apply (mul_le_mul_iff_right₀ hd).mp
  change q*(t^(d+1)*E+(1-t^(d+1)*Q/q)*E') ≤ q*E'
  have he : q*(t^(d+1)*E+(1-t^(d+1)*Q/q)*E') =
      q*t^(d+1)*E+(q-t^(d+1)*Q)*E' := by
    have hqne : q ≠ 0 := ne_of_gt hd
    field_simp [hqne]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg ht.1 (d+1))
  nlinarith only [hh]

/-- The planar ratio retains the exact width-dependent excess weight.
Zero scale and zero width are included before any cancellation. -/
theorem gap_excess_contraction_two_weighted {K : Set (Point 1)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : Point 1 →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    t^2*(gap K f c r-(1-r)^2*(volume K).toReal)+
      (1-t)*(2/(2-t*r)*(gap K f c (t*r)-(1-t*r)^2*(volume K).toReal)) ≤
      gap K f c (t*r)-(1-t*r)^2*(volume K).toReal := by
  have h := gap_excess_contraction_weighted hK hconv f hf hzero hone hc ht hr
  have htr : t*r ∈ Icc (0 : ℝ) 1 := ⟨mul_nonneg ht.1 hr.1,
    (mul_le_mul_of_nonneg_left hr.2 ht.1).trans (by simpa only [mul_one] using ht.2)⟩
  rw [excessWeight_two t htr] at h
  simpa only [mul_assoc] using h

end Plank.FiniteDimensionalCapWindowScaling
