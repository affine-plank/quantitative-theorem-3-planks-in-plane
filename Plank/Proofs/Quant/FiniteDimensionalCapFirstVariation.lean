/- First variation of the finite cap inequality, in every positive dimension. -/
module
public import Plank.Proofs.Quant.FiniteDimensionalCapWindowScaling
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalCapFirstVariation

open Set MeasureTheory Filter FiniteDimensionalCapWindowScaling
open scoped Topology

/-- A comparison from the left needs only derivatives of the two totals. -/
theorem derivative_lower_bound_of_left_comparison {F H : ℝ → ℝ} {D E : ℝ}
    (hF : HasDerivAt F D 1) (hH : HasDerivAt H E 1) (he : F 1=H 1)
    (hle : ∀ᶠ t in nhdsWithin 1 (Iio 1), F t ≤ H t) : E ≤ D := by
  have hd := (hasDerivAt_iff_tendsto_slope_left_right.mp (hF.sub hH)).1
  have hn : 0 ≤ D-E := ge_of_tendsto hd (by
    filter_upwards [hle, (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[<] 1, t < 1)] with t ht hlt
    rw [slope_def_field]
    change 0 ≤ (F t-H t-(F 1-H 1))/(t-1)
    rw [he, sub_self, sub_zero]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr ht) (sub_nonpos.mpr hlt.le))
  linarith only [hn]

/-- The finite cap comparison differentiates the total covered volume.
Individual windows need not be assumed differentiable. -/
theorem total_window_derivative_lower_bound {d m : ℕ} {K : Set (Point d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : Fin m → Point d →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (hzero : ∀ i, ∃ x ∈ K, f i x=0)
    (hone : ∀ i, ∃ x ∈ K, f i x=1) (c r : Fin m → ℝ)
    (hc : ∀ i, c i ∈ Icc 0 1) (hr : ∀ i, r i ∈ Ioo 0 1) {D : ℝ}
    (hd : HasDerivAt (fun t : ℝ => ∑ i,
      (volume (K ∩ {x | (1-t*r i)*c i ≤ f i x ∧
        f i x ≤ c i+(1-c i)*(t*r i)})).toReal) D 1) :
    (∑ i, (((d+1 : ℕ) : ℝ)*r i*(1-r i)^d)/(1-(1-r i)^(d+1))*
      (volume (K ∩ {x | (1-r i)*c i ≤ f i x ∧
        f i x ≤ c i+(1-c i)*r i})).toReal) ≤ D := by
  let A (i : Fin m) := (volume (K ∩ {x | (1-r i)*c i ≤ f i x ∧
    f i x ≤ c i+(1-c i)*r i})).toReal
  have hq (i) : 0 < 1-(1-r i)^(d+1) := sub_pos.mpr
    (pow_lt_one₀ (sub_pos.mpr (hr i).2).le
      (by linarith only [(hr i).1]) (Nat.succ_ne_zero d))
  have hder (i : Fin m) : HasDerivAt (fun t : ℝ =>
      (1-(1-t*r i)^(d+1))/(1-(1-r i)^(d+1))*A i)
      ((((d+1 : ℕ) : ℝ)*r i*(1-r i)^d)/(1-(1-r i)^(d+1))*A i) 1 := by
    have h₁ := (hasDerivAt_id (1 : ℝ)).mul_const (r i)
    have h₂ := (h₁.const_sub 1).pow (d+1)
    have h₃ := (h₂.const_sub 1).div_const (1-(1-r i)^(d+1))
    convert! h₃.mul_const (A i) using 1
    norm_num
    ring_nf
    simp
  apply derivative_lower_bound_of_left_comparison hd (HasDerivAt.fun_sum fun i _ => hder i)
  · apply Finset.sum_congr rfl
    intro i _
    simp [A, ne_of_gt (hq i)]
  · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ)<1)] with t ht
    apply Finset.sum_le_sum
    intro i _
    have h := window_contraction_ratio hK hconv (f i) (hf i) (hzero i) (hone i)
      (hc i) ⟨ht.1.le,ht.2.le⟩ ⟨(hr i).1.le,(hr i).2.le⟩
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ (hq i)).mpr (by
      simpa only [A, mul_comm] using h)

/-- Shared scalar algebra for a cap balance, whether supplied by derivatives
or directly by a finite comparison at a minimum. -/
theorem margin_from_cap_balance {d m : ℕ} (V B D G P : ℝ)
    (r A : Fin m → ℝ) (hr : ∀ i, r i ∈ Ioo 0 1)
    (hval : G = V-(∑ i, A i)+P)
    (hcap : (∑ i, (((d+1 : ℕ) : ℝ)*r i*(1-r i)^d)/(1-(1-r i)^(d+1))*A i) ≤
      D+((d+1 : ℕ) : ℝ)*V*(B-∑ i, r i)^d*(∑ i, r i)) :
    V*(1-(∑ i, (1-(1-r i)^d))-B*(B-∑ i, r i)^d)+P-D/((d+1 : ℕ) : ℝ)+
      (∑ i, (1-(1-r i)^d)/(1-(1-r i)^(d+1))*
        (V-A i-(1-r i)^(d+1)*V)) ≤ G-V*(B-∑ i, r i)^(d+1) := by
  have hq (i) : 0 < 1-(1-r i)^(d+1) := sub_pos.mpr
    (pow_lt_one₀ (sub_pos.mpr (hr i).2).le
      (by linarith only [(hr i).1]) (Nat.succ_ne_zero d))
  have heq (i) :
      (((d+1 : ℕ) : ℝ)*r i*(1-r i)^d)/(1-(1-r i)^(d+1))*A i =
      ((d+1 : ℕ) : ℝ)*(A i+
        (1-(1-r i)^d)/(1-(1-r i)^(d+1))*(V-A i-(1-r i)^(d+1)*V)-
        V*(1-(1-r i)^d)) := by
    field_simp [ne_of_gt (hq i)]
    simp only [pow_succ]
    ring
  simp_rw [heq] at hcap
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hcap
  have hn : 0 < ((d+1 : ℕ) : ℝ) := by positivity
  have hdiv : ((d+1 : ℕ) : ℝ)*(D/((d+1 : ℕ) : ℝ))=D := by field_simp
  rw [hval]
  apply le_of_mul_le_mul_left (a := ((d+1 : ℕ) : ℝ)) ?_ hn
  rw [pow_succ]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib]
  nlinarith only [hcap,hdiv]

/-- A stationary decomposition of the actual finite window sum retains its
cap surplus in every positive dimension. Only the two total derivatives are
assumed; no section-density objects or individual derivatives are required. -/
theorem stationary_margin_lower_bound {d m : ℕ} {K : Set (Point d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : Fin m → Point d →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (hzero : ∀ i, ∃ x ∈ K, f i x=0)
    (hone : ∀ i, ∃ x ∈ K, f i x=1) (c r : Fin m → ℝ)
    (hc : ∀ i, c i ∈ Icc 0 1) (hr : ∀ i, r i ∈ Ioo 0 1)
    (B D : ℝ) (G P : ℝ → ℝ)
    (hidentity : ∀ᶠ t in 𝓝 (1 : ℝ), G t = (volume K).toReal-
      (∑ i, (volume (K ∩ {x | (1-t*r i)*c i ≤ f i x ∧
        f i x ≤ c i+(1-c i)*(t*r i)})).toReal)+P t)
    (hstationary : HasDerivAt G
      (-((d+1 : ℕ) : ℝ)*(volume K).toReal*(B-∑ i, r i)^d*(∑ i, r i)) 1)
    (hinteraction : HasDerivAt P D 1) :
    (volume K).toReal*(1-(∑ i, (1-(1-r i)^d))-B*(B-∑ i, r i)^d)+P 1-
      D/((d+1 : ℕ) : ℝ)+
      (∑ i, (1-(1-r i)^d)/(1-(1-r i)^(d+1))*
        (gap K (f i) (c i) (r i)-(1-r i)^(d+1)*(volume K).toReal)) ≤
      G 1-(volume K).toReal*(B-∑ i, r i)^(d+1) := by
  let A (i : Fin m) (t : ℝ) := (volume (K ∩
    {x | (1-t*r i)*c i ≤ f i x ∧ f i x ≤ c i+(1-c i)*(t*r i)})).toReal
  have htotal : HasDerivAt (fun t : ℝ => ∑ i, A i t)
      (D+((d+1 : ℕ) : ℝ)*(volume K).toReal*(B-∑ i, r i)^d*(∑ i, r i)) 1 := by
    have h := (hstationary.const_sub (volume K).toReal).add hinteraction
    have he : (fun t : ℝ => ∑ i, A i t) =ᶠ[𝓝 1]
        (fun t => (volume K).toReal-G t+P t) := hidentity.mono (fun t ht => by
      dsimp only [A]
      linarith only [ht])
    convert! h.congr_of_eventuallyEq he using 1
    ring
  have hcap := total_window_derivative_lower_bound hK hconv f hf hzero hone c r hc hr htotal
  have hval := hidentity.self_of_nhds
  have h := margin_from_cap_balance (d := d) (volume K).toReal B D (G 1) (P 1)
    r (fun i => A i 1) hr hval (by simpa only [A,one_mul] using hcap)
  simpa only [gap_eq_sub_window hK,A,one_mul] using h

/-- The planar specialization needs only derivatives of the total gap and
interaction along simultaneous canonical scaling. -/
theorem planar_stationary_margin_lower_bound {m : ℕ} {K : Set (Point 1)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : Fin m → Point 1 →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (hzero : ∀ i, ∃ x ∈ K, f i x=0)
    (hone : ∀ i, ∃ x ∈ K, f i x=1) (c r : Fin m → ℝ)
    (hc : ∀ i, c i ∈ Icc 0 1) (hr : ∀ i, r i ∈ Ioo 0 1)
    (B D : ℝ) (G P : ℝ → ℝ)
    (hidentity : ∀ᶠ t in 𝓝 (1 : ℝ), G t = (volume K).toReal-
      (∑ i, (volume (K ∩ {x | (1-t*r i)*c i ≤ f i x ∧
        f i x ≤ c i+(1-c i)*(t*r i)})).toReal)+P t)
    (hstationary : HasDerivAt G
      (-2*(volume K).toReal*(B-∑ i, r i)*(∑ i, r i)) 1)
    (hinteraction : HasDerivAt P D 1) :
    (volume K).toReal*(1-B)*(1+B-∑ i, r i)+P 1-D/2+
      (∑ i, (gap K (f i) (c i) (r i)-(1-r i)^2*(volume K).toReal)/(2-r i)) ≤
      G 1-(volume K).toReal*(B-∑ i, r i)^2 := by
  have hs : HasDerivAt G
      (-((1+1 : ℕ) : ℝ)*(volume K).toReal*(B-∑ i, r i)^1*(∑ i, r i)) 1 := by
    simpa only [Nat.reduceAdd, Nat.cast_ofNat, pow_one] using hstationary
  have h := stationary_margin_lower_bound hK hconv f hf hzero hone c r hc hr
    B D G P hidentity hs hinteraction
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, pow_one] at h
  have hsimp (i : Fin m) : 1-(1-r i)=r i := by ring
  simp only [hsimp] at h
  have hcoef (i : Fin m) : r i/(1-(1-r i)^2)=1/(2-r i) := by
    rw [show 1-(1-r i)^2=r i*(2-r i) by ring]
    field_simp [ne_of_gt (hr i).1]
  simp_rw [hcoef, div_mul_eq_mul_div, one_mul] at h
  convert h using 1
  ring

/-- The finite cap ratio gives a first-variation inequality whenever the actual
covered volume is differentiable. No section profile is an assumption. -/
theorem window_derivative_lower_bound {d : ℕ} {K : Set (Point d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : Point d →ᵃ[ℝ] ℝ)
    (hf : f.linear ≠ 0) (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c r D : ℝ} (hc : c ∈ Icc 0 1) (hr : r ∈ Ioo 0 1)
    (hd : HasDerivAt (fun s : ℝ =>
      (volume (K ∩ {x | (1-s)*c ≤ f x ∧ f x ≤ c+(1-c)*s})).toReal) D r) :
    ((d+1 : ℕ) : ℝ)*(1-r)^d*
      (volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal ≤
        (1-(1-r)^(d+1))*D := by
  have hq : 0 < 1-(1-r)^(d+1) := sub_pos.mpr
    (pow_lt_one₀ (sub_pos.mpr hr.2).le (by linarith only [hr.1]) (Nat.succ_ne_zero d))
  have hp : HasDerivAt (fun s : ℝ => 1-(1-s)^(d+1))
      (((d+1 : ℕ) : ℝ)*(1-r)^d) r := by
    convert! (((hasDerivAt_id r).const_sub 1).pow (d+1)).const_sub 1 using 1
    norm_num
  have hratio := hd.fun_div hp hq.ne'
  have hm := window_volume_ratio_monotone hK hconv f hf hzero hone hc
  have hh := hm.derivWithin_nonneg (x := r)
  have hn : Ioc (0 : ℝ) 1 ∈ nhds r :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hr) Ioo_subset_Ioc_self
  rw [derivWithin_of_mem_nhds hn, hratio.deriv] at hh
  have hnum := (le_div_iff₀ (sq_pos_of_pos hq)).mp hh
  nlinarith only [hnum]

/-- In the plane, the first variation retains the full width-weighted actual
one-plank surplus. The hypothesis is the derivative of covered area itself. -/
theorem planar_balance_with_excess {K : Set (Point 1)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : Point 1 →ᵃ[ℝ] ℝ)
    (hf : f.linear ≠ 0) (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c r D : ℝ} (hc : c ∈ Icc 0 1) (hr : r ∈ Ioo 0 1)
    (hd : HasDerivAt (fun s : ℝ =>
      (volume (K ∩ {x | (1-s)*c ≤ f x ∧ f x ≤ c+(1-c)*s})).toReal) D r) :
    2*(volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal+
      2/(2-r)*(gap K f c r-(1-r)^2*(volume K).toReal) ≤
        r*D+2*r*(volume K).toReal := by
  have h := window_derivative_lower_bound hK hconv f hf hzero hone hc hr hd
  norm_num only [Nat.cast_add, Nat.cast_one, pow_one] at h
  rw [gap_eq_sub_window hK]
  have hden : 0 < 2-r := by linarith only [hr.2]
  apply le_of_mul_le_mul_left (a := 2-r) ?_ hden
  have he (E : ℝ) : (2-r)*(2/(2-r)*E)=2*E := by field_simp
  rw [mul_add,he]
  nlinarith only [h]

end Plank.FiniteDimensionalCapFirstVariation
