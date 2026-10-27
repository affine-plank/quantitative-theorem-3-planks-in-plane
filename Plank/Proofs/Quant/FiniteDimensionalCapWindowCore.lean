/- Direct cap and canonical-window contraction from Brunn–Minkowski in every positive dimension. -/
module

public import ResearchFormalized.BrunnMinkowski
public import Plank.Proofs.Quant.FiniteDimensionalAffineGeometry
public import Mathlib.Analysis.Convex.Function
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

def volumeRoot (A : Set (Point d)) : ℝ :=
  (volume A).toReal ^ (((d+1 : ℕ) : ℝ)⁻¹)

theorem volumeRoot_nonneg (A : Set (Point d)) : 0 ≤ volumeRoot A :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

theorem volumeRoot_pow (A : Set (Point d)) :
    volumeRoot A ^ (d+1) = (volume A).toReal :=
  Real.rpow_inv_natCast_pow ENNReal.toReal_nonneg (Nat.succ_ne_zero d)

theorem volumeRoot_mono {A B : Set (Point d)} (hB : IsCompact B) (h : A ⊆ B) :
    volumeRoot A ≤ volumeRoot B :=
  Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono hB.measure_ne_top (measure_mono h)) (by positivity)

/-- Brunn--Minkowski for actual real volumes in every positive dimension. -/
theorem volumeRoot_add {A B : Set (Point d)}
    (hA : IsCompact A) (hB : IsCompact B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    volumeRoot A + volumeRoot B ≤ volumeRoot (A+B) := by
  simpa only [volumeRoot, measureReal_def, Fintype.card_fin] using
    ResearchFormalized.pi_brunnMinkowski (by simp) hA hB hneA hneB

theorem volumeRoot_smul (A : Set (Point d)) (a : ℝ) (ha : 0 ≤ a) :
    volumeRoot (a • A) = a * volumeRoot A := by
  unfold volumeRoot
  rw [volume.addHaar_smul_of_nonneg ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg ha _)]
  simp only [Module.finrank_pi, Fintype.card_fin]
  rw [Real.mul_rpow (pow_nonneg ha _) ENNReal.toReal_nonneg,
    Real.pow_rpow_inv_natCast ha (Nat.succ_ne_zero d)]

theorem volumeRoot_smul_add {A B : Set (Point d)}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * volumeRoot A + b * volumeRoot B ≤ volumeRoot (a • A+b • B) := by
  simpa only [volumeRoot_smul A a ha, volumeRoot_smul B b hb] using
    volumeRoot_add (hA.smul a) (hB.smul b)
      (hneA.image (fun x => a • x)) (hneB.image (fun x => b • x))

def cap (K : Set (Point d)) (f : Point d →ᵃ[ℝ] ℝ) (u : ℝ) : Set (Point d) :=
  K ∩ {x | f x ≤ u}

theorem compact_cap {K : Set (Point d)} (hK : IsCompact K)
    (f : Point d →ᵃ[ℝ] ℝ) (u : ℝ) : IsCompact (cap K f u) :=
  hK.inter_right (isClosed_le (continuous_form f) continuous_const)

theorem root_cap_mix {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Point d →ᵃ[ℝ] ℝ) {u v a b : ℝ}
    (hu : (cap K f u).Nonempty) (hv : (cap K f v).Nonempty)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a*volumeRoot (cap K f u)+b*volumeRoot (cap K f v) ≤
      volumeRoot (cap K f (a*u+b*v)) := by
  have hsub : a • cap K f u+b • cap K f v ⊆ cap K f (a*u+b*v) := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
    refine ⟨hc hx.1 hy.1 ha hb hab,?_⟩
    change f (a • x+b • y) ≤ a*u+b*v
    rw [Convex.combo_affine_apply hab]
    exact add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
      (mul_le_mul_of_nonneg_left hy.2 hb)
  exact (volumeRoot_smul_add (compact_cap hK f u) (compact_cap hK f v)
    hu hv a b ha hb).trans (volumeRoot_mono (compact_cap hK f _) hsub)

theorem root_cap_contract {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Point d →ᵃ[ℝ] ℝ) (hzero : ∃ x ∈ K, f x=0)
    {c r : ℝ} (hc0 : 0 ≤ c) (hr : r ∈ Icc 0 1) :
    (1-r)*volumeRoot (cap K f c) ≤ volumeRoot (cap K f ((1-r)*c)) := by
  obtain ⟨x,hx,hfx⟩ := hzero
  have h := root_cap_mix hK hc f
    (show (cap K f c).Nonempty from ⟨x,hx,hfx.le.trans hc0⟩)
    (show (cap K f 0).Nonempty from ⟨x,hx,hfx.le⟩)
    (sub_nonneg.mpr hr.2) hr.1 (by ring)
  simp only [mul_zero,add_zero] at h
  exact (le_add_of_nonneg_right (mul_nonneg hr.1 (volumeRoot_nonneg _))).trans h

/-- The increment of a natural power is monotone on the nonnegative half-line,
by the standard difference-of-powers factorization and termwise monotonicity. -/
theorem pow_increment_mono {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (n : ℕ) : (a+c)^n-a^n ≤ (b+c)^n-b^n := by
  rw [← geom_sum₂_mul, ← geom_sum₂_mul]
  simp only [add_sub_cancel_left]
  gcongr
  exact pow_nonneg (add_nonneg (ha.trans hab) hc) _

/-- Actual cap-volume contraction in dimension `d+1`. -/
theorem cap_contraction {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : Point d →ᵃ[ℝ] ℝ) (hzero : ∃ x ∈ K, f x=0)
    {c t r : ℝ} (hc0 : 0 ≤ c) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    t^(d+1)*(volume (cap K f ((1-r)*c))).toReal+
      ((1-t*r)^(d+1)-t^(d+1)*(1-r)^(d+1))*(volume (cap K f c)).toReal ≤
      (volume (cap K f ((1-t*r)*c))).toReal := by
  let u := volumeRoot (cap K f c)
  let v := volumeRoot (cap K f ((1-r)*c))
  have hu : 0 ≤ u := volumeRoot_nonneg _
  have hl := root_cap_contract hK hc f hzero hc0 hr
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
  have hi := pow_increment_mono
    (mul_nonneg ht.1 (mul_nonneg (sub_nonneg.mpr hr.2) hu))
    (mul_le_mul_of_nonneg_left hl ht.1)
    (mul_nonneg (sub_nonneg.mpr ht.2) hu) (d+1)
  change (t*((1-r)*u)+(1-t)*u)^(d+1)-(t*((1-r)*u))^(d+1) ≤
    (t*v+(1-t)*u)^(d+1)-(t*v)^(d+1) at hi
  rw [show t*((1-r)*u)+(1-t)*u=(1-t*r)*u by ring,
    add_comm (t*v) ((1-t)*u)] at hi
  simp only [mul_pow] at hi
  dsimp only [u,v] at hp hi
  simp only [volumeRoot_pow] at hp hi
  nlinarith only [hp,hi]

def reflect (f : Point d →ᵃ[ℝ] ℝ) : Point d →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (Point d) 1-f

@[simp] theorem reflect_apply (f : Point d →ᵃ[ℝ] ℝ) (x : Point d) :
    reflect f x = 1-f x := rfl

/-- The two closed caps partition the body up to their null common level. -/
theorem cap_partition {K : Set (Point d)} (hK : IsCompact K)
    (f : (Point d) →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ) :
    (volume (cap K f c)).toReal+
      (volume (cap K (reflect f) (1-c))).toReal = (volume K).toReal := by
  have hu : cap K f c ∪ cap K (reflect f) (1-c) = K := by
    ext x
    simp only [cap, mem_union, mem_inter_iff, mem_ofPred_eq, reflect_apply,
      sub_le_sub_iff_left, ← and_or_left, le_total, and_true]
  have hz : volume (cap K f c ∩ cap K (reflect f) (1-c)) = 0 := by
    apply measure_mono_null _ (measure_level_zero f hf c)
    intro x hx
    change f x=c
    exact le_antisymm hx.1.2 (by
      simpa only [mem_ofPred_eq, reflect_apply, sub_le_sub_iff_left] using hx.2.2)
  have h := measureReal_union_add_inter (μ := volume) (s := cap K f c)
    (compact_cap hK (reflect f) (1-c)).measurableSet
    (compact_cap hK f c).measure_ne_top (compact_cap hK (reflect f) (1-c)).measure_ne_top
  change (volume (cap K f c ∪ cap K (reflect f) (1-c))).toReal+
    (volume (cap K f c ∩ cap K (reflect f) (1-c))).toReal =
    (volume (cap K f c)).toReal+(volume (cap K (reflect f) (1-c))).toReal at h
  simpa only [hu,hz,ENNReal.toReal_zero,add_zero] using h.symm

/-- Deleting a window leaves precisely its two exterior caps in volume. -/
theorem cap_window_partition {K : Set (Point d)} (hK : IsCompact K)
    (f : (Point d) →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) {lo hi : ℝ} (ho : lo ≤ hi) :
    (volume (cap K f lo)).toReal+
      (volume (cap K (reflect f) (1-hi))).toReal+
      (volume (K ∩ {x | lo ≤ f x ∧ f x ≤ hi})).toReal = (volume K).toReal := by
  let W := K ∩ {x | lo ≤ f x ∧ f x ≤ hi}
  have hm : IsCompact W := hK.inter_right
    ((isClosed_le continuous_const (continuous_form f)).inter
      (isClosed_le (continuous_form f) continuous_const))
  have hu : cap K f lo ∪ W = cap K f hi := by
    change (K ∩ f ⁻¹' Iic lo) ∪ (K ∩ f ⁻¹' Icc lo hi) = K ∩ f ⁻¹' Iic hi
    rw [← inter_union_distrib_left, ← preimage_union, Iic_union_Icc_eq_Iic ho]
  have hz : volume (cap K f lo ∩ W) = 0 := by
    apply measure_mono_null _ (measure_level_zero f hf lo)
    intro x hx
    exact le_antisymm hx.1.2 hx.2.2.1
  have h := measureReal_union_add_inter (μ := volume) (s := cap K f lo)
    hm.measurableSet (compact_cap hK f lo).measure_ne_top hm.measure_ne_top
  change (volume (cap K f lo ∪ W)).toReal+(volume (cap K f lo ∩ W)).toReal =
    (volume (cap K f lo)).toReal+(volume W).toReal at h
  rw [hu,hz,ENNReal.toReal_zero,add_zero] at h
  linarith only [h,cap_partition hK f hf hi]

/-- Summing the two cap contractions gives covered-volume scaling directly.
Both support points are explicit; no surplus refinement is needed. -/
theorem window_contraction {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : (Point d) →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hzero : ∃ x ∈ K, f x=0) (hone : ∃ x ∈ K, f x=1)
    {c t r : ℝ} (hc : c ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (hr : r ∈ Icc 0 1) :
    (volume (K ∩ {x | (1-t*r)*c ≤ f x ∧ f x ≤ c+(1-c)*(t*r)})).toReal ≤
      t^(d+1)*(volume (K ∩ {x | (1-r)*c ≤ f x ∧ f x ≤ c+(1-c)*r})).toReal+
        (1-(1-t*r)^(d+1)-t^(d+1)*(1-(1-r)^(d+1)))*(volume K).toReal := by
  have hgzero : ∃ x ∈ K, reflect f x=0 := by
    obtain ⟨x,hx,hfx⟩ := hone
    exact ⟨x,hx,by simp only [reflect_apply,hfx,sub_self]⟩
  have hm := cap_contraction hK hconv f hzero hc.1 ht hr
  have hp := cap_contraction hK hconv (reflect f) hgzero
    (sub_nonneg.mpr hc.2) ht hr
  have houter := cap_window_partition hK f hf
    (show (1-r)*c ≤ c+(1-c)*r by nlinarith only [hr.1])
  have hinner := cap_window_partition hK f hf
    (show (1-t*r)*c ≤ c+(1-c)*(t*r) by nlinarith only [mul_nonneg ht.1 hr.1])
  rw [show 1-(c+(1-c)*r)=(1-r)*(1-c) by ring] at houter
  rw [show 1-(c+(1-c)*(t*r))=(1-t*r)*(1-c) by ring] at hinner
  linear_combination hm + hp + hinner - t^(d+1)*houter -
    ((1-t*r)^(d+1)-t^(d+1)*(1-r)^(d+1))*(cap_partition hK f hf c)

end Plank.FiniteDimensionalCapWindowScaling
