/- Affine normalization and clipping of actual plank windows in every positive dimension. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalNormalizedDomain
public import Plank.Proofs.Quant.FiniteDimensionalAffineGeometry
public import Mathlib.Topology.UnitInterval

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalNormalization

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalInductionBoundary FiniteDimensionalParameterDomain

variable {d : ℕ}

/-- Clamp an endpoint to the normalized support interval. -/
def clip (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clip_bounds (x : ℝ) : 0 ≤ clip x ∧ clip x ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem monotone_clip : Monotone clip := by
  intro x y h
  exact max_le_max le_rfl (min_le_min le_rfl h)

theorem clip_sub_le {lo hi : ℝ} (h : lo ≤ hi) : clip hi - clip lo ≤ hi-lo := by
  calc
    _ ≤ |clip hi - clip lo| := le_abs_self _
    _ ≤ |hi - lo| := Set.abs_projIcc_sub_projIcc
      (a := (0 : ℝ)) (b := 1) (c := hi) (d := lo) zero_le_one
    _ = hi - lo := abs_of_nonneg (sub_nonneg.mpr h)

/-- At a point strictly inside the support interval, clipping does not
change membership in the plank. Support levels are handled by nullity below. -/
theorem mem_clipped_iff {lo hi z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    (clip lo ≤ z ∧ z ≤ clip hi) ↔ (lo ≤ z ∧ z ≤ hi) := by
  simp only [clip, max_le_iff, min_le_iff, le_max_iff, le_min_iff,
    not_le.mpr hz, not_le.mpr hz1, hz.le, hz1.le, false_or, true_and]

def clipEndpoints {m : ℕ} (p : Endpoints (Fin m)) : Endpoints (Fin m) :=
  (fun i => clip (p.1 i), fun i => clip (p.2 i))

theorem budget_clip_le {m : ℕ} {K : Set (Point d)} (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < Body.width K (f i)) (p : Endpoints (Fin m))
    (horder : ∀ i, p.1 i ≤ p.2 i) :
    budget K f (clipEndpoints p) ≤ budget K f p := by
  apply Finset.sum_le_sum
  intro i _
  exact (div_le_div_iff_of_pos_right (hW i)).mpr (clip_sub_le (horder i))

theorem clipEndpoints_mem_domain {m : ℕ} {K : Set (Point d)}
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (p : Endpoints (Fin m)) (horder : ∀ i, p.1 i ≤ p.2 i) (hbudget : budget K f p ≤ 1) :
    clipEndpoints p ∈ domain K f := by
  exact ⟨fun i => ⟨(clip_bounds (p.1 i)).1, monotone_clip (horder i),
    (clip_bounds (p.2 i)).2⟩, (budget_clip_le f hW p horder).trans hbudget⟩

/-- Clipping preserves the actual gap volume. It can change the closed covered
set on support hyperplanes, so the two gaps agree almost everywhere. -/
theorem gapVolume_clip {m : ℕ} {K : Set (Point d)} (hne : K.Nonempty)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) (p : Endpoints (Fin m)) :
    gapVolume K f (clipEndpoints p) = gapVolume K f p := by
  classical
  let bad : Set (Point d) := ⋃ i, {x | f i x = 0} ∪ {x | f i x = 1}
  have hbad : volume bad = 0 := measure_iUnion_null fun i =>
    measure_union_null
      (measure_level_zero (f i) (linear_ne_zero_of_width_pos hne (f i) (hW i)) 0)
      (measure_level_zero (f i) (linear_ne_zero_of_width_pos hne (f i) (hW i)) 1)
  have hequiv (x : (Point d)) (hx : x ∈ K) (hb : x ∉ bad) (i : Fin m) :
      (clip (p.1 i) ≤ f i x ∧ f i x ≤ clip (p.2 i)) ↔
        (p.1 i ≤ f i x ∧ f i x ≤ p.2 i) := by
    have hzero : f i x ≠ 0 := fun h => hb (mem_iUnion.mpr ⟨i, Or.inl h⟩)
    have hone : f i x ≠ 1 := fun h => hb (mem_iUnion.mpr ⟨i, Or.inr h⟩)
    exact mem_clipped_iff (lt_of_le_of_ne (hnorm i x hx).1 hzero.symm)
      (lt_of_le_of_ne (hnorm i x hx).2 hone)
  unfold gapVolume clipEndpoints
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hae : ∀ᵐ x ∂volume, x ∉ bad := compl_mem_ae_iff.mpr hbad
  filter_upwards [hae] with x hx
  by_cases hxK : x ∈ K
  · simp only [mem_sdiff, mem_iUnion, mem_ofPred_eq, hxK, true_and]
    exact propext (not_congr (exists_congr (fun i => hequiv x hxK hx i)))
  · simp only [mem_sdiff, hxK, false_and]

/-- The normalized domain version of the full actual-volume target. It retains
arbitrary compact convex bodies and imposes no polygon or area-chart premise. -/
def UnitDomainBound (d m : ℕ) : Prop :=
  ∀ (K : Set (Point d)), IsCompact K → Convex ℝ K → K.Nonempty →
    ∀ (f : Fin m → (Point d) →ᵃ[ℝ] ℝ),
      (∀ i, Body.width K (f i) = 1) →
      (∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) →
      ∀ p ∈ domain K f,
        (max 0 (1-budget K f p))^(d+1) * (volume K).toReal ≤ gapVolume K f p

/-- Normalizing and clipping loses no part of the original theorem. In
particular, planks outside the support window, zero-width planks and bodies
of zero volume are included in this equivalence. -/
theorem sharpBound_iff_unitDomainBound (m : ℕ) :
    SharpBound d m ↔ UnitDomainBound d m := by
  constructor
  · intro h K hK hconv hne f hunit _ p hp
    exact h K hK hconv hne f p.1 p.2 (fun i => (hp.1 i).2.1)
      (fun i => by rw [hunit]; norm_num)
  · intro h K hK hconv hne f lo hi horder hW
    change (max 0 (1-budget K f (lo, hi)))^(d+1) * (volume K).toReal ≤
      gapVolume K f (lo, hi)
    by_cases hR : budget K f (lo, hi) ≤ 1
    · obtain ⟨g, p, hunit, hnorm, hordered, hbudget, hgap⟩ :=
        normalize_data hK hne f lo hi horder hW
      have hgW : ∀ i, 0 < Body.width K (g i) := fun i => by rw [hunit]; norm_num
      have hRp : budget K g p ≤ 1 := by rwa [hbudget]
      have hmem := clipEndpoints_mem_domain g hgW p hordered hRp
      have hdeficit : max 0 (1-budget K g p) ≤
          max 0 (1-budget K g (clipEndpoints p)) :=
        max_le_max le_rfl (sub_le_sub_left (budget_clip_le g hgW p hordered) 1)
      calc
        (max 0 (1-budget K f (lo, hi)))^(d+1) * (volume K).toReal =
            (max 0 (1-budget K g p))^(d+1) * (volume K).toReal := by rw [hbudget]
        _ ≤ (max 0 (1-budget K g (clipEndpoints p)))^(d+1) * (volume K).toReal :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (le_max_left _ _) hdeficit (d+1))
            ENNReal.toReal_nonneg
        _ ≤ gapVolume K g (clipEndpoints p) := h K hK hconv hne g hunit hnorm _ hmem
        _ = gapVolume K f (lo, hi) := (gapVolume_clip hne g hgW hnorm p).trans hgap
    · have hzero : max 0 (1-budget K f (lo, hi)) = 0 :=
        max_eq_left (sub_nonpos.mpr (le_of_not_ge hR))
      rw [hzero, zero_pow (Nat.succ_ne_zero d), zero_mul]
      exact ENNReal.toReal_nonneg

/-- Failure of the full statement already gives a positive-volume normalized
counterexample. This is an actual body and actual plank family, not abstract
volume functions satisfying unproved geometric assumptions. -/
theorem exists_normalized_counterexample {m : ℕ} (h : ¬ SharpBound d m) :
    ∃ (K : Set (Point d)), IsCompact K ∧ Convex ℝ K ∧ K.Nonempty ∧
      0 < (volume K).toReal ∧
      ∃ (f : Fin m → (Point d) →ᵃ[ℝ] ℝ),
        (∀ i, Body.width K (f i) = 1) ∧
        (∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1) ∧
        ∃ p ∈ domain K f,
          gapVolume K f p < (max 0 (1-budget K f p))^(d+1) * (volume K).toReal := by
  classical
  have hn : ¬ UnitDomainBound d m := fun hu => h ((sharpBound_iff_unitDomainBound m).mpr hu)
  unfold UnitDomainBound at hn
  push Not at hn
  obtain ⟨K, hK, hconv, hne, f, hunit, hnorm, p, hp, hbad⟩ := hn
  have hV : 0 < (volume K).toReal := by
    by_contra hv
    have hz : (volume K).toReal = 0 := le_antisymm (le_of_not_gt hv) ENNReal.toReal_nonneg
    rw [hz, mul_zero] at hbad
    exact (not_lt_of_ge (show 0 ≤ gapVolume K f p from ENNReal.toReal_nonneg)) hbad
  exact ⟨K, hK, hconv, hne, hV, f, hunit, hnorm, p, hp, hbad⟩

end Plank.FiniteDimensionalNormalization

#print axioms Plank.FiniteDimensionalNormalization.normalize_data_with_formula
#print axioms Plank.FiniteDimensionalNormalization.sharpBound_iff_unitDomainBound
#print axioms Plank.FiniteDimensionalNormalization.exists_normalized_counterexample
