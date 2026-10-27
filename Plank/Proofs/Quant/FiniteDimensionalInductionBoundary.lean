/- Actual homothetic bodies and the dimension-power induction boundary. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalCapWindowCore
public import Plank.Proofs.AffineWidthCore
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalInductionBoundary

open Set MeasureTheory FiniteDimensionalCapWindowScaling
open scoped BigOperators

variable {d : ℕ}

/-- The sharp actual-volume bound for every compact convex body and `m`
ordered affine planks in dimension `d+1`. This defines the induction input. -/
def SharpBound (d m : ℕ) : Prop :=
  ∀ (K : Set (Point d)), IsCompact K → Convex ℝ K → K.Nonempty →
    ∀ (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ),
      (∀ i, lo i ≤ hi i) → (∀ i, 0 < Body.width K (f i)) →
      (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^(d+1) *
        (volume K).toReal ≤
        (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal

/-- Evaluation at an actual homothetic point. -/
theorem form_homothety (f : (Point d) →ᵃ[ℝ] ℝ) (z : (Point d)) (q : ℝ) (x : (Point d)) :
    f (AffineMap.homothety z q x) = (1-q)*f z + q*f x := by
  rw [AffineMap.homothety_eq_lineMap]
  simpa only [AffineMap.lineMap_apply_ring] using f.apply_lineMap z x q

/-- Homotheties scale the actual directional range of every affine form. -/
theorem width_homothety {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (f : (Point d) →ᵃ[ℝ] ℝ) (z : (Point d)) (q : ℝ) (hq : 0 ≤ q) :
    Body.width (AffineMap.homothety z q '' K) f = q * Body.width K f := by
  obtain ⟨a, ha, b, hb, hmax, hmin⟩ := Body.exists_realisers hK hne (continuous_form f)
  have hold : Body.width K f = f a - f b :=
    Body.width_eq_of_realisers ha hb hmax hmin
  have hnew : Body.width (AffineMap.homothety z q '' K) f =
      f (AffineMap.homothety z q a) - f (AffineMap.homothety z q b) := by
    refine Body.width_eq_of_realisers (K := AffineMap.homothety z q '' K) (f := f)
      (a := AffineMap.homothety z q a) (b := AffineMap.homothety z q b)
      ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [form_homothety, form_homothety]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmax x hx) hq)
    · rintro _ ⟨x, hx, rfl⟩
      rw [form_homothety, form_homothety]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmin x hx) hq)
  rw [hnew, hold, form_homothety, form_homothety]
  ring

/-- Positive homotheties scale actual volume by the dimension power. -/
theorem volume_homothety (K : Set (Point d)) (z : Point d) (q : ℝ) (hq : 0 ≤ q) :
    (volume (AffineMap.homothety z q '' K)).toReal = q^(d+1) * (volume K).toReal := by
  rw [volume.addHaar_image_homothety, ENNReal.toReal_mul]
  simp only [Module.finrank_pi, Fintype.card_fin]
  rw [abs_of_nonneg (pow_nonneg hq _), ENNReal.toReal_ofReal (pow_nonneg hq _)]

/-- Contracting a convex body toward one of its points stays inside the body. -/
theorem homothety_subset {K : Set (Point d)} (hconv : Convex ℝ K) {z : (Point d)}
    (hz : z ∈ K) {q : ℝ} (hq : q ∈ Icc 0 1) :
    AffineMap.homothety z q '' K ⊆ K := by
  rintro _ ⟨x, hx, rfl⟩
  rw [AffineMap.homothety_eq_lineMap]
  exact hconv.lineMap_mem hz hx hq

/-- A zero-width affine plank can be deleted without changing actual gap volume. -/
theorem volume_delete_zero_width (K U : Set (Point d)) (f : (Point d) →ᵃ[ℝ] ℝ)
    (hf : f.linear ≠ 0) (c : ℝ) :
    (volume (K \ ({x | c ≤ f x ∧ f x ≤ c} ∪ U))).toReal =
      (volume (K \ U)).toReal := by
  have hband : {x | c ≤ f x ∧ f x ≤ c} = {x | f x = c} := by
    ext x
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
  have hset : K \ ({x | f x = c} ∪ U) = (K \ U) \ {x | f x = c} := by
    ext x
    simp only [mem_sdiff, mem_union, not_or]
    tauto
  rw [hband, hset, measure_sdiff_null (measure_level_zero f hf c)]

/-- A sub-body lying on the upper side of an extra plank contributes all of
its remaining gap volume. Its common boundary hyperplane has zero volume. -/
theorem volume_gap_mono_beyond {K C U : Set (Point d)} (hK : IsCompact K)
    (hCK : C ⊆ K) (f : (Point d) →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (lo hi : ℝ)
    (hbeyond : ∀ x ∈ C, hi ≤ f x) :
    (volume (C \ U)).toReal ≤
      (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪ U))).toReal := by
  have hmeasure : volume (C \ U) ≤ volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪ U)) := by
    calc
      volume (C \ U) = volume ((C \ U) \ {x | f x = hi}) :=
        (measure_sdiff_null (measure_level_zero f hf hi)).symm
      _ ≤ volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪ U)) := by
        apply measure_mono
        intro x hx
        refine ⟨hCK hx.1.1, ?_⟩
        rintro (hband | hU)
        · exact hx.2 (le_antisymm hband.2 (hbeyond x hx.1.1))
        · exact hx.1.2 hU
  exact ENNReal.toReal_mono
    (ne_top_of_le_ne_top hK.measure_ne_top (measure_mono sdiff_subset)) hmeasure

/-- The lower-support boundary step for actual affine planks. Assuming the
full theorem for `m` planks on every body, an additional plank whose lower
endpoint is at or below the body's minimum satisfies the sharp bound.
The homothetic body's volume, ranges and containment are proved here. -/
theorem bound_extra_lower_support {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (g : Fin m → (Point d) →ᵃ[ℝ] ℝ) (l u : Fin m → ℝ)
    (horder : ∀ i, l i ≤ u i) (hWg : ∀ i, 0 < Body.width K (g i))
    (f : (Point d) →ᵃ[ℝ] ℝ) (lo hi : ℝ) (horderf : lo ≤ hi)
    (hWf : 0 < Body.width K f) (hlower : ∀ x ∈ K, lo ≤ f x) :
    (max 0 (1 - (hi-lo)/Body.width K f - ∑ i, (u i-l i)/Body.width K (g i)))^(d+1) *
        (volume K).toReal ≤
      (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪
        ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal := by
  let r := (hi-lo)/Body.width K f
  let S := ∑ i, (u i-l i)/Body.width K (g i)
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr horderf) hWf.le
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ =>
    div_nonneg (sub_nonneg.mpr (horder i)) (hWg i).le
  change (max 0 (1-r-S))^(d+1) * (volume K).toReal ≤ _
  by_cases hsmall : r + S < 1
  · let q := 1-r
    have hq : 0 < q := by dsimp [q]; linarith only [hsmall, hS]
    have hq1 : q ≤ 1 := by dsimp [q]; linarith only [hr]
    have hmargin : 0 ≤ 1-r-S := by linarith only [hsmall]
    have hmargin' : 0 ≤ 1-S/q := by
      rw [sub_nonneg, div_le_one hq]
      dsimp [q]
      linarith only [hsmall]
    obtain ⟨a, ha, b, hb, hmax, hmin⟩ := Body.exists_realisers hK hne (continuous_form f)
    have hspan : Body.width K f = f a - f b :=
      Body.width_eq_of_realisers ha hb hmax hmin
    have hpaid : r * (f a - f b) = hi-lo := by
      rw [← hspan]
      exact div_mul_cancel₀ _ hWf.ne'
    let C := AffineMap.homothety a q '' K
    have hC : IsCompact C := hK.image (AffineMap.homothety_continuous a q)
    have hCconv : Convex ℝ C := Convex.affine_image (AffineMap.homothety a q) hconv
    have hCne : C.Nonempty := hne.image (AffineMap.homothety a q)
    have hCK : C ⊆ K := homothety_subset hconv ha ⟨hq.le, hq1⟩
    have hscale (i : Fin m) : Body.width C (g i) = q * Body.width K (g i) :=
      width_homothety hK hne (g i) a q hq.le
    have hCW (i : Fin m) : 0 < Body.width C (g i) := by
      rw [hscale]
      exact mul_pos hq (hWg i)
    have hbeyond : ∀ x ∈ C, hi ≤ f x := by
      rintro _ ⟨x, hx, rfl⟩
      rw [form_homothety]
      have hpart := mul_le_mul_of_nonneg_left (hmin x hx) hq.le
      have hlow := hlower b hb
      dsimp only [q] at hpart ⊢
      nlinarith only [hpaid, hpart, hlow]
    have hsum : (∑ i, (u i-l i)/Body.width C (g i)) = S/q := by
      dsimp only [S]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [hscale]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    have harea : (volume C).toReal = q^(d+1) * (volume K).toReal := volume_homothety K a q hq.le
    have hprev := hm C hC hCconv hCne g l u horder hCW
    rw [hsum, harea] at hprev
    calc
      (max 0 (1-r-S))^(d+1) * (volume K).toReal =
          (max 0 (1-S/q))^(d+1) * (q^(d+1) * (volume K).toReal) := by
        rw [max_eq_right hmargin, max_eq_right hmargin']
        change (q-S)^(d+1) * (volume K).toReal = _
        rw [← mul_assoc,← mul_pow]
        congr 1
        field_simp [hq.ne']
      _ ≤ (volume (C \ ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i})).toReal := hprev
      _ ≤ (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪
          ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal :=
        volume_gap_mono_beyond hK hCK f (Body.linear_ne_zero_of_width_pos hne f hWf)
          lo hi hbeyond
  · have hnonpos : 1-r-S ≤ 0 := by linarith only [hsmall]
    rw [max_eq_left hnonpos, zero_pow (Nat.succ_ne_zero d), zero_mul]
    exact ENNReal.toReal_nonneg

/-- The upper-support case is the lower-support construction with the extra
functional reversed. All other physical planks stay fixed. -/
theorem bound_extra_upper_support {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (g : Fin m → (Point d) →ᵃ[ℝ] ℝ) (l u : Fin m → ℝ)
    (horder : ∀ i, l i ≤ u i) (hWg : ∀ i, 0 < Body.width K (g i))
    (f : (Point d) →ᵃ[ℝ] ℝ) (lo hi : ℝ) (horderf : lo ≤ hi)
    (hWf : 0 < Body.width K f) (hupper : ∀ x ∈ K, f x ≤ hi) :
    (max 0 (1 - (hi-lo)/Body.width K f - ∑ i, (u i-l i)/Body.width K (g i)))^(d+1) *
        (volume K).toReal ≤
      (volume (K \ ({x | lo ≤ f x ∧ f x ≤ hi} ∪
        ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal := by
  have hrange : Body.width K (-f) = Body.width K f :=
    Body.width_neg hK hne (continuous_form f)
  have h := bound_extra_lower_support hm hK hconv hne g l u horder hWg
    (-f) (-hi) (-lo) (neg_le_neg horderf) (by rw [hrange]; exact hWf)
    (fun x hx => by simpa using neg_le_neg (hupper x hx))
  have hset : {x | -hi ≤ (-f) x ∧ (-f) x ≤ -lo} = {x | lo ≤ f x ∧ f x ≤ hi} := by
    ext x
    change (-hi ≤ -f x ∧ -f x ≤ -lo) ↔ (lo ≤ f x ∧ f x ≤ hi)
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hnum : -lo - -hi = hi-lo := by ring
  rw [hset, hnum, hrange] at h
  exact h

/-- The zero-width boundary case follows by deleting the null extra plank
and applying the actual-volume induction hypothesis. -/
theorem bound_extra_zero_width {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (g : Fin m → (Point d) →ᵃ[ℝ] ℝ) (l u : Fin m → ℝ)
    (horder : ∀ i, l i ≤ u i) (hWg : ∀ i, 0 < Body.width K (g i))
    (f : (Point d) →ᵃ[ℝ] ℝ) (c : ℝ) (hWf : 0 < Body.width K f) :
    (max 0 (1 - ∑ i, (u i-l i)/Body.width K (g i)))^(d+1) * (volume K).toReal ≤
      (volume (K \ ({x | c ≤ f x ∧ f x ≤ c} ∪
        ⋃ i, {x | l i ≤ g i x ∧ g i x ≤ u i}))).toReal := by
  rw [volume_delete_zero_width K _ f (Body.linear_ne_zero_of_width_pos hne f hWf) c]
  exact hm K hK hconv hne g l u horder hWg

/-- The boundary estimate in the final theorem's indexing convention,
when the distinguished plank is indexed by zero. -/
theorem bound_at_zero_index {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ) (lo hi : Fin (m+1) → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < Body.width K (f i))
    (hface : lo 0 = hi 0 ∨ (∀ x ∈ K, lo 0 ≤ f 0 x) ∨ (∀ x ∈ K, f 0 x ≤ hi 0)) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^(d+1) * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal := by
  have hset : (⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) =
      {x | lo 0 ≤ f 0 x ∧ f 0 x ≤ hi 0} ∪
        ⋃ i : Fin m, {x | lo i.succ ≤ f i.succ x ∧ f i.succ x ≤ hi i.succ} := by
    ext x
    simp only [mem_iUnion, mem_union, Fin.exists_fin_succ]
  rw [hset, Fin.sum_univ_succ, sub_add_eq_sub_sub]
  rcases hface with hzero | hlower | hupper
  · simpa only [hzero, sub_self, zero_div, sub_zero] using
      bound_extra_zero_width hm hK hconv hne (fun i => f i.succ)
        (fun i => lo i.succ) (fun i => hi i.succ)
        (fun i => horder i.succ) (fun i => hW i.succ) (f 0) (hi 0) (hW 0)
  · exact bound_extra_lower_support hm hK hconv hne (fun i => f i.succ)
      (fun i => lo i.succ) (fun i => hi i.succ)
      (fun i => horder i.succ) (fun i => hW i.succ)
      (f 0) (lo 0) (hi 0) (horder 0) (hW 0) hlower
  · exact bound_extra_upper_support hm hK hconv hne (fun i => f i.succ)
      (fun i => lo i.succ) (fun i => hi i.succ)
      (fun i => horder i.succ) (fun i => hW i.succ)
      (f 0) (lo 0) (hi 0) (horder 0) (hW 0) hupper

/-- Any zero-width or support-touching plank pays the boundary through the
previous actual-volume theorem. The distinguished index is arbitrary. -/
theorem bound_at_index {m : ℕ} (hm : SharpBound d m)
    {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : Fin (m+1) → (Point d) →ᵃ[ℝ] ℝ) (lo hi : Fin (m+1) → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < Body.width K (f i))
    (j : Fin (m+1))
    (hface : lo j = hi j ∨ (∀ x ∈ K, lo j ≤ f j x) ∨ (∀ x ∈ K, f j x ≤ hi j)) :
    (max 0 (1 - ∑ i, (hi i-lo i)/Body.width K (f i)))^(d+1) * (volume K).toReal ≤
      (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal := by
  classical
  let e := Equiv.swap (0 : Fin (m+1)) j
  have he : e 0 = j := Equiv.swap_apply_left _ _
  have h := bound_at_zero_index hm hK hconv hne (fun i => f (e i))
    (fun i => lo (e i)) (fun i => hi (e i))
    (fun i => horder (e i)) (fun i => hW (e i)) (by simpa only [he] using hface)
  have hsum : (∑ i, (hi (e i)-lo (e i))/Body.width K (f (e i))) =
      ∑ i, (hi i-lo i)/Body.width K (f i) :=
    Equiv.sum_comp e (fun i => (hi i-lo i)/Body.width K (f i))
  have hset : (⋃ i, {x | lo (e i) ≤ f (e i) x ∧ f (e i) x ≤ hi (e i)}) =
      ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i} := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e i, hi⟩
    · rintro ⟨i, hi⟩
      obtain ⟨j, rfl⟩ := e.surjective i
      exact ⟨j, hi⟩
  simpa only [hsum, hset] using h

end Plank.FiniteDimensionalInductionBoundary

#print axioms Plank.FiniteDimensionalInductionBoundary.bound_at_index
