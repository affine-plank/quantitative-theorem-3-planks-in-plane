/-
Copyright (c) 2026 Zaz Brown. All rights reserved.
Supporting lemmas for the Affine Plank Conjecture.
Properties of the `widthAlong` function.
-/
module

public import Geometry.AffinePlankConjecture
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Data.Real.Pointwise

@[expose] public section

open scoped RealInnerProductSpace Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Helper lemmas: boundedness of inner product images -/

/-- The image of a bounded set under `⟪·, u⟫` is bounded above. -/
theorem bddAbove_inner_image {K : Set E} (hbdd : Bornology.IsBounded K) (u : E) :
    BddAbove ((fun x => ⟪x, u⟫) '' K) := by
  obtain ⟨R, hR⟩ := hbdd.subset_ball 0
  exact ⟨R * ‖u‖, fun y ⟨x, hx, hxy⟩ => by
    subst hxy; have := hR hx; rw [Metric.mem_ball, dist_zero_right] at this
    exact (le_abs_self _).trans ((abs_real_inner_le_norm x u).trans
      (mul_le_mul_of_nonneg_right this.le (norm_nonneg u)))⟩

/-- The image of a bounded set under `⟪·, u⟫` is bounded below. -/
theorem bddBelow_inner_image {K : Set E} (hbdd : Bornology.IsBounded K) (u : E) :
    BddBelow ((fun x => ⟪x, u⟫) '' K) := by
  obtain ⟨R, hR⟩ := hbdd.subset_ball 0
  exact ⟨-(R * ‖u‖), fun y ⟨x, hx, hxy⟩ => by
    subst hxy; have hx' := hR hx; rw [Metric.mem_ball, dist_zero_right] at hx'
    nlinarith [abs_real_inner_le_norm x u, neg_abs_le ⟪x, u⟫, norm_nonneg u]⟩

/-! ## Basic properties of `widthAlong` -/

/-- `widthAlong` is nonneg for nonempty bounded sets. -/
theorem widthAlong_nonneg {K : Set E} (hne : K.Nonempty) (hbdd : Bornology.IsBounded K)
    (u : E) : 0 ≤ widthAlong K u := by
  unfold widthAlong
  obtain ⟨x, hx⟩ := hne
  have hmem := Set.mem_image_of_mem (fun x => ⟪x, u⟫) hx
  exact sub_nonneg.mpr ((csInf_le (bddBelow_inner_image hbdd u) hmem).trans
    (le_csSup (bddAbove_inner_image hbdd u) hmem))

/-- `widthAlong` of a singleton is zero. -/
theorem widthAlong_singleton (x : E) (u : E) :
    widthAlong {x} u = 0 := by
  unfold widthAlong
  rw [Set.image_singleton]
  simp

/-- `widthAlong K 0 = 0` for any nonempty set `K`. -/
theorem widthAlong_zero_dir (K : Set E) (hne : K.Nonempty) :
    widthAlong K 0 = 0 := by
  unfold widthAlong
  simp only [inner_zero_right]
  rw [hne.image_const]
  simp

/-- Monotonicity (bounded version): if `S ⊆ T`, then `widthAlong S u ≤ widthAlong T u`. -/
theorem widthAlong_mono_bounded {S T : Set E} (hST : S ⊆ T)
    (hSne : S.Nonempty) (hTbdd : Bornology.IsBounded T) (u : E) :
    widthAlong S u ≤ widthAlong T u := by
  unfold widthAlong
  have him := Set.image_mono (f := fun x => ⟪x, u⟫) hST
  linarith [csSup_le_csSup (bddAbove_inner_image hTbdd u) (hSne.image _) him,
    csInf_le_csInf (bddBelow_inner_image hTbdd u) (hSne.image _) him]

/-- `widthAlong` is nonneg for a ConvexBody. -/
theorem widthAlong_nonneg_convexBody [FiniteDimensional ℝ E] (K : ConvexBody E) (u : E) :
    0 ≤ widthAlong (↑K : Set E) u :=
  widthAlong_nonneg K.nonempty K.isBounded u

/-- `widthAlong K (-u) = widthAlong K u`, for nonempty bounded `K`. -/
theorem widthAlong_neg {K : Set E} (hne : K.Nonempty) (hbdd : Bornology.IsBounded K) (u : E) :
    widthAlong K (-u) = widthAlong K u := by
  unfold widthAlong
  set S := (fun x => ⟪x, u⟫) '' K
  have hSne : S.Nonempty := hne.image _
  have hbddA : BddAbove S := bddAbove_inner_image hbdd u
  have hbddB : BddBelow S := bddBelow_inner_image hbdd u
  have him : (fun x => ⟪x, -u⟫) '' K = -S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show -⟪x, -u⟫ ∈ S
      simp only [inner_neg_right, neg_neg]
      exact Set.mem_image_of_mem _ hx
    · intro hy
      have hy' : -y ∈ S := hy
      obtain ⟨x, hx, hfx⟩ := hy'
      exact ⟨x, hx, by simp only [inner_neg_right]; linarith⟩
  rw [him, csSup_neg hSne hbddB, csInf_neg hSne hbddA]
  ring

/-- If `K` has nonempty interior and `u ≠ 0`, then `widthAlong K u > 0`. -/
theorem widthAlong_pos_of_interior [FiniteDimensional ℝ E]
    {K : Set E} (hne_int : (interior K).Nonempty) (hbdd : Bornology.IsBounded K)
    {u : E} (hu : u ≠ 0) :
    0 < widthAlong K u := by
  unfold widthAlong
  obtain ⟨z, hz⟩ := hne_int
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have h_in_ball : z + (ε / (2 * ‖u‖)) • u ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖z + (ε / (2 * ‖u‖)) • u - z‖ = ε / (2 * ‖u‖) * ‖u‖ := by
      rw [show z + (ε / (2 * ‖u‖)) • u - z = (ε / (2 * ‖u‖)) • u from by abel]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε (mul_pos two_pos hu_pos))]
    rw [h1]; have : ε / (2 * ‖u‖) * ‖u‖ = ε / 2 := by field_simp
    linarith
  have hz1 : z + (ε / (2 * ‖u‖)) • u ∈ K := interior_subset (hball h_in_ball)
  have h_val : ⟪z + (ε / (2 * ‖u‖)) • u, u⟫ =
      ⟪z, u⟫ + (ε / (2 * ‖u‖)) * ‖u‖ ^ 2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith [csInf_le (bddBelow_inner_image hbdd u)
      (Set.mem_image_of_mem _ (interior_subset hz)),
    le_csSup (bddAbove_inner_image hbdd u) (Set.mem_image_of_mem _ hz1),
    mul_pos (div_pos hε (mul_pos two_pos hu_pos)) (sq_pos_of_pos hu_pos)]

/-- `widthAlong` is positive for a ConvexBody with nonempty interior and nonzero direction. -/
theorem widthAlong_pos_convexBody [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hK : (interior (K : Set E)).Nonempty)
    {u : E} (hu : u ≠ 0) :
    0 < widthAlong (↑K : Set E) u :=
  widthAlong_pos_of_interior hK K.isBounded hu

/-- Relative width denominator is nonzero for a ConvexBody with nonempty interior. -/
theorem widthAlong_ne_zero_of_interior [FiniteDimensional ℝ E]
    (K : ConvexBody E) (hK : (interior (K : Set E)).Nonempty)
    {u : E} (hu : u ≠ 0) :
    widthAlong (↑K : Set E) u ≠ 0 :=
  ne_of_gt (widthAlong_pos_convexBody K hK hu)

/-! ## Scaling of `widthAlong` -/

/-- `widthAlong K (c • u) = c * widthAlong K u` for `c ≥ 0`. -/
theorem widthAlong_smul_nonneg {K : Set E} {c : ℝ} (hc : 0 ≤ c) (u : E) :
    widthAlong K (c • u) = c * widthAlong K u := by
  unfold widthAlong; simp_rw [inner_smul_right]
  have him : (fun x => c * ⟪x, u⟫) '' K = c • ((fun x => ⟪x, u⟫) '' K) := by
    ext y; simp only [Set.mem_image, Set.mem_smul_set]; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟪x, u⟫, Set.mem_image_of_mem _ hx, rfl⟩
    · rintro ⟨s, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [him, Real.sSup_smul_of_nonneg hc, Real.sInf_smul_of_nonneg hc]
  simp only [smul_eq_mul]; ring

/-- `widthAlong K (c • u) = |c| * widthAlong K u` for any scalar `c`. -/
theorem widthAlong_smul {K : Set E} (hne : K.Nonempty) (hbdd : Bornology.IsBounded K)
    (c : ℝ) (u : E) :
    widthAlong K (c • u) = |c| * widthAlong K u := by
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc, widthAlong_smul_nonneg hc]
  · rw [show c • u = |c| • (-u) from by rw [abs_of_neg hc, smul_neg, neg_smul, neg_neg],
      widthAlong_smul_nonneg (abs_nonneg c), widthAlong_neg hne hbdd]

/-! ## Translation invariance -/

/-- `widthAlong` is translation invariant: `widthAlong (t +ᵥ K) u = widthAlong K u`. -/
theorem widthAlong_vadd {K : Set E} (hne : K.Nonempty) (hbdd : Bornology.IsBounded K)
    (t : E) (u : E) :
    widthAlong (t +ᵥ K) u = widthAlong K u := by
  unfold widthAlong
  set S := (fun x => ⟪x, u⟫) '' K with hS_def
  set c := ⟪t, u⟫
  have hSne : S.Nonempty := hne.image _
  have hbddA : BddAbove S := bddAbove_inner_image hbdd u
  have hbddB : BddBelow S := bddBelow_inner_image hbdd u
  have him : (fun x => ⟪x, u⟫) '' (t +ᵥ K) = {c} + S := by
    ext y; simp only [Set.mem_image, Set.mem_vadd_set, Set.mem_add, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨c, rfl, ⟪k, u⟫, Set.mem_image_of_mem _ hk, ?_⟩
      show ⟪t, u⟫ + ⟪k, u⟫ = ⟪(t +ᵥ k : E), u⟫
      rw [vadd_eq_add, inner_add_left]
    · rintro ⟨a, rfl, b, hb, rfl⟩
      obtain ⟨k, hk, rfl⟩ := hb
      refine ⟨t + k, ⟨k, hk, vadd_eq_add t k⟩, ?_⟩
      show ⟪t + k, u⟫ = ⟪t, u⟫ + ⟪k, u⟫
      rw [inner_add_left]
  rw [him]
  have h1 : sSup ({c} + S) = c + sSup S :=
    (csSup_add (Set.singleton_nonempty c) bddAbove_singleton hSne hbddA).trans (by simp)
  have h2 : sInf ({c} + S) = c + sInf S :=
    (csInf_add (Set.singleton_nonempty c) bddBelow_singleton hSne hbddB).trans (by simp)
  rw [h1, h2]; ring

/-! ## Convex hull invariance -/

/-- `sSup (convexHull ℝ S) = sSup S` for bounded nonempty sets in `ℝ`. -/
theorem csSup_convexHull_eq {S : Set ℝ} (hne : S.Nonempty) (hbddA : BddAbove S)
    (hbddB : BddBelow S) :
    sSup (convexHull ℝ S) = sSup S := by
  have hIcc : convexHull ℝ S ⊆ Set.Icc (sInf S) (sSup S) :=
    convexHull_min (fun y hy => ⟨csInf_le hbddB hy, le_csSup hbddA hy⟩) (convex_Icc _ _)
  apply le_antisymm
  · exact csSup_le (convexHull_nonempty_iff.mpr hne) (fun x hx => (hIcc hx).2)
  · exact csSup_le_csSup ⟨sSup S, fun x hx => (hIcc hx).2⟩ hne (subset_convexHull ℝ S)

/-- `sInf (convexHull ℝ S) = sInf S` for bounded nonempty sets in `ℝ`. -/
theorem csInf_convexHull_eq {S : Set ℝ} (hne : S.Nonempty) (hbddA : BddAbove S)
    (hbddB : BddBelow S) :
    sInf (convexHull ℝ S) = sInf S := by
  have hIcc : convexHull ℝ S ⊆ Set.Icc (sInf S) (sSup S) :=
    convexHull_min (fun y hy => ⟨csInf_le hbddB hy, le_csSup hbddA hy⟩) (convex_Icc _ _)
  apply le_antisymm
  · exact csInf_le_csInf ⟨sInf S, fun x hx => (hIcc hx).1⟩ hne (subset_convexHull ℝ S)
  · exact le_csInf (convexHull_nonempty_iff.mpr hne) (fun x hx => (hIcc hx).1)

/-- `widthAlong (convexHull ℝ K) u = widthAlong K u` for bounded nonempty `K`. -/
theorem widthAlong_convexHull {K : Set E} (hne : K.Nonempty) (hbdd : Bornology.IsBounded K)
    (u : E) :
    widthAlong (convexHull ℝ K) u = widthAlong K u := by
  unfold widthAlong
  set f : E → ℝ := fun x => ⟪x, u⟫
  have hlin : IsLinearMap ℝ f :=
    ⟨fun _ _ => inner_add_left _ _ _, fun _ _ => real_inner_smul_left _ _ _⟩
  rw [hlin.image_convexHull,
    csSup_convexHull_eq (hne.image f) (bddAbove_inner_image hbdd u)
      (bddBelow_inner_image hbdd u),
    csInf_convexHull_eq (hne.image f) (bddAbove_inner_image hbdd u)
      (bddBelow_inner_image hbdd u)]

/-! ## Normalization and scale invariance -/

/-- `widthAlong K u / ‖u‖ = widthAlong K (‖u‖⁻¹ • u)` for `u ≠ 0`. -/
theorem widthAlong_div_norm {K : Set E} (hne : K.Nonempty) (hbdd : Bornology.IsBounded K)
    {u : E} (hu : u ≠ 0) :
    widthAlong K u / ‖u‖ = widthAlong K (‖u‖⁻¹ • u) := by
  rw [widthAlong_smul hne hbdd, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hu))]
  rw [div_eq_mul_inv, mul_comm]

/-- The relative width `(hi - lo) / widthAlong K u` is scale-invariant in `u` (for `c > 0`). -/
theorem relWidth_scale_invariant {K : Set E} {u : E} {lo hi : ℝ} {c : ℝ} (hc : 0 < c) :
    (c * hi - c * lo) / widthAlong K (c • u) = (hi - lo) / widthAlong K u := by
  rw [widthAlong_smul_nonneg hc.le, ← mul_sub, mul_div_mul_left _ _ (ne_of_gt hc)]
