/- Minimum width gives contained chords in every direction, via separation
of the difference body. This connects Bang's chord lemma to its classical form. -/
module

public import Plank.Convex.LongestChord
public import Geometry.MinWidth
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace Pointwise

namespace Plank.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The difference body contains the ball of radius equal to minimum width. -/
theorem mem_sub_of_norm_le_minWidth (K : ConvexBody E) (z : E)
    (hz : ‖z‖ ≤ minWidth (K : Set E)) : z ∈ (K : Set E) - (K : Set E) := by
  by_contra hout
  have hc : IsCompact ((K : Set E) - (K : Set E)) := by
    have himage : (fun p : E × E => p.1-p.2) '' ((K : Set E) ×ˢ (K : Set E)) =
        (K : Set E) - (K : Set E) := by
      ext x
      simp only [Set.mem_image, Set.mem_prod, Set.mem_sub]
      aesop
    rw [← himage]
    exact (K.isCompact.prod K.isCompact).image (continuous_fst.sub continuous_snd)
  obtain ⟨f, a, hsep, hza⟩ := geometric_hahn_banach_closed_point
    (K.convex'.sub K.convex') hc.isClosed hout
  let v : E := (InnerProductSpace.toDual ℝ E).symm f
  have hf (x : E) : f x = ⟪x, v⟫ := by
    rw [real_inner_comm]
    exact (InnerProductSpace.toDual_symm_apply).symm
  have hv : v ≠ 0 := by
    intro hv0
    obtain ⟨x, hx⟩ := K.nonempty'
    have h0 := hsep 0 (by exact ⟨x, hx, x, hx, sub_self x⟩)
    rw [hf z, hv0, inner_zero_right] at hza
    rw [map_zero] at h0
    linarith only [h0, hza]
  obtain ⟨x, hx, y, hy, hxy⟩ := widthAlong_attained (K : Set E) K.isCompact K.nonempty' v
  have hxysep := hsep (x-y) ⟨x, hx, y, hy, rfl⟩
  rw [hf (x-y), inner_sub_left] at hxysep
  have hbound : f z ≤ widthAlong (K : Set E) v := by
    rw [hf z]
    calc ⟪z, v⟫ ≤ ‖z‖*‖v‖ := real_inner_le_norm _ _
      _ ≤ minWidth (K : Set E)*‖v‖ := mul_le_mul_of_nonneg_right hz (norm_nonneg v)
      _ ≤ widthAlong (K : Set E) v := widthAlong_ge_minWidth_mul_norm K hv
  linarith only [hxysep, hza, hbound, hxy]

/-- In every unit direction there is a chord of length at least minimum width. -/
theorem exists_minWidth_chord (K : ConvexBody E) (u : E) (hu : ‖u‖ = 1) :
    ∃ x ∈ (K : Set E), ∃ y ∈ (K : Set E),
      x-y = minWidth (K : Set E) • u := by
  apply Set.mem_sub.mp
  apply mem_sub_of_norm_le_minWidth K
  rw [norm_smul, hu, mul_one, Real.norm_of_nonneg (minWidth_nonneg K)]

/-- Bang's classical plank inequality for unit normals. Interior nonemptiness
is unnecessary: bodies of zero minimum width give the inequality immediately. -/
theorem bang_minWidth_unit (K : ConvexBody E) {n : ℕ} (hn : 0 < n)
    (u : Fin n → E) (hu : ∀ i, ‖u i‖ = 1)
    (lo hi : Fin n → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hcover : ∀ z ∈ (K : Set E), ∃ i, lo i ≤ ⟪z, u i⟫ ∧ ⟪z, u i⟫ ≤ hi i) :
    minWidth (K : Set E) ≤ ∑ i, (hi i-lo i) := by
  classical
  let W := minWidth (K : Set E)
  by_cases hW : 0 < W
  · choose x hx y hy hxy using fun i => exists_minWidth_chord K (u i) (hu i)
    let c : Fin n → E := fun i => (1/2 : ℝ) • (x i+y i)
    have hends (i : Fin n) : c i-(W/2) • u i ∈ (K : Set E) ∧
        c i+(W/2) • u i ∈ (K : Set E) := by
      have hs : (W/2) • u i = (1/2 : ℝ) • (x i-y i) := by
        rw [hxy i, smul_smul]
        congr 1
        dsimp [W]
        ring
      have hm : c i-(W/2) • u i = y i := by rw [hs]; dsimp [c]; module
      have hp : c i+(W/2) • u i = x i := by rw [hs]; dsimp [c]; module
      exact ⟨hm ▸ hy i, hp ▸ hx i⟩
    have hb := sum_ge_one_of_realized_chord_cover hn (K : Set E) K.convex' c u
      (fun _ => W/2) (fun _ => div_pos hW (by norm_num)) hu hends
      (fun i => (lo i+hi i)/2) (fun i => (hi i-lo i)/2)
      (fun i => div_nonneg (sub_nonneg.mpr (hle i)) (by norm_num)) (by
        intro z hz
        obtain ⟨i, hl, hh⟩ := hcover z hz
        exact ⟨i, abs_le.mpr ⟨by linarith only [hl], by linarith only [hh]⟩⟩)
    have heq (i : Fin n) : ((hi i-lo i)/2)/(W/2) = (hi i-lo i)/W := by field_simp
    simp only [heq, ← Finset.sum_div] at hb
    have hh := (le_div_iff₀ hW).mp hb
    simpa only [one_mul] using hh
  · exact le_trans (le_of_not_gt hW) (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hle i))

/-- Bang's classical plank theorem with arbitrary nonzero normals and the
correct absolute widths `(hi-lo)/‖u‖`. -/
theorem bang_minWidth (K : ConvexBody E) {n : ℕ} (hn : 0 < n)
    (u : Fin n → E) (hu : ∀ i, u i ≠ 0)
    (lo hi : Fin n → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hcover : ∀ z ∈ (K : Set E), ∃ i, lo i ≤ ⟪z, u i⟫ ∧ ⟪z, u i⟫ ≤ hi i) :
    minWidth (K : Set E) ≤ ∑ i, (hi i-lo i)/‖u i‖ := by
  let v : Fin n → E := fun i => ‖u i‖⁻¹ • u i
  have hnrm (i : Fin n) : 0 < ‖u i‖ := norm_pos_iff.mpr (hu i)
  have hv (i : Fin n) : ‖v i‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (hnrm i).ne']
  have hb := bang_minWidth_unit K hn v hv (fun i => lo i/‖u i‖) (fun i => hi i/‖u i‖)
    (fun i => div_le_div_of_nonneg_right (hle i) (norm_nonneg _)) (by
      intro z hz
      obtain ⟨i, hl, hh⟩ := hcover z hz
      refine ⟨i, ?_, ?_⟩
      · simpa only [v, inner_smul_right, RCLike.conj_to_real, div_eq_mul_inv, mul_comm]
          using div_le_div_of_nonneg_right hl (norm_nonneg (u i))
      · simpa only [v, inner_smul_right, RCLike.conj_to_real, div_eq_mul_inv, mul_comm]
          using div_le_div_of_nonneg_right hh (norm_nonneg (u i)))
  simpa only [sub_div] using hb

/-- info: 'Plank.Convex.mem_sub_of_norm_le_minWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mem_sub_of_norm_le_minWidth

/-- info: 'Plank.Convex.bang_minWidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bang_minWidth

end Plank.Convex
