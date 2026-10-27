/- Widths under affine functionals, including coordinate changes, clipped
sets and homotheties. Import AffineWidthCore for extrema and reflection alone. -/
module

public import Plank.Proofs.AffineWidthCore
public import Plank.Proofs.AffineEvaluation
public import Mathlib.Analysis.Convex.Topology

@[expose] public section
noncomputable section

open Set Finset

namespace Plank.Body

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Width under a composed affine form is width on the affine image. -/
theorem width_comp_image {F : Type*} [AddCommGroup F] [Module ℝ F]
    (K : Set E) (A : E →ᵃ[ℝ] F) (f : F →ᵃ[ℝ] ℝ) :
    width K (f.comp A)=width (A '' K) f := by
  simp only [width,AffineMap.coe_comp,Set.image_image,Function.comp_def]

/-- An affine coordinate change preserves the full original support width. -/
theorem width_affine_preimage {F : Type*} [AddCommGroup F] [Module ℝ F]
    (A : E ≃ᵃ[ℝ] F) (K : Set F) (f : F →ᵃ[ℝ] ℝ) :
    width (A ⁻¹' K) (f.comp A.toAffineMap)=width K f := by
  rw [width_comp_image]
  change width (A '' (A ⁻¹' K)) f=width K f
  rw [image_preimage_eq K A.surjective]

variable [TopologicalSpace E]

/-! ## §3  Slabs and the homothety -/

omit [TopologicalSpace E] in
/-- The sub-level slab of a body is convex. -/
theorem slab_convex {K : Set E} (hK : Convex ℝ K) (f : E →ᵃ[ℝ] ℝ) (c : ℝ) :
    Convex ℝ (K ∩ {x | f x ≤ c}) :=
  hK.inter ((convex_Iic c).affine_preimage f)

/-- The sub-level slab of a compact body is compact. -/
theorem slab_compact {K : Set E} (hK : IsCompact K) {f : E →ᵃ[ℝ] ℝ} (hf : Continuous f)
    (c : ℝ) : IsCompact (K ∩ {x | f x ≤ c}) :=
  hK.inter_right (isClosed_le hf continuous_const)

/-- ★ **The homothety step** ★ (paper §6) — a body `S` containing the
homothet `V + t·(K − V)` of a body `K` is at least `t` times as wide as
`K` under every direction.  Read off `K`'s own realisers, whose
homothetic images lie in `S`. -/
theorem width_homothet_ge {K S : Set E} (hK : IsCompact K) (hKne : K.Nonempty)
    (hS : IsCompact S) {V : E} {t : ℝ} (hsub : ∀ x ∈ K, V + t • (x - V) ∈ S)
    {g : E →ᵃ[ℝ] ℝ} (hg : Continuous g) : t * width K g ≤ width S g := by
  obtain ⟨a, ha, b, hb, hamax, hbmin⟩ := exists_realisers hK hKne hg
  rw [width_eq_of_realisers ha hb hamax hbmin]
  have := sub_le_width hS hg (hsub a ha) (hsub b hb)
  rw [map_add_smul_sub, map_add_smul_sub] at this
  linarith

end Plank.Body

end

/-- info: 'Plank.Body.width_eq_of_realisers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Body.width_eq_of_realisers

/-- info: 'Plank.Body.map_comb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Body.map_comb

/-- info: 'Plank.Body.width_homothet_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Body.width_homothet_ge

#print axioms Plank.Body.linear_ne_zero_of_width_pos
#print axioms Plank.Body.width_const_sub
#print axioms Plank.Body.width_neg
