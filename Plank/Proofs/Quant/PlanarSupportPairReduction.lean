/- Equality with one support plank reduces to actual one-plank equality
and a closed geometric cover, with no assumption on the other direction. -/
module

public import Plank.Proofs.Quant.PlanarSupportGap

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSupportPairReduction

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarInductionBoundary PlanarSupportGap
open Plank.Convex.DeficientHeightTilt

def pulledEndpoint (g : Point →ᵃ[ℝ] ℝ) (a : Point) (r t : ℝ) : ℝ :=
  (t-r*g a)/(1-r)

theorem pulled_width (g : Point →ᵃ[ℝ] ℝ) (a : Point) (r lo hi : ℝ) :
    pulledEndpoint g a r hi-pulledEndpoint g a r lo = (hi-lo)/(1-r) := by
  unfold pulledEndpoint
  ring

theorem pulled_relativeWidth (K : Set Point) (g : Point →ᵃ[ℝ] ℝ)
    (a : Point) (r lo hi : ℝ) :
    (pulledEndpoint g a r hi-pulledEndpoint g a r lo)/rangeWidth K g =
      ((hi-lo)/rangeWidth K g)/(1-r) := by
  rw [pulled_width]
  ring

/-- The first window is [0,r] in its normalized support coordinate.
No parallelism or polygon assumption occurs. Equality is equivalent to
one-plank equality for the pulled-back second window, together with an
explicit closed cover by the two original planks and the contracted body. -/
theorem equality_iff_reduced {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f g : Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (_hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (r lo hi : ℝ) (hr : 0 ≤ r) (hlohi : lo < hi) (hW : 0 < rangeWidth K g)
    (hR : r+(hi-lo)/rangeWidth K g < 1) :
    (volume (K \ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ {x | lo ≤ g x ∧ g x ≤ hi}))).toReal =
        (1-r-(hi-lo)/rangeWidth K g)^2*(volume K).toReal ↔
      (volume (K \ {x | pulledEndpoint g a r lo ≤ g x ∧ g x ≤ pulledEndpoint g a r hi})).toReal =
        (1-(pulledEndpoint g a r hi-pulledEndpoint g a r lo)/rangeWidth K g)^2*(volume K).toReal ∧
      K ⊆ ({x | 0 ≤ f x ∧ f x ≤ r} ∪ {x | lo ≤ g x ∧ g x ≤ hi}) ∪
        (AffineMap.homothety a (1-r) '' K) := by
  let q := 1-r
  let s := (hi-lo)/rangeWidth K g
  let C := AffineMap.homothety a q '' K
  let P := {x | 0 ≤ f x ∧ f x ≤ r}
  let U := {x | lo ≤ g x ∧ g x ≤ hi}
  let l := pulledEndpoint g a r lo
  let h := pulledEndpoint g a r hi
  let M := (1-r-s)^2*(volume K).toReal
  have hs : 0 < s := div_pos (sub_pos.mpr hlohi) hW
  have hq : 0 < q := by dsimp [q]; linarith only [hR,hs]
  have hq1 : q ≤ 1 := by dsimp [q]; linarith only [hr]
  have hsmall : s/q < 1 := (div_lt_one hq).mpr (by dsimp [q]; linarith only [hR])
  have hlinear : f.linear ≠ 0 := by
    intro hz
    obtain ⟨c,hc⟩ := f.linear_eq_zero_iff_exists_const.mp hz
    have he : f a = f b := by rw [hc]; rfl
    rw [hfa,hfb] at he
    norm_num at he
  have hC : IsCompact C := hK.image (AffineMap.homothety_continuous a q)
  have hU : IsClosed U := (isClosed_le continuous_const (continuous_form g)).inter
    (isClosed_le (continuous_form g) continuous_const)
  have hCK : C ⊆ K := homothety_subset hconv ha ⟨hq.le,hq1⟩
  have hbeyond : ∀ x ∈ C, r ≤ f x := by
    rintro _ ⟨x,hx,rfl⟩
    rw [form_homothety,hfa,mul_one]
    have hh := mul_nonneg hq.le (hf x hx).1
    dsimp [q] at hh ⊢
    linarith only [hh]
  have harea : (volume (C \ U)).toReal = q^2*(volume (K \ {x | l ≤ g x ∧ g x ≤ h})).toReal := by
    simpa only [C,U,l,h,q,sub_sub_cancel,pulledEndpoint] using area_homothety_gap K g a hq lo hi
  have hwidth : (h-l)/rangeWidth K g = s/q := pulled_relativeWidth K g a r lo hi
  have hlh : l < h := sub_pos.mp (by
    change 0 < pulledEndpoint g a r hi-pulledEndpoint g a r lo
    rw [pulled_width]
    exact div_pos (sub_pos.mpr hlohi) hq)
  have hscalar : q^2*((1-s/q)^2*(volume K).toReal) = M := by
    have hM : M = (q-s)^2*(volume K).toReal := rfl
    rw [hM]
    field_simp
  have hbound := PlanarOnePlank.uncovered_area_lower_bound hK hconv ⟨a,ha⟩ g l h hlh.le hW
  rw [hwidth,max_eq_right (sub_pos.mpr hsmall).le] at hbound
  have hcapbound : M ≤ (volume (C \ U)).toReal := by
    rw [← hscalar,harea]
    exact mul_le_mul_of_nonneg_left hbound (sq_nonneg q)
  have hcapmono : (volume (C \ U)).toReal ≤ (volume (K \ (P ∪ U))).toReal :=
    area_gap_mono_beyond hK hCK f hlinear 0 r hbeyond
  have hcoveriff := area_eq_iff_cover hK hconv hV hC hU hCK f hlinear 0 r hbeyond
  change (volume (K \ (P ∪ U))).toReal = M ↔ _
  constructor
  · intro he
    have hcap : (volume (C \ U)).toReal = M := le_antisymm (hcapmono.trans_eq he) hcapbound
    refine ⟨?_,hcoveriff.mp (hcap.trans he.symm)⟩
    change (volume (K \ {x | l ≤ g x ∧ g x ≤ h})).toReal = (1-(h-l)/rangeWidth K g)^2*(volume K).toReal
    rw [hwidth]
    apply (mul_left_cancel₀ (pow_ne_zero 2 hq.ne'))
    rw [← harea,hcap,hscalar]
  · rintro ⟨he,hcover⟩
    have hcap : (volume (C \ U)).toReal = M := by
      rw [harea,he,hwidth,hscalar]
    exact (hcoveriff.mpr hcover).symm.trans hcap

end Plank.PlanarSupportPairReduction

/-- info: 'Plank.PlanarSupportPairReduction.equality_iff_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSupportPairReduction.equality_iff_reduced
