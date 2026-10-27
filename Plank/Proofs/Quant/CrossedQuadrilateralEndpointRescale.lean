/- Continuous endpoint normalization, including reversed and null affine bands. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralMixedCompact

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralEndpointRescale
open Set MeasureTheory CrossedQuadrilateralAttainment
open Plank.Convex.DeficientHeightTilt

def lower (s c lo hi : ℝ) : ℝ := if 0 < s then (lo-c)/s else (hi-c)/s
def upper (s c lo hi : ℝ) : ℝ := if 0 < s then (hi-c)/s else (lo-c)/s

theorem continuous_lower (s c : ℝ) :
    Continuous (fun p : ℝ × ℝ => lower s c p.1 p.2) := by
  unfold lower
  split <;> fun_prop

theorem continuous_upper (s c : ℝ) :
    Continuous (fun p : ℝ × ℝ => upper s c p.1 p.2) := by
  unfold upper
  split <;> fun_prop

theorem difference (s c lo hi : ℝ) :
    upper s c lo hi-lower s c lo hi = (hi-lo)/|s| := by
  by_cases hs : 0 < s
  · simp only [lower,upper,if_pos hs,abs_of_pos hs]
    ring
  · have hsn : s ≤ 0 := le_of_not_gt hs
    simp only [lower,upper,if_neg hs,abs_of_nonpos hsn,div_neg]
    ring

theorem ordered {s c lo hi : ℝ} (hs : s ≠ 0) (ho : lo ≤ hi) :
    lower s c lo hi ≤ upper s c lo hi := by
  apply sub_nonneg.mp
  rw [difference]
  exact div_nonneg (sub_nonneg.mpr ho) (abs_pos.mpr hs).le

theorem positive_iff {s c lo hi : ℝ} (hs : s ≠ 0) :
    lower s c lo hi < upper s c lo hi ↔ lo < hi := by
  rw [← sub_pos,difference,div_pos_iff_of_pos_right (abs_pos.mpr hs),sub_pos]

theorem band_eq (G H : Point →ᵃ[ℝ] ℝ) {s c : ℝ} (hs : s ≠ 0)
    (hG : ∀ z, G z = s*H z+c) (lo hi : ℝ) :
    {z | lo ≤ G z ∧ G z ≤ hi} =
      {z | lower s c lo hi ≤ H z ∧ H z ≤ upper s c lo hi} := by
  ext z
  change (lo ≤ G z ∧ G z ≤ hi) ↔ _
  rw [hG]
  rcases lt_or_gt_of_ne hs with hs | hs
  · simp only [lower,upper,if_neg (not_lt.mpr hs.le),mem_ofPred_eq,
      div_le_iff_of_neg hs,le_div_iff_of_neg hs]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith only [h₁,h₂]
  · simp only [lower,upper,if_pos hs,mem_ofPred_eq,div_le_iff₀ hs,le_div_iff₀ hs]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith only [h₁,h₂]

theorem positive_range (S : Shape) (G H : Point →ᵃ[ℝ] ℝ) {s c : ℝ}
    (hs : 0 < s) (hG : ∀ z, G z = s*H z+c) :
    rangeWidth S.body G = s*rangeWidth S.body H := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Plank.Body.exists_realisers (compact_body S)
    ⟨0,zero_mem S⟩ H.continuous_of_finiteDimensional
  have hmaxG (z) (hz : z ∈ S.body) : G z ≤ G a := by
    rw [hG,hG]
    exact add_le_add (mul_le_mul_of_nonneg_left (hmax z hz) hs.le) le_rfl
  have hminG (z) (hz : z ∈ S.body) : G b ≤ G z := by
    rw [hG,hG]
    exact add_le_add (mul_le_mul_of_nonneg_left (hmin z hz) hs.le) le_rfl
  change Plank.Body.width S.body G = s*Plank.Body.width S.body H
  rw [Plank.Body.width_eq_of_realisers ha hb hmaxG hminG,
    Plank.Body.width_eq_of_realisers ha hb hmax hmin,hG,hG]
  ring

theorem range_eq (S : Shape) (G H : Point →ᵃ[ℝ] ℝ) {s c : ℝ}
    (hs : s ≠ 0) (hG : ∀ z, G z = s*H z+c) :
    rangeWidth S.body G = |s| * rangeWidth S.body H := by
  rcases lt_or_gt_of_ne hs with hs | hs
  · have he := positive_range S (-G) H (neg_pos.mpr hs)
      (c := -c) (fun z => by change -G z = _; rw [hG]; ring)
    have hn : rangeWidth S.body (-G) = rangeWidth S.body G :=
      Plank.Body.width_neg (compact_body S) ⟨0,zero_mem S⟩ G.continuous_of_finiteDimensional
    rw [hn] at he
    simpa only [abs_of_neg hs] using he
  · simpa only [abs_of_pos hs] using positive_range S G H hs hG

/-- The formula is valid at every endpoint pair, including null bands. The
normalization is a fixed continuous map of endpoints, rather than a pointwise
choice of a new band; this matters when taking limits of equality families. -/
theorem relative_width_eq (S : Shape) (G H : Point →ᵃ[ℝ] ℝ) {s c : ℝ}
    (hs : s ≠ 0) (hG : ∀ z, G z = s*H z+c) (lo hi : ℝ) :
    (hi-lo)/rangeWidth S.body G =
      (upper s c lo hi-lower s c lo hi)/rangeWidth S.body H := by
  rw [range_eq S G H hs hG,difference,div_div]

theorem coefficients (G : Point →ᵃ[ℝ] ℝ) (u : Point) {s c : ℝ}
    (hG : ∀ z, G z = s*direction u z+c) :
    G.linear (1,0) = s*u.1 ∧ G.linear (0,1) = s*u.2 := by
  have h0 := hG 0
  have hx := hG (1,0)
  have hy := hG (0,1)
  rw [CrossedQuadrilateralSupport.eval_linear] at hx hy
  simp only [direction_apply,dot,Prod.fst_zero,Prod.snd_zero,mul_zero,mul_one,
    add_zero,zero_add] at h0 hx hy
  constructor <;> linarith only [h0,hx,hy]

end Quant.CrossedQuadrilateralEndpointRescale

/-- info: 'Quant.CrossedQuadrilateralEndpointRescale.relative_width_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralEndpointRescale.relative_width_eq
