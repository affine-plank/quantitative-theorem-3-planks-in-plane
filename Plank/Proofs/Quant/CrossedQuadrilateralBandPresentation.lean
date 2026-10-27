/- Preserve original bands and actual widths under scalar normalization. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralVerticalPairCatalogue
public import Plank.Proofs.Quant.CrossedQuadrilateralAxisPresentation

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralBandPresentation
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionGeometry
open CrossedQuadrilateralPlacement
open Plank.Convex.DeficientHeightTilt

theorem positive_rescale (S : Shape) (G H : Point →ᵃ[ℝ] ℝ) (s c : ℝ)
    (hs : 0 < s) (hG : ∀ z, G z = s*H z+c) (lo hi : ℝ) (ho : lo < hi) :
    ∃ l u : ℝ, l < u ∧ {z | lo ≤ G z ∧ G z ≤ hi} = {z | l ≤ H z ∧ H z ≤ u} ∧
      (hi-lo)/rangeWidth S.body G = (u-l)/rangeWidth S.body H := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Plank.Body.exists_realisers (compact_body S)
    ⟨0,zero_mem S⟩ H.continuous_of_finiteDimensional
  have hmaxG (z) (hz : z ∈ S.body) : G z ≤ G a := by
    rw [hG,hG]
    exact add_le_add (mul_le_mul_of_nonneg_left (hmax z hz) hs.le) le_rfl
  have hminG (z) (hz : z ∈ S.body) : G b ≤ G z := by
    rw [hG,hG]
    exact add_le_add (mul_le_mul_of_nonneg_left (hmin z hz) hs.le) le_rfl
  have hw : rangeWidth S.body G = s*rangeWidth S.body H := by
    change Plank.Body.width S.body G = s*Plank.Body.width S.body H
    rw [Plank.Body.width_eq_of_realisers ha hb hmaxG hminG,
      Plank.Body.width_eq_of_realisers ha hb hmax hmin,hG,hG]
    ring
  refine ⟨(lo-c)/s,(hi-c)/s,
    (div_lt_div_iff_of_pos_right hs).mpr (sub_lt_sub_right ho _),?_,?_⟩
  · ext z
    change (lo ≤ G z ∧ G z ≤ hi) ↔ ((lo-c)/s ≤ H z ∧ H z ≤ (hi-c)/s)
    rw [hG,div_le_iff₀ hs,le_div_iff₀ hs]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith only [h₁,h₂]
  · rw [hw]
    field_simp
    ring

theorem nonzero_rescale (S : Shape) (G H : Point →ᵃ[ℝ] ℝ) (s c : ℝ)
    (hs : s ≠ 0) (hG : ∀ z, G z = s*H z+c) (lo hi : ℝ) (ho : lo < hi) :
    ∃ l u : ℝ, l < u ∧ {z | lo ≤ G z ∧ G z ≤ hi} = {z | l ≤ H z ∧ H z ≤ u} ∧
      (hi-lo)/rangeWidth S.body G = (u-l)/rangeWidth S.body H := by
  rcases lt_or_gt_of_ne hs with hs | hs
  · obtain ⟨l,u,hu,hband,hw⟩ := positive_rescale S (-G) H (-s) (-c) (neg_pos.mpr hs)
      (fun z => by change -G z = _; rw [hG]; ring) (-hi) (-lo) (neg_lt_neg ho)
    have hneg : {z | -hi ≤ (-G) z ∧ (-G) z ≤ -lo} = {z | lo ≤ G z ∧ G z ≤ hi} := by
      ext z
      change (-hi ≤ -G z ∧ -G z ≤ -lo) ↔ _
      constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]
    have hwneg : rangeWidth S.body (-G) = rangeWidth S.body G :=
      Plank.Body.width_neg (compact_body S) ⟨0,zero_mem S⟩ G.continuous_of_finiteDimensional
    exact ⟨l,u,hu,by rwa [hneg] at hband,by simpa only [hwneg,neg_sub_neg] using hw⟩
  · exact positive_rescale S G H s c hs hG lo hi ho

/-- The transverse coefficient may have either sign. -/
theorem transverse (S : Shape) (G : Point →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo < hi) (hy : G.linear (0,1) ≠ 0) :
    ∃ k l u : ℝ, l < u ∧ {z | lo ≤ G z ∧ G z ≤ hi} = oblique k l u ∧
      (hi-lo)/rangeWidth S.body G = (u-l)/rangeWidth S.body (direction (k,1)) ∧
      G.linear (1,0) = k*G.linear (0,1) := by
  let k := G.linear (1,0)/G.linear (0,1)
  have hk : G.linear (1,0) = k*G.linear (0,1) := by
    dsimp only [k]
    exact (div_mul_cancel₀ _ hy).symm
  have he (z : Point) : G z = G.linear (0,1)*direction (k,1) z+G 0 := by
    rw [CrossedQuadrilateralSupport.eval_linear,hk]
    change (k*G.linear (0,1))*z.1+G.linear (0,1)*z.2+G 0 =
      G.linear (0,1)*(k*z.1+1*z.2)+G 0
    ring
  obtain ⟨l,u,hu,hband,hw⟩ := nonzero_rescale S G (direction (k,1))
    (G.linear (0,1)) (G 0) hy he lo hi ho
  refine ⟨k,l,u,hu,?_,hw,hk⟩
  simpa only [oblique,direction_apply,dot,one_mul] using hband

theorem vertical_plank (S : Shape) (p : Plank) (ho : p.lo < p.hi) (hy : p.u.2 = 0) :
    ∃ l u : ℝ, l < u ∧ p.set = band false l u ∧ relativeWidth S p = (u-l)/(S.a+S.c) := by
  have hx : p.u.1 ≠ 0 := fun hh => p.u_ne_zero (Prod.ext hh hy)
  exact CrossedQuadrilateralAxisPresentation.nonzero_scale S false (direction p.u)
    p.u.1 0 hx
    (fun z => by change p.u.1*z.1+p.u.2*z.2 = p.u.1*z.1+0; rw [hy]; ring)
    p.lo p.hi ho

theorem transverse_plank (S : Shape) (p : Plank) (ho : p.lo < p.hi) (hy : p.u.2 ≠ 0) :
    ∃ k l u : ℝ, l < u ∧ p.set = oblique k l u ∧
      relativeWidth S p = (u-l)/rangeWidth S.body (direction (k,1)) ∧ p.u.1 = k*p.u.2 := by
  have hx : (direction p.u).linear (1,0) = p.u.1 := by simp [direction,dot]
  have hy' : (direction p.u).linear (0,1) = p.u.2 := by simp [direction,dot]
  obtain ⟨k,l,u,hu,hset,hw,hd⟩ :=
    transverse S (direction p.u) p.lo p.hi ho (by rwa [hy'])
  exact ⟨k,l,u,hu,hset,hw,by simpa only [hx,hy'] using hd⟩

end Quant.CrossedQuadrilateralBandPresentation

/-- info: 'Quant.CrossedQuadrilateralBandPresentation.transverse_plank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralBandPresentation.transverse_plank
