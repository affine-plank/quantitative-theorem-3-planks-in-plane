/- No thin non-diagonal equality near a calibrated diagonal boundary configuration. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralInnerPacking

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralBoundaryNeighborhood
open Set MeasureTheory Filter CrossedQuadrilateralAttainment
open CrossedQuadrilateralInnerPacking CrossedQuadrilateralResidualArea
open CrossedQuadrilateralThinExtension
open scoped Topology

/-- A null band may have any position. A positive band has its calibrated endpoints. -/
def Calibrated (p n r lo hi : ℝ) : Prop :=
  (r = 0 ∧ lo = hi) ∨ (lo = -n*r ∧ hi = p*r)

theorem calibrated_width {p n r lo hi : ℝ} (hp : 0 < p) (hn : 0 < n)
    (h : Calibrated p n r lo hi) : (hi-lo)/(p+n) = r := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simp
  · field_simp [(add_pos hp hn).ne']
    ring

theorem calibrated_of_balanced {p n lo hi : ℝ} (hp : 0 < p) (hn : 0 < n)
    (h : hi = lo ∨ hi/p = -lo/n) :
    Calibrated p n ((hi-lo)/(p+n)) lo hi := by
  rcases h with rfl | h
  · exact Or.inl ⟨by simp,rfl⟩
  · right
    have he : hi*n = -lo*p := (div_eq_div_iff hp.ne' hn.ne').mp h
    constructor <;> field_simp [(add_pos hp hn).ne'] <;> nlinarith only [he]

theorem eventually_inner {α : Type*} {F : Filter α} {p n r lo₀ hi₀ θ : ℝ}
    (hp : 0 < p) (hn : 0 < n) (hr : 0 ≤ r) (hθ : θ < 1)
    (hc : Calibrated p n r lo₀ hi₀) {lo hi : α → ℝ}
    (hl : Tendsto lo F (𝓝 lo₀)) (hu : Tendsto hi F (𝓝 hi₀)) :
    ∀ᶠ x in F, Inner p n (θ*r) (lo x) (hi x) := by
  by_cases hz : r = 0
  · exact Filter.Eventually.of_forall (fun _ => Or.inl (by rw [hz,mul_zero]))
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
  obtain ⟨rfl,rfl⟩ := hc.resolve_left (fun h => hz h.1)
  have hl' : -n*r < -n*(θ*r) := by
    have hh := mul_pos hn (mul_pos (sub_pos.mpr hθ) hrp)
    nlinarith only [hh]
  have hu' : p*(θ*r) < p*r := by
    have hh := mul_pos hp (mul_pos (sub_pos.mpr hθ) hrp)
    nlinarith only [hh]
  filter_upwards [hl.eventually_lt_const hl',hu.eventually_const_lt hu'] with x hx hy
  exact Or.inr ⟨hx.le,hy.le⟩

theorem exists_inner_parameters {A B r s : ℝ} (hB : B < 2*A)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r+s < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ θ*r+θ*s < 1 ∧
      (1-θ*r-θ*s)*B < 2*(1-r-s)*A := by
  have hstrict : (1-(1:ℝ)*r-1*s)*B < 2*(1-r-s)*A := by
    have hh := mul_pos (by linarith only [hrs] : 0 < 1-r-s) (sub_pos.mpr hB)
    nlinarith only [hh]
  have he : ∀ᶠ θ in 𝓝 (1 : ℝ), (1-θ*r-θ*s)*B < 2*(1-r-s)*A :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds hstrict
  have hp : ∀ᶠ θ in 𝓝 (1 : ℝ), 0 < θ := eventually_gt_nhds zero_lt_one
  have hl : ∀ᶠ θ in 𝓝[<] (1 : ℝ), θ < 1 := self_mem_nhdsWithin
  obtain ⟨θ,⟨hineq,hpos⟩,hlt⟩ :=
    (((he.and hp).filter_mono nhdsWithin_le_nhds).and hl).exists
  refine ⟨θ,hpos,hlt,?_,hineq⟩
  have hx := mul_le_mul_of_nonneg_right hlt.le hr
  have hy := mul_le_mul_of_nonneg_right hlt.le hs
  nlinarith only [hx,hy,hrs]

/-- Along any convergent family of diagonal endpoints with a calibrated limit,
two fixed non-diagonal slopes cannot be sharp when their total actual width is
positive and tends to zero. Neither their placements nor their overlap must converge.
Null diagonal limit bands are permitted at arbitrary positions. -/
theorem eventually_strict {α : Type*} {F : Filter α} (S : Shape)
    (k : Fin 2 → ℝ) (hk : ∀ i, k i ≠ 0)
    {r s lx₀ ux₀ ly₀ uy₀ : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r+s < 1)
    (hcx : Calibrated S.a S.c r lx₀ ux₀) (hcy : Calibrated S.b S.d s ly₀ uy₀)
    (lx ux ly uy : α → ℝ) (lo hi : α → Fin 2 → ℝ)
    (hlx : Tendsto lx F (𝓝 lx₀)) (hux : Tendsto ux F (𝓝 ux₀))
    (hly : Tendsto ly F (𝓝 ly₀)) (huy : Tendsto uy F (𝓝 uy₀))
    (ht : Tendsto (fun x => total S k (lo x) (hi x)) F (𝓝 0)) :
    ∀ᶠ x in F, lx x ≤ ux x → ly x ≤ uy x → (∀ i, lo x i ≤ hi x i) →
      0 < total S k (lo x) (hi x) →
      (1-budget S (lx x) (ux x) (ly x) (uy x)-total S k (lo x) (hi x))^2*
        (volume S.body).toReal <
      (volume (axisGap S (lx x) (ux x) (ly x) (uy x) \
        ⋃ i, band (k i) (lo x i) (hi x i))).toReal := by
  obtain ⟨B,hB0,hB,hbound⟩ := strict_extension S k hk
  obtain ⟨θ,hθ0,hθ1,hθsum,hθbound⟩ := exists_inner_parameters hB hr hs hrs
  have hx := eventually_inner S.ha S.hc hr hθ1 hcx hlx hux
  have hy := eventually_inner S.hb S.hd hs hθ1 hcy hly huy
  have hbudget : Tendsto (fun x => budget S (lx x) (ux x) (ly x) (uy x)) F (𝓝 (r+s)) := by
    have hh := ((hux.sub hlx).div_const (S.a+S.c)).add
      ((huy.sub hly).div_const (S.b+S.d))
    rw [calibrated_width S.ha S.hc hcx,calibrated_width S.hb S.hd hcy] at hh
    exact hh
  have hleft := ht.mul_const (volume S.body).toReal
  have hright := ((((tendsto_const_nhds : Tendsto (fun _ : α => (1 : ℝ)) F (𝓝 1)).sub hbudget).const_mul 2).mul_const
    (volume S.body).toReal).sub_const ((1-θ*r-θ*s)*B)
  have hstrict : 0*(volume S.body).toReal <
      2*(1-(r+s))*(volume S.body).toReal-(1-θ*r-θ*s)*B := by
    nlinarith only [hθbound]
  filter_upwards [hx,hy,hbudget.eventually_lt_const hrs,hleft.eventually_lt hright hstrict]
    with x hix hiy hbudget' hsmall
  intro hox hoy ho hpos
  exact hbound (θ*r) (θ*s) (mul_nonneg hθ0.le hr) (mul_nonneg hθ0.le hs) hθsum
    (lx x) (ux x) (ly x) (uy x) hox hoy hbudget' hix hiy (lo x) (hi x) ho hpos hsmall

end Quant.CrossedQuadrilateralBoundaryNeighborhood

/-- info: 'Quant.CrossedQuadrilateralBoundaryNeighborhood.eventually_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralBoundaryNeighborhood.eventually_strict
