/- An internal parallel section cannot be exhausted by a proper homothetic
copy whose center also has an internal level. This is the geometric
obstruction to gaps between positive parallel planks in an equality case. -/
module

public import Plank.Proofs.Quant.PlanarOnePlankVertices
public import Plank.Proofs.Quant.PlanarDirectionDerivatives

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelSections

open Set MeasureTheory Filter Topology PlanarQuantitative PlanarGapCells
  PlanarOnePlankShape PlanarDirectionDerivatives

theorem map_combo (f : Point →ᵃ[ℝ] ℝ) (x y : Point) (r : ℝ) :
    f ((1-r) • x+r • y) = (1-r)*f x+r*f y := by
  simpa only [AffineMap.lineMap_apply_module,AffineMap.lineMap_apply_ring,smul_eq_mul]
    using f.apply_lineMap x y r

/-- Every internal level meets the interior of a full-dimensional body. -/
theorem exists_interior_level {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ x ∈ interior K, f x = t := by
  obtain ⟨x,hx⟩ := PlanarGapAnalysis.interior_nonempty_of_area_pos hK hconv hV
  by_cases htx : t ≤ f x
  · let r := t/f x
    have hfx : 0 < f x := ht.trans_le htx
    have hr : 0 < r := div_pos ht hfx
    have hr1 : r ≤ 1 := (div_le_one hfx).mpr htx
    refine ⟨(1-r) • b+r • x,
      hconv.combo_self_interior_mem_interior hb hx (sub_nonneg.mpr hr1) hr
        (sub_add_cancel 1 r),?_⟩
    rw [map_combo,hfb,mul_zero,zero_add]
    exact div_mul_cancel₀ t hfx.ne'
  · let r := (1-t)/(1-f x)
    have hfx : 0 < 1-f x := by linarith only [htx,ht1]
    have hr : 0 < r := div_pos (sub_pos.mpr ht1) hfx
    have hr1 : r ≤ 1 := (div_le_one hfx).mpr (by linarith only [htx])
    refine ⟨(1-r) • a+r • x,
      hconv.combo_self_interior_mem_interior ha hx (sub_nonneg.mpr hr1) hr
        (sub_add_cancel 1 r),?_⟩
    rw [map_combo,hfa,mul_one]
    have hh : r*(1-f x) = 1-t := div_mul_cancel₀ _ hfx.ne'
    nlinarith only [hh]

/-- A nonconstant planar affine functional has a nonzero kernel direction. -/
theorem exists_kernel_direction (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) :
    ∃ v : Point, v ≠ 0 ∧ f.linear v = 0 := by
  let T := directionCoordinates f hf
  let v : Point := T.symm ![0,1]
  have he : T v = ![0,1] := T.apply_symm_apply _
  have hn : v ≠ 0 := by
    intro hz
    have hh := congrFun he 1
    rw [hz,map_zero] at hh
    norm_num at hh
  refine ⟨v,hn,?_⟩
  have hh := congrFun he 0
  rw [directionCoordinates_first] at hh
  rw [affine_eval] at hh
  simpa using hh

/-- An internal section of a positive-area body contains a point distinct
from any prescribed point on its supporting line. -/
theorem exists_ne_on_level {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    (z : Point) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ w ∈ K, f w = t ∧ w ≠ z := by
  obtain ⟨x,hx,hfx⟩ := exists_interior_level hK hconv hV f a b ha hb hfa hfb ht ht1
  by_cases hxz : x = z
  · have hf : f.linear ≠ 0 := by
      intro hzero
      obtain ⟨c,hc⟩ := f.linear_eq_zero_iff_exists_const.mp hzero
      have he : f a = f b := by rw [hc]; rfl
      rw [hfa,hfb] at he
      norm_num at he
    obtain ⟨v,hv,hfv⟩ := exists_kernel_direction f hf
    have hc : Continuous (fun r : ℝ => x+r • v) := by fun_prop
    have hev : ∀ᶠ r : ℝ in 𝓝 0, x+r • v ∈ K := by
      have hm : K ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
      have hc0 : Tendsto (fun r : ℝ => x+r • v) (𝓝 0) (𝓝 x) := by
        simpa only [ContinuousAt,zero_smul,add_zero] using
          (hc.continuousAt : ContinuousAt (fun r : ℝ => x+r • v) 0)
      exact hc0.eventually hm
    obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hd : dist (ε/2) (0 : ℝ) < ε := by
      rw [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < ε/2)]
      linarith
    refine ⟨x+(ε/2) • v,hball hd,?_,?_⟩
    · rw [affine_eval,map_add,map_smul,hfv,smul_zero,add_zero,← affine_eval,hfx]
    · intro he
      have hh : (ε/2) • v = 0 := by rw [← hxz] at he; exact add_left_cancel (he.trans (add_zero x).symm)
      exact hv ((smul_eq_zero.mp hh).resolve_left (ne_of_gt (by positivity : 0 < ε/2)))
  · exact ⟨x,interior_subset hx,hfx,hxz⟩

/-- A nonempty compact set cannot contain a nontrivial translate of itself. -/
theorem translation_eq_zero {S : Set Point} (hS : IsCompact S) (hne : S.Nonempty)
    (v : Point) (hmove : ∀ x ∈ S, x+v ∈ S) : v = 0 := by
  ext i
  obtain ⟨a,ha,hmax⟩ := hS.exists_isMaxOn hne (continuous_apply i).continuousOn
  obtain ⟨b,hb,hmin⟩ := hS.exists_isMinOn hne (continuous_apply i).continuousOn
  have hu : a i+v i ≤ a i := hmax (hmove a ha)
  have hl : b i ≤ b i+v i := hmin (hmove b hb)
  change v i = 0
  linarith only [hu,hl]

def homotheticCopy (K : Set Point) (q : ℝ) (z : Point) : Set Point :=
  (fun x => q • x+(1-q) • z) '' K

/-- If one entire nonempty section fits in a homothetic copy, the section
through the center must be a singleton. Compactness gives the rigidity. -/
theorem section_singleton_of_copy {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (z : Point) (t : ℝ) (hne : (levelSection K f t).Nonempty)
    (hcopy : levelSection K f t ⊆ homotheticCopy K q z) :
    levelSection K f (f z) ⊆ {z} := by
  let u := (t-(1-q)*f z)/q
  let S := levelSection K f u
  have heval (x y : Point) : f (q • x+(1-q) • y) = q*f x+(1-q)*f y := by
    simpa only [sub_sub_cancel] using map_combo f x y (1-q)
  have hS : IsCompact S := hK.inter_right (isClosed_eq (continuous_form f) continuous_const)
  have hSnon : S.Nonempty := by
    obtain ⟨y,hy⟩ := hne
    obtain ⟨x,hx,he⟩ := hcopy hy
    refine ⟨x,hx,?_⟩
    have hh := congrArg f he
    rw [heval,hy.2] at hh
    dsimp [u]
    apply (eq_div_iff hq.ne').mpr
    linarith only [hh]
  intro w hw
  let v := ((1-q)/q) • (w-z)
  have hmove : ∀ x ∈ S, x+v ∈ S := by
    intro x hx
    have hy : q • x+(1-q) • w ∈ levelSection K f t := by
      refine ⟨hconv hx.1 hw.1 hq.le (sub_pos.mpr hq1).le (by ring),?_⟩
      change f (q • x+(1-q) • w) = t
      rw [heval,hx.2,hw.2]
      dsimp [u]
      field_simp
      ring
    obtain ⟨x',hx',he⟩ := hcopy hy
    have hxx : x' = x+v := by
      ext i
      have hh := congrFun he i
      change q*x' i+(1-q)*z i = q*x i+(1-q)*w i at hh
      change x' i = x i+((1-q)/q)*(w i-z i)
      apply (mul_left_cancel₀ hq.ne')
      field_simp
      nlinarith only [hh]
    have hfx' : f x' = u := by
      have hh := congrArg f he
      rw [heval,heval,hx.2,hw.2] at hh
      nlinarith only [hh,hq]
    exact hxx ▸ And.intro hx' hfx'
  have hv := translation_eq_zero hS hSnon v hmove
  have hn : (1-q)/q ≠ 0 := ne_of_gt (div_pos (sub_pos.mpr hq1) hq)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hv).resolve_left hn)

/-- A full internal section cannot fit into a proper homothetic copy whose
center has an internal level. This holds for every compact convex planar
body of positive area, with no polygon hypothesis. -/
theorem not_section_subset_copy {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : Point →ᵃ[ℝ] ℝ)
    (a b : Point) (ha : a ∈ K) (hb : b ∈ K) (hfa : f a = 1) (hfb : f b = 0)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (z : Point)
    (hz : 0 < f z) (hz1 : f z < 1) (t : ℝ)
    (hne : (levelSection K f t).Nonempty) :
    ¬ levelSection K f t ⊆ homotheticCopy K q z := by
  intro hcopy
  obtain ⟨w,hw,hfw,hwz⟩ := exists_ne_on_level hK hconv hV f a b ha hb hfa hfb z hz hz1
  exact hwz (section_singleton_of_copy hK hconv f hq hq1 z t hne hcopy ⟨hw,hfw⟩)

end Plank.PlanarParallelSections

/-- info: 'Plank.PlanarParallelSections.not_section_subset_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelSections.not_section_subset_copy
