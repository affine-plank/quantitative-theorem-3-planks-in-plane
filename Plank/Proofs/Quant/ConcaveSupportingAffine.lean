/- Supporting affine majorants for finite-dimensional concave functions. -/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.LocallyConvex.Separation

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ConcaveSupportingAffine

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- At an interior point of its convex domain, a real concave function
has a global supporting affine majorant. Differentiability is not assumed. -/
theorem exists_majorant {S : Set E} {F : E → ℝ} (hF : ConcaveOn ℝ S F)
    (p : E) (hp : p ∈ interior S) :
    ∃ L : E →L[ℝ] ℝ, ∀ x ∈ S, F x ≤ F p+L (x-p) := by
  let H : Set (E × ℝ) := {v | v.1 ∈ S ∧ v.2 ≤ F v.1}
  have hH : Convex ℝ H := hF.convex_hypograph
  have hn : S ∈ 𝓝 p := mem_interior_iff_mem_nhds.mp hp
  have hc : ContinuousAt F p := hF.continuousOn_interior.continuousAt
    (isOpen_interior.mem_nhds hp)
  have hlow : (p,F p-1) ∈ interior H := by
    apply mem_interior_iff_mem_nhds.mpr
    have hf : ContinuousAt (fun v : E × ℝ => F v.1) (p,F p-1) :=
      hc.comp continuous_fst.continuousAt
    have hlt := continuous_snd.continuousAt.eventually_lt hf
      (by change F p-1 < F p; linarith)
    filter_upwards [(continuous_fst.tendsto (p,F p-1)).eventually hn,hlt] with v hv hlt
    exact ⟨hv,hlt.le⟩
  have hnot : (p,F p) ∉ interior H := by
    intro h
    have hh := preimage_interior_subset_interior_preimage
      (show Continuous (fun t : ℝ => (p,t)) by fun_prop) h
    simp only [H,preimage_ofPred_eq,interior_subset hp,true_and] at hh
    change F p ∈ interior (Iic (F p)) at hh
    simp only [interior_Iic,mem_Iio,lt_self_iff_false] at hh
  obtain ⟨Λ,hΛne,hΛ⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hH hnot ⟨_,hlow⟩
  let A : E →L[ℝ] ℝ := Λ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let b : ℝ := Λ (0,1)
  have hΛeval (x : E) (y : ℝ) : Λ (x,y) = A x+y*b := by
    have he : (x,y) = (x,0)+y • (0,1) := by ext <;> simp
    rw [he,map_add,map_smul]
    rfl
  have hb : 0 < b := by
    have hh := (Λ.isOpenMap_of_ne_zero hΛne).mapsTo_interior
      (show MapsTo Λ H (Iic (Λ (p,F p))) from hΛ) hlow
    simp only [interior_Iic,mem_Iio,hΛeval] at hh
    linarith only [hh]
  refine ⟨-(b⁻¹ • A),?_⟩
  intro x hx
  have hh := hΛ (x,F x) ⟨hx,le_rfl⟩
  rw [hΛeval,hΛeval] at hh
  have halg : b*(F p+(-(b⁻¹ • A)) (x-p)) = b*F p+A p-A x := by
    change b*(F p+ -(b⁻¹*A (x-p))) = b*F p+A p-A x
    rw [map_sub]
    field_simp [hb.ne']
    ring
  apply le_of_mul_le_mul_left (a := b) _ hb
  rw [halg]
  linarith only [hh]

end Plank.ConcaveSupportingAffine

/-- info: 'Plank.ConcaveSupportingAffine.exists_majorant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.ConcaveSupportingAffine.exists_majorant
