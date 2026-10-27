/- Compact collinear sections in real normed spaces. -/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.CollinearSections

open Set
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact nonempty convex collinear set is a closed segment, also when it
is a singleton. No finite-dimensional ambient-space assumption is needed. -/
theorem eq_segment_of_collinear {S : Set E} (hS : IsCompact S)
    (hconv : Convex ℝ S) (hne : S.Nonempty) (hline : Collinear ℝ S) :
    ∃ c ∈ S, ∃ d ∈ S, S = segment ℝ c d := by
  obtain ⟨p,hp⟩ := hne
  obtain ⟨v,hv⟩ := (collinear_iff_of_mem hp).mp hline
  by_cases hv0 : v = 0
  · refine ⟨p,hp,p,hp,?_⟩
    rw [segment_same]
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨r,hr⟩ := hv x hx
      simpa [hv0] using hr
    · exact singleton_subset_iff.mpr hp
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap p (p+v)
  have hL (t : ℝ) : L t = p+t • v := by
    simp [L,AffineMap.lineMap_apply_module',add_comm]
  let T := L ⁻¹' S
  have hTc : IsCompact T := by
    have he := (Homeomorph.addLeft p).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (𝕜 := ℝ) hv0)
    change IsCompact ((fun t => L t) ⁻¹' S)
    simp_rw [hL]
    exact he.isCompact_preimage hS
  have hTconv : Convex ℝ T := hconv.affine_preimage L
  have hTne : T.Nonempty := ⟨0,by simpa [T,hL] using hp⟩
  have hl : sInf T ∈ T := hTc.sInf_mem hTne
  have hu : sSup T ∈ T := hTc.sSup_mem hTne
  have hlu : sInf T ≤ sSup T := csInf_le hTc.bddBelow hu
  have hT : T = Icc (sInf T) (sSup T) := by
    apply Set.Subset.antisymm
    · exact fun _ ht => ⟨csInf_le hTc.bddBelow ht,le_csSup hTc.bddAbove ht⟩
    · exact hTconv.ordConnected.out hl hu
  have hST : S = L '' T := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨r,hr⟩ := hv x hx
      have hxL : L r = x := by simpa only [hL,vadd_eq_add,add_comm] using hr.symm
      exact ⟨r,by change L r ∈ S; rwa [hxL],hxL⟩
    · rintro _ ⟨r,hr,rfl⟩
      exact hr
  refine ⟨L (sInf T),hl,L (sSup T),hu,?_⟩
  calc
    S = L '' T := hST
    _ = L '' Icc (sInf T) (sSup T) := congrArg (fun U => L '' U) hT
    _ = segment ℝ (L (sInf T)) (L (sSup T)) := by
      rw [← segment_eq_Icc hlu,image_segment]

/-- Independent affine coordinates cut out at most a line when their number is
at least the ambient dimension minus one. -/
theorem collinear_common_fiber [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (f : ι → E →ᵃ[ℝ] ℝ) (t : ι → ℝ)
    (hind : LinearIndependent ℝ (fun i => (f i).linear))
    (hdim : Module.finrank ℝ E ≤ Fintype.card ι+1) :
    Collinear ℝ {x | ∀ i, f i x = t i} := by
  let W := Submodule.span ℝ (range (fun i => (f i).linear))
  have hdimW : Module.finrank ℝ W = Fintype.card ι := finrank_span_eq_card hind
  have hdimA : Module.finrank ℝ W.dualCoannihilator ≤ 1 := by
    have hh := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    rw [hdimW] at hh
    omega
  apply collinear_iff_finrank_le_one.mpr
  apply (Submodule.finrank_mono (show vectorSpan ℝ {x | ∀ i, f i x = t i} ≤
    W.dualCoannihilator from ?_)).trans hdimA
  rw [vectorSpan_def,Submodule.span_le]
  rintro _ ⟨x,hx,y,hy,rfl⟩
  change x-y ∈ (↑W.dualCoannihilator : Set E)
  rw [Submodule.coe_dualCoannihilator_span]
  rintro g ⟨i,rfl⟩
  simpa only [vsub_eq_sub,hx i,hy i,sub_self] using (f i).linearMap_vsub x y

/-- A nonconstant affine level section is a segment in dimension at most two. -/
theorem levelSection_eq_segment [FiniteDimensional ℝ E] {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hdim : Module.finrank ℝ E ≤ 2)
    (f : E →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (t : ℝ)
    (hne : (K ∩ {x | f x = t}).Nonempty) :
    ∃ c ∈ K ∩ {x | f x = t}, ∃ d ∈ K ∩ {x | f x = t},
      K ∩ {x | f x = t} = segment ℝ c d := by
  have hfiber : Collinear ℝ {x | f x = t} := by
    simpa using collinear_common_fiber (fun _ : Unit => f) (fun _ => t)
      (linearIndependent_unique_iff.mpr hf) (by simpa using hdim)
  exact eq_segment_of_collinear
    (hK.inter_right (isClosed_eq f.continuous_of_finiteDimensional continuous_const))
    (hconv.inter ((convex_singleton t).affine_preimage f)) hne
    (hfiber.subset inter_subset_right)

end Plank.CollinearSections
