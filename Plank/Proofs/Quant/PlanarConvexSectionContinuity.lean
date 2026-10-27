/- Continuity up to the supporting lines, including nontrivial supporting faces. -/
module

public import Plank.Proofs.Quant.PlanarConvexSectionIntegral
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarConvexSectionContinuity

open Set MeasureTheory Filter ConvexSections PlanarConvexSectionLength
open scoped Topology

/-- Compactness prevents an upward jump in the length of neighboring
sections. This statement includes the supporting lines. -/
theorem upperSemicontinuous_length {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) : UpperSemicontinuous (length K) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro v
  by_cases hv : v ≤ 0
  · have he : length K ⁻¹' Ici v = univ := by
      ext t
      simp only [mem_preimage,mem_Ici,mem_univ,iff_true]
      exact hv.trans ENNReal.toReal_nonneg
    rw [he]
    exact isClosed_univ
  have hvp : 0 < v := lt_of_not_ge hv
  let S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := (K ×ˢ K) ∩
    {p | p.1.1 = p.2.1 ∧ v ≤ p.2.2-p.1.2}
  have hS : IsCompact S := (hK.prod hK).inter_right
    ((isClosed_eq (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1)
      (g := fun p => p.2.1) (by fun_prop) (by fun_prop)).inter
      (isClosed_le (f := fun _ : (ℝ × ℝ) × (ℝ × ℝ) => v)
        (g := fun p => p.2.2-p.1.2) continuous_const (by fun_prop)))
  have he : length K ⁻¹' Ici v = (fun p : (ℝ × ℝ) × (ℝ × ℝ) => p.1.1) '' S := by
    ext t
    constructor
    · intro ht
      have hn : (fiber K t).Nonempty := by
        by_contra hh
        have hz := not_nonempty_iff_eq_empty.mp hh
        have ht' : v ≤ length K t := ht
        simp only [length,hz,measure_empty,ENNReal.toReal_zero] at ht'
        exact hv ht'
      obtain ⟨y,hy⟩ := hn
      have htK : t ∈ Prod.fst '' K := ⟨(t,y),hy,rfl⟩
      obtain ⟨a,b,hab,hI⟩ := fiber_interval hK hc htK
      have ha : (t,a) ∈ K := by change a ∈ fiber K t; rw [hI]; exact ⟨le_rfl,hab⟩
      have hb : (t,b) ∈ K := by change b ∈ fiber K t; rw [hI]; exact ⟨hab,le_rfl⟩
      refine ⟨((t,a),(t,b)),⟨⟨ha,hb⟩,rfl,?_⟩,rfl⟩
      change v ≤ length K t at ht
      rw [length,hI] at ht
      exact (Real.volume_real_Icc_of_le hab) ▸ ht
    · rintro ⟨⟨⟨x,a⟩,⟨y,b⟩⟩,⟨⟨ha,hb⟩,hxy,hab⟩,rfl⟩
      dsimp only at hxy hab
      subst y
      have hab' : a ≤ b := by linarith only [hvp,hab]
      have hs : Icc a b ⊆ fiber K x := (convex_fiber hc x).ordConnected.out ha hb
      have hm : (volume (Icc a b)).toReal ≤ length K x :=
        ENNReal.toReal_mono (compact_fiber hK x).measure_ne_top (measure_mono hs)
      change v ≤ length K x
      exact hab.trans ((Real.volume_real_Icc_of_le hab') ▸ hm)
  rw [he]
  exact (hS.image (by fun_prop)).isClosed

/-- A normalized convex body's actual section length is continuous on
its closed support interval, even when a supporting section has positive
length. No polygon or transversality assumption is used. -/
theorem continuousOn_length_unit {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hfull : (interior K).Nonempty)
    (hproj : Prod.fst '' K = Icc (0 : ℝ) 1) :
    ContinuousOn (length K) (Icc (0 : ℝ) 1) := by
  have hconc : ConcaveOn ℝ (Icc (0 : ℝ) 1) (length K) := by
    rw [← hproj]
    exact concaveOn_length hK hc
  let g (t : ℝ) := (1-t)*length K 0+t*length K 1
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hgf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t ≤ length K t := by
    have hh := hconc.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel 1 t)
    simpa only [smul_eq_mul,mul_zero,mul_one,zero_add,g] using hh
  have hend (x : ℝ) (hx : x = 0 ∨ x = 1) :
      ContinuousWithinAt (length K) (Icc (0 : ℝ) 1) x := by
    apply continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr
    refine ⟨?_,(upperSemicontinuous_length hK hc).upperSemicontinuousWithinAt _ x⟩
    intro v hv
    have hxeq : g x = length K x := by rcases hx with rfl | rfl <;> simp [g]
    have hev := hg.continuousAt.eventually_const_lt (hxeq ▸ hv)
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht hti
    exact ht.trans_le (hgf t hti)
  intro x hx
  by_cases hx0 : x = 0
  · exact hend x (Or.inl hx0)
  by_cases hx1 : x = 1
  · exact hend x (Or.inr hx1)
  have hi : x ∈ interior (Prod.fst '' K) := by
    rw [hproj,interior_Icc]
    exact ⟨lt_of_le_of_ne hx.1 (fun h => hx0 h.symm),lt_of_le_of_ne hx.2 hx1⟩
  exact (continuousAt_section_measure (volume : Measure ℝ) hK hc hfull hi).continuousWithinAt

end Plank.PlanarConvexSectionContinuity

/-- info: 'Plank.PlanarConvexSectionContinuity.continuousOn_length_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarConvexSectionContinuity.continuousOn_length_unit
