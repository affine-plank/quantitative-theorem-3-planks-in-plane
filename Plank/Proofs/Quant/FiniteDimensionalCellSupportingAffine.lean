/- Actual convex-cell support geometry in every positive dimension.
The planar and spatial APIs specialize this common proof. -/
module

public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells
public import Plank.Proofs.Quant.FiniteDimensionalCapWindowCore
public import Plank.Proofs.Quant.ConcaveSupportingAffine
public import Plank.Measure.ConvexBody
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Order.LeftRight

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalCellSupportingAffine

open Set MeasureTheory Filter FiniteDimensionalCapWindowScaling
open scoped Topology Pointwise

variable {d : ℕ}

theorem interior_nonempty_of_volume_pos {K : Set (Point d)} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hvolume : 0 < (volume K).toReal) : (interior K).Nonempty :=
  ConvexBodyMeasure.interior_nonempty_of_measure_pos volume hK hconv hvolume


variable {κ : Type*} [Fintype κ]

theorem relaxed_volume_pos {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : κ → (Point d) →L[ℝ] ℝ) (u : κ → ℝ)
    (hne : (cell K f u).Nonempty) (ε : ℝ) (hε : 0 < ε) :
    0 < (volume (cell K f (u+ε • (1 : κ → ℝ)))).toReal := by
  let O : Set (Point d) := ⋂ i, {x | f i x < u i+ε}
  have hO : IsOpen O := isOpen_iInter_of_finite fun i =>
    isOpen_lt (f i).continuous continuous_const
  have hint := interior_nonempty_of_volume_pos hK hconv hV
  have hclosure : closure (interior K) = K :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hint).trans hK.isClosed.closure_eq
  have hmeet : (interior K ∩ O).Nonempty := by
    apply (closure_inter_open_nonempty_iff hO).mp
    obtain ⟨x,hxK,hxu⟩ := hne
    refine ⟨x,by rwa [hclosure],mem_iInter.mpr fun i => ?_⟩
    exact (mem_iInter.mp hxu i).trans_lt (lt_add_of_pos_right _ hε)
  have hsub : interior K ∩ O ⊆ cell K f (u+ε • (1 : κ → ℝ)) := by
    intro x hx
    refine ⟨interior_subset hx.1,mem_iInter.mpr fun i => ?_⟩
    simpa only [mem_ofPred_eq,Pi.add_apply,Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one] using
      (show f i x < u i+ε from mem_iInter.mp hx.2 i).le
  have hmeasure : 0 < volume (cell K f (u+ε • (1 : κ → ℝ))) :=
    ((isOpen_interior.inter hO).measure_pos volume hmeet).trans_le (measure_mono hsub)
  exact ENNReal.toReal_pos hmeasure.ne' (isCompact_cell hK f _).measure_ne_top

/-- One point satisfying all cuts strictly puts the offsets in the interior
of the feasible offset set. -/
theorem interior_of_strict_feasible {K : Set (Point d)} (f : κ → (Point d) →L[ℝ] ℝ)
    (u : κ → ℝ) (x : (Point d)) (hx : x ∈ K) (hstrict : ∀ i, f i x < u i) :
    u ∈ interior {v | (cell K f v).Nonempty} := by
  let O : Set (κ → ℝ) := ⋂ i, {v | f i x < v i}
  have hO : IsOpen O := isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (continuous_apply i)
  have hsub : O ⊆ {v | (cell K f v).Nonempty} := by
    intro v hv
    refine ⟨x,hx,mem_iInter.mpr fun i => ?_⟩
    exact (show f i x < v i from mem_iInter.mp hv i).le
  exact interior_maximal hsub hO (mem_iInter.mpr hstrict)

/-- A positive-volume cell contains a point outside every cut boundary,
so its offsets are interior feasible parameters. -/
theorem interior_of_volume_pos {K : Set (Point d)} (f : κ → (Point d) →L[ℝ] ℝ)
    (hf : ∀ i, f i ≠ 0) (u : κ → ℝ) (hpos : 0 < (volume (cell K f u)).toReal) :
    u ∈ interior {v | (cell K f v).Nonempty} := by
  let N : Set (Point d) := ⋃ i, {x | f i x = u i}
  have hN : volume N = 0 := measure_iUnion_null fun i =>
    LinearBands.measure_level_zero volume (f i) (hf i) (u i)
  have hpositive : 0 < (volume (cell K f u \ N)).toReal := by
    rw [measure_sdiff_null hN]
    exact hpos
  obtain ⟨x,hx,hxN⟩ := nonempty_of_measureReal_ne_zero hpositive.ne'
  apply interior_of_strict_feasible f u x hx.1
  intro i
  apply lt_of_le_of_ne (show f i x ≤ u i from mem_iInter.mp hx.2 i)
  intro he
  exact hxN (mem_iUnion.mpr ⟨i,he⟩)

/-- Interior feasible offsets give positive volume, by first tightening all
cuts slightly and then applying the actual relaxation-volume theorem. -/
theorem volume_pos_of_interior {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : κ → (Point d) →L[ℝ] ℝ) (u : κ → ℝ)
    (hu : u ∈ interior {v | (cell K f v).Nonempty}) :
    0 < (volume (cell K f u)).toReal := by
  have ht : Tendsto (fun t : ℝ => u-t • (1 : κ → ℝ)) (𝓝 0) (𝓝 u) := by
    simpa only [zero_smul,sub_zero] using
      (show Continuous (fun t : ℝ => u-t • (1 : κ → ℝ)) by fun_prop).tendsto (0 : ℝ)
  obtain ⟨ε,hε,hi⟩ := (ht.eventually (isOpen_interior.mem_nhds hu)).exists_gt
  simpa only [sub_add_cancel] using
    relaxed_volume_pos hK hconv hV f _ (interior_subset hi) ε hε

/-- At a positive cell, the dimension-root of volume admits a global affine majorant
on all nonempty cells. No chart or differentiability premise is used. -/
theorem exists_root_majorant {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → (Point d) →L[ℝ] ℝ) (hf : ∀ i, f i ≠ 0) (u : κ → ℝ)
    (hpos : 0 < (volume (cell K f u)).toReal) :
    ∃ L : (κ → ℝ) →L[ℝ] ℝ, ∀ v, (cell K f v).Nonempty →
      volumeRoot (cell K f v) ≤
        volumeRoot (cell K f u)+L (v-u) :=
  ConcaveSupportingAffine.exists_majorant (concaveOn_volumeRoot_cell hK hconv f) u
    (interior_of_volume_pos f hf u hpos)

/-- A zero-volume cell, including a nonempty degenerate cell on an initial
chart wall, has a linear constraint preserving zero volume on the whole line.
This removes the need to assume that the base cell is empty. -/
theorem exists_zero_volume_constraint {K : Set (Point d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal) (f : κ → (Point d) →L[ℝ] ℝ)
    (hf : ∀ i, f i ≠ 0) (u : κ → ℝ) (hzero : (volume (cell K f u)).toReal = 0) :
    ∃ L : (κ → ℝ) →L[ℝ] ℝ, L ≠ 0 ∧ ∀ z, L z = 0 → ∀ t : ℝ,
      (volume (cell K f (u+t • z))).toReal = 0 := by
  have hnot : u ∉ interior {v | (cell K f v).Nonempty} := by
    intro hi
    have hh := volume_pos_of_interior hK hconv hV f u hi
    rw [hzero] at hh
    exact lt_irrefl 0 hh
  have hint : (interior {v | (cell K f v).Nonempty}).Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨fun i => f i x+1,interior_of_strict_feasible f _ x hx (fun i => by linarith)⟩
  obtain ⟨L,hL⟩ := geometric_hahn_banach_open_point
    (convex_feasible hconv f).interior isOpen_interior hnot
  refine ⟨L,?_,?_⟩
  · intro hzero
    obtain ⟨v,hv⟩ := hint
    simpa [hzero] using hL v hv
  intro z hz t
  by_contra hn
  have hpos : 0 < (volume (cell K f (u+t • z))).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hn)
  have hi := interior_of_volume_pos f hf (u+t • z) hpos
  have hLu : L (u+t • z) = L u := by rw [map_add,map_smul,hz,smul_zero,add_zero]
  exact (ne_of_lt (hL _ hi)) hLu


/-- Actual positive-volume cells have local affine-power upper bounds, in
all positive dimensions. The neighborhood keeps odd powers nonnegative. -/
theorem exists_local_power_majorant
    {K : Set (Point d)} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : κ → Point d →L[ℝ] ℝ) (hf : ∀ i, f i ≠ 0) (u : κ → ℝ)
    (hpos : 0 < (volume (cell K f u)).toReal) :
    ∃ L : (κ → ℝ) →L[ℝ] ℝ, ∀ᶠ v in 𝓝 u,
      0 < volumeRoot (cell K f u)+L (v-u) ∧
      (volume (cell K f v)).toReal ≤ (volumeRoot (cell K f u)+L (v-u))^(d+1) := by
  obtain ⟨L,hL⟩ := exists_root_majorant hK hc f hf u hpos
  have hb : 0 < volumeRoot (cell K f u) := Real.rpow_pos_of_pos hpos _
  have hcont : Continuous (fun v : κ → ℝ => volumeRoot (cell K f u)+L (v-u)) := by
    fun_prop
  have hnear := hcont.continuousAt.eventually
    (isOpen_Ioi.mem_nhds (show (0 : ℝ) < volumeRoot (cell K f u)+L (u-u) by simpa using hb))
  refine ⟨L,?_⟩
  filter_upwards [hnear] with v hv
  refine ⟨hv,?_⟩
  by_cases hne : (cell K f v).Nonempty
  · have hp := pow_le_pow_left₀ (volumeRoot_nonneg (cell K f v)) (hL v hne) (d+1)
    rwa [volumeRoot_pow] at hp
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne,measure_empty,ENNReal.toReal_zero]
    exact pow_nonneg hv.le _

end Plank.FiniteDimensionalCellSupportingAffine

#print axioms Plank.FiniteDimensionalCellSupportingAffine.concaveOn_volumeRoot_cell

#print axioms Plank.FiniteDimensionalCellSupportingAffine.exists_root_majorant

#print axioms Plank.FiniteDimensionalCellSupportingAffine.exists_zero_volume_constraint

#print axioms Plank.FiniteDimensionalCellSupportingAffine.exists_local_power_majorant
