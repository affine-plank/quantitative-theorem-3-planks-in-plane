/- Common upper scaling for actual two-plank cells without area charts. -/
module

public import Plank.Proofs.Quant.PlanarEndpointMajorants
public import Plank.Proofs.Quant.EqualitySupportingRank

public import Plank.Proofs.Quant.PlanarTwoPlank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarChartFreeScaling

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPlankCellCharts PlanarPositiveCellRank QuadraticChartCalculus PlanarPolygonCharts
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

/-- At any interior tight two-plank configuration, a nonzero endpoint
direction makes every actual cell area at most its initial area times
one common square. Zero-area cells remain zero on the entire line.
The body is any compact convex planar set of positive area. -/
theorem exists_common_upper_scaling {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p : Endpoints 2) (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ z : Endpoints 2, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      (deficit K f 1).linear z = (1-budget K f p)*c ∧
      ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
        (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
  classical
  let A (s : Finset (Fin 2)) (e : Endpoints 2) :=
    (volume (signCell K f e.1 e.2 s)).toReal
  let S : Finset (Finset (Fin 2)) := Finset.univ.filter (fun s => 0 < A s p)
  have hS (s) : s ∈ S ↔ 0 < A s p := by simp [S]
  have hzero (s) (hs : s ∉ S) : A s p = 0 :=
    le_antisymm (le_of_not_gt (fun hh => hs ((hS s).mpr hh))) ENNReal.toReal_nonneg
  have hmaj (s : S) : ∃ G : Endpoints 2 →L[ℝ] ℝ, ∀ e,
      A s e ≤ (Real.sqrt (A s p)+G (e-p))^2 :=
    PlanarEndpointMajorants.exists_majorant hK hconv hne f hW s p ((hS s).mp s.property)
  choose G hG using hmaj
  have hconstraints (s : {s // s ∉ S}) : ∃ L : Endpoints 2 →ₗ[ℝ] ℝ,
      ∀ z, L z = 0 → ∀ t : ℝ, A s (p+t • z) = 0 :=
    PlanarEndpointMajorants.exists_zero_constraint hK hconv hne hV f hW s p
      (hzero s s.property)
  choose L hL using hconstraints
  let Z := LinearMap.pi L
  let H := LinearMap.ker Z
  let M (s : S) : H →L[ℝ] ℝ := (G s).comp H.subtypeL
  let b (s : S) := Real.sqrt (A s p)
  let V := (volume K).toReal
  let q := 1-budget K f p
  let d : H →L[ℝ] ℝ := (deficit K f 1).linear.toContinuousLinearMap.comp H.subtypeL
  have hzcell (x : H) (s : Finset (Fin 2)) (hs : s ∉ S) (t : ℝ) :
      A s (p+t • (x : Endpoints 2)) = 0 := by
    have hh : Z (x : Endpoints 2) = 0 := x.property
    exact hL ⟨s,hs⟩ x (congrFun hh ⟨s,hs⟩) t
  have hsum (x : H) (t : ℝ) :
      (∑ s : S, A s (p+t • (x : Endpoints 2))) =
        ∑ s, A s (p+t • (x : Endpoints 2)) := by
    rw [Finset.sum_coe_sort S (fun s => A s (p+t • (x : Endpoints 2)))]
    exact Finset.sum_subset (Finset.subset_univ _) (fun s _ hs => hzcell x s hs t)
  have hbase : (∑ s : S, (b s)^2) = V*q^2 := by
    have hsq (s : S) : (b s)^2 = A s p := Real.sq_sqrt ENNReal.toReal_nonneg
    simp only [hsq]
    have hh := hsum 0 0
    simp only [zero_smul,add_zero] at hh
    rw [hh]
    change (∑ s, (volume (signCell K f p.1 p.2 s)).toReal) = _
    rw [← area_gap_eq_sum_signCells hK hne f hW p.1 p.2
      (fun i => ((interior_subset hp).1 i).2.1)]
    simpa only [V,q,mul_comm,gapArea] using heq
  have hdadd (x : H) : 1-budget K f (p+(x : Endpoints 2)) = q+d x := by
    have hh := affine_eval_line (deficit K f 1) p (x : Endpoints 2) 1
    simpa only [one_smul,deficit_apply,one_mul,q,d,ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap',Submodule.subtypeL_apply] using hh
  have hmin : IsLocalMin (fun x : H => (∑ s, (b s+M s x)^2)-V*(q+d x)^2) 0 := by
    have hopen : IsOpen {x : H | p+(x : Endpoints 2) ∈ interior (domain K f)} :=
      isOpen_interior.preimage (continuous_const.add H.subtypeL.continuous)
    apply Filter.Eventually.mono (hopen.mem_nhds
      (show (0 : H) ∈ {x : H | p+(x : Endpoints 2) ∈ interior (domain K f)} by
        simpa only [mem_ofPred_eq,Submodule.coe_zero,add_zero] using hp))
    intro x hx
    change (∑ s, (b s+M s 0)^2)-V*(q+d 0)^2 ≤
      (∑ s, (b s+M s x)^2)-V*(q+d x)^2
    simp only [map_zero,add_zero,hbase,sub_self]
    apply sub_nonneg.mpr
    have hlower := PlanarTwoPlank.sharpPlanarBound_two K hK hconv hne f
      (p+(x : Endpoints 2)).1 (p+(x : Endpoints 2)).2
      (fun i => ((interior_subset hx).1 i).2.1) hW
    change (max 0 (1-budget K f (p+(x : Endpoints 2))))^2*V ≤
      gapArea K f (p+(x : Endpoints 2)) at hlower
    rw [max_eq_right (sub_nonneg.mpr (interior_subset hx).2),hdadd] at hlower
    apply (show V*(q+d x)^2 ≤ gapArea K f (p+(x : Endpoints 2)) by
      simpa only [mul_comm] using hlower).trans
    rw [gapArea,area_gap_eq_sum_signCells hK hne f hW _ _
      (fun i => ((interior_subset hx).1 i).2.1)]
    have hh := hsum x 1
    simp only [one_smul] at hh
    change (∑ s, A s (p+(x : Endpoints 2))) ≤ _
    rw [← hh]
    exact Finset.sum_le_sum (fun s _ => by
      simpa only [add_sub_cancel_left,M,b,ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply] using hG s (p+(x : Endpoints 2)))
  have hdim : Fintype.card S ≤ Module.finrank ℝ H :=
    EqualitySupportingRank.card_active_le_finrank_ker S L
      (by simp only [Fintype.card_finset,Fintype.card_fin,endpoint_finrank]; norm_num)
  obtain ⟨x,hxne,c,hc,hd,hM⟩ := EqualitySupportingRank.exists_proportional_direction
    b M d V q hV (sub_pos.mpr hR) hbase hmin hdim
  refine ⟨(x : Endpoints 2),?_,c,hc,hd,?_⟩
  · intro hx
    exact hxne (Subtype.ext hx)
  · intro s t
    by_cases hs : s ∈ S
    · have hh := hG ⟨s,hs⟩ (p+t • (x : Endpoints 2))
      rw [add_sub_cancel_left,map_smul] at hh
      have hm : G ⟨s,hs⟩ (x : Endpoints 2) = Real.sqrt (A s p)*c := hM ⟨s,hs⟩
      rw [hm] at hh
      change A s (p+t • (x : Endpoints 2)) ≤ A s p*(1+t*c)^2
      calc
        A s (p+t • (x : Endpoints 2)) ≤ (Real.sqrt (A s p)+t*(Real.sqrt (A s p)*c))^2 := hh
        _ = (Real.sqrt (A s p))^2*(1+t*c)^2 := by ring
        _ = A s p*(1+t*c)^2 := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]
    · change A s (p+t • (x : Endpoints 2)) ≤ A s p*(1+t*c)^2
      rw [hzcell x s hs t,hzero s hs,zero_mul]

end Plank.PlanarChartFreeScaling

/-- info: 'Plank.PlanarChartFreeScaling.exists_common_upper_scaling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarChartFreeScaling.exists_common_upper_scaling
