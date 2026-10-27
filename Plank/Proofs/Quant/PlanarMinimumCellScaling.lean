/- Common scaling at an actual shifted-margin minimum, without the three-plank bound. -/
module

public import Plank.Proofs.Quant.PlanarEndpointMajorants
public import Plank.Proofs.Quant.EqualitySupportingRank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFewCellScaling

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPlankCellCharts PlanarPositiveCellRank QuadraticChartCalculus PlanarPolygonCharts
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

variable {m : ℕ}

/-- Only the listed exterior cells may be nonempty. -/
def region (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (C : Finset (Finset (Fin m))) : Set (Endpoints m) :=
  {p | ∀ s, s ∉ C → signCell K f p.1 p.2 s = ∅}

theorem isOpen_empty_cell {K : Set Point} (hK : IsCompact K)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (s : Finset (Fin m)) :
    IsOpen {p : Endpoints m | signCell K f p.1 p.2 s = ∅} := by
  classical
  have hcont : Continuous (fun p : Endpoints m => cutOffsets f p.1 p.2 s) := by
    apply continuous_pi
    intro i
    by_cases hs : i ∈ s <;> simp only [cutOffsets,hs,if_true,if_false] <;> fun_prop
  have hclosed : IsClosed {p : Endpoints m | (signCell K f p.1 p.2 s).Nonempty} := by
    simp_rw [signCell_eq_cell]
    exact (PlanarInactiveCellMotion.isClosed_feasible hK (cutForms f s)).preimage hcont
  convert hclosed.isOpen_compl using 1
  ext p
  exact not_nonempty_iff_eq_empty.symm

theorem isOpen_region {K : Set Point} (hK : IsCompact K)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (C : Finset (Finset (Fin m))) :
    IsOpen (region K f C) := by
  have he : region K f C = ⋂ s : {s // s ∉ C},
      {p : Endpoints m | signCell K f p.1 p.2 s = ∅} := by
    ext p
    simp only [region,mem_ofPred_eq,mem_iInter,Subtype.forall]
  rw [he]
  exact isOpen_iInter_of_finite fun s => isOpen_empty_cell hK f s

theorem area_zero_outside (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (C : Finset (Finset (Fin m))) (p : Endpoints m) (hp : p ∈ region K f C)
    (s : Finset (Fin m)) (hs : s ∉ C) :
    (volume (signCell K f p.1 p.2 s)).toReal = 0 := by
  rw [hp s hs,measure_empty,ENNReal.toReal_zero]

theorem sum_allowed (K : Set Point) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (C : Finset (Finset (Fin m))) (p : Endpoints m) (hp : p ∈ region K f C) :
    (∑ s : C, (volume (signCell K f p.1 p.2 s)).toReal) =
      ∑ s, (volume (signCell K f p.1 p.2 s)).toReal := by
  classical
  rw [Finset.sum_coe_sort C (fun s => (volume (signCell K f p.1 p.2 s)).toReal)]
  exact Finset.sum_subset (Finset.subset_univ _)
    (fun s _ hs => area_zero_outside K f C p hp s hs)

/-- At most `2*m` potentially nonempty closed cells supply a common scaling
direction at a zero local minimum of the actual shifted margin. The minimum
is explicit; no quantitative two- or three-plank theorem is imported or used.
Zero-area cells retain their constraints, including degenerate nonempty cells. -/
theorem exists_common_upper_scaling_at_minimum {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (C : Finset (Finset (Fin m))) (hC : C.card ≤ 2*m)
    (B : ℝ) (p : Endpoints m) (hp : p ∈ interior (domain K f))
    (horder : p ∈ region K f C) (hR : budget K f p < B)
    (heq : gapArea K f p = (B-budget K f p)^2*(volume K).toReal)
    (hminimum : IsLocalMin (PlanarShiftedDomain.margin K f B) p) :
    ∃ z : Endpoints m, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      (deficit K f B).linear z = (B-budget K f p)*c ∧
      ∀ s t, p+t • z ∈ region K f C → (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
        (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
  classical
  let A (s : Finset (Fin m)) (e : Endpoints m) :=
    (volume (signCell K f e.1 e.2 s)).toReal
  let S : Finset C := Finset.univ.filter (fun s => 0 < A s p)
  have hS (s) : s ∈ S ↔ 0 < A s p := by simp [S]
  have hzero (s) (hs : s ∉ S) : A s p = 0 :=
    le_antisymm (le_of_not_gt (fun hh => hs ((hS s).mpr hh))) ENNReal.toReal_nonneg
  have hmaj (s : S) : ∃ G : Endpoints m →L[ℝ] ℝ, ∀ e,
      A s e ≤ (Real.sqrt (A s p)+G (e-p))^2 :=
    PlanarEndpointMajorants.exists_majorant hK hconv hne f hW s p ((hS s).mp s.property)
  choose G hG using hmaj
  have hconstraints (s : {s // s ∉ S}) : ∃ L : Endpoints m →ₗ[ℝ] ℝ,
      ∀ z, L z = 0 → ∀ t : ℝ, A s (p+t • z) = 0 :=
    PlanarEndpointMajorants.exists_zero_constraint hK hconv hne hV f hW s p
      (hzero s s.property)
  choose L hL using hconstraints
  let Z := LinearMap.pi L
  let H := LinearMap.ker Z
  let M (s : S) : H →L[ℝ] ℝ := (G s).comp H.subtypeL
  let b (s : S) := Real.sqrt (A s p)
  let V := (volume K).toReal
  let q := B-budget K f p
  let d : H →L[ℝ] ℝ := (deficit K f B).linear.toContinuousLinearMap.comp H.subtypeL
  have hzcell (x : H) (s : C) (hs : s ∉ S) (t : ℝ) :
      A s (p+t • (x : Endpoints m)) = 0 := by
    have hh : Z (x : Endpoints m) = 0 := x.property
    exact hL ⟨s,hs⟩ x (congrFun hh ⟨s,hs⟩) t
  have hsum (x : H) (t : ℝ)
      (ho : p+t • (x : Endpoints m) ∈ region K f C) :
      (∑ s : S, A s (p+t • (x : Endpoints m))) =
        ∑ s, A s (p+t • (x : Endpoints m)) := by
    have hh : (∑ s : S, A s (p+t • (x : Endpoints m))) =
        ∑ s : C, A s (p+t • (x : Endpoints m)) := by
      rw [Finset.sum_coe_sort S (fun s => A s (p+t • (x : Endpoints m)))]
      exact Finset.sum_subset (Finset.subset_univ _) (fun s _ hs => hzcell x s hs t)
    rw [hh]
    exact sum_allowed K f C _ ho
  have hbase : (∑ s : S, (b s)^2) = V*q^2 := by
    have hsq (s : S) : (b s)^2 = A s p := Real.sq_sqrt ENNReal.toReal_nonneg
    simp only [hsq]
    have hh := hsum 0 0 (by simpa only [zero_smul,add_zero] using horder)
    simp only [zero_smul,add_zero] at hh
    rw [hh]
    change (∑ s, (volume (signCell K f p.1 p.2 s)).toReal) = _
    rw [← area_gap_eq_sum_signCells hK hne f hW p.1 p.2
      (fun i => ((interior_subset hp).1 i).2.1)]
    simpa only [V,q,mul_comm,gapArea] using heq
  have hdadd (x : H) : B-budget K f (p+(x : Endpoints m)) = q+d x := by
    have hh := affine_eval_line (deficit K f B) p (x : Endpoints m) 1
    simpa only [one_smul,deficit_apply,one_mul,q,d,ContinuousLinearMap.comp_apply,
      LinearMap.coe_toContinuousLinearMap',Submodule.subtypeL_apply] using hh
  have hmargin0 : PlanarShiftedDomain.margin K f B p = 0 := by
    dsimp only [PlanarShiftedDomain.margin]
    nlinarith only [heq]
  have hnear : ∀ᶠ x : H in 𝓝 0,
      0 ≤ PlanarShiftedDomain.margin K f B (p+(x : Endpoints m)) := by
    have ht : Filter.Tendsto (fun x : H => p+(x : Endpoints m)) (𝓝 0) (𝓝 p) := by
      have hcont : Continuous (fun x : H => p+(x : Endpoints m)) :=
        continuous_const.add H.subtypeL.continuous
      simpa only [Submodule.coe_zero,add_zero] using
        (hcont.continuousAt (x := (0 : H))).tendsto
    exact (ht.eventually hminimum).mono (fun x hx => by rwa [hmargin0] at hx)
  have hmin : IsLocalMin (fun x : H => (∑ s, (b s+M s x)^2)-V*(q+d x)^2) 0 := by
    have hopen : IsOpen {x : H | p+(x : Endpoints m) ∈ interior (domain K f) ∧
        p+(x : Endpoints m) ∈ region K f C} :=
      (isOpen_interior.preimage (continuous_const.add H.subtypeL.continuous)).inter
        ((isOpen_region hK f C).preimage (continuous_const.add H.subtypeL.continuous))
    have hnhds := hopen.mem_nhds
      (show (0 : H) ∈ {x : H | p+(x : Endpoints m) ∈ interior (domain K f) ∧
          p+(x : Endpoints m) ∈ region K f C} by
        simpa only [mem_ofPred_eq,Submodule.coe_zero,add_zero] using And.intro hp horder)
    filter_upwards [hnhds,hnear] with x hx hxminimum
    change (∑ s, (b s+M s 0)^2)-V*(q+d 0)^2 ≤
      (∑ s, (b s+M s x)^2)-V*(q+d x)^2
    simp only [map_zero,add_zero,hbase,sub_self]
    apply sub_nonneg.mpr
    have hlower := sub_nonneg.mp hxminimum
    change V*(B-budget K f (p+(x : Endpoints m)))^2 ≤ gapArea K f (p+(x : Endpoints m)) at hlower
    rw [hdadd] at hlower
    apply hlower.trans
    rw [gapArea,area_gap_eq_sum_signCells hK hne f hW _ _
      (fun i => ((interior_subset hx.1).1 i).2.1)]
    have hh := hsum x 1 (by simpa only [one_smul] using hx.2)
    simp only [one_smul] at hh
    change (∑ s, A s (p+(x : Endpoints m))) ≤ _
    rw [← hh]
    exact Finset.sum_le_sum (fun s _ => by
      simpa only [add_sub_cancel_left,M,b,ContinuousLinearMap.comp_apply,
        Submodule.subtypeL_apply] using hG s (p+(x : Endpoints m)))
  have hdim : Fintype.card S ≤ Module.finrank ℝ H :=
    EqualitySupportingRank.card_active_le_finrank_ker S L
      (by simpa only [Fintype.card_coe,endpoint_finrank] using hC)
  obtain ⟨x,hxne,c,hc,hd,hM⟩ := EqualitySupportingRank.exists_proportional_direction
    b M d V q hV (sub_pos.mpr hR) hbase hmin hdim
  refine ⟨(x : Endpoints m),?_,c,hc,hd,?_⟩
  · intro hx
    exact hxne (Subtype.ext hx)
  · intro s t ho
    by_cases ha : s ∈ C
    · let u : C := ⟨s,ha⟩
      by_cases hs : u ∈ S
      · have hh := hG ⟨u,hs⟩ (p+t • (x : Endpoints m))
        rw [add_sub_cancel_left,map_smul] at hh
        have hm : G ⟨u,hs⟩ (x : Endpoints m) = Real.sqrt (A s p)*c := hM ⟨u,hs⟩
        rw [hm] at hh
        change A s (p+t • (x : Endpoints m)) ≤ A s p*(1+t*c)^2
        calc
          A s (p+t • (x : Endpoints m)) ≤ (Real.sqrt (A s p)+t*(Real.sqrt (A s p)*c))^2 := hh
          _ = (Real.sqrt (A s p))^2*(1+t*c)^2 := by ring
          _ = A s p*(1+t*c)^2 := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]
      · change A u (p+t • (x : Endpoints m)) ≤ A u p*(1+t*c)^2
        rw [hzcell x u hs t,hzero u hs,zero_mul]
    · rw [area_zero_outside K f C _ ho s ha,area_zero_outside K f C p horder s ha,zero_mul]

end Plank.PlanarFewCellScaling

/-- info: 'Plank.PlanarFewCellScaling.exists_common_upper_scaling_at_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFewCellScaling.exists_common_upper_scaling_at_minimum
