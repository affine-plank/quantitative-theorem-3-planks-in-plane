/- Too few closed exterior cells leave a constant motion at any local minimum. -/
module
public import Plank.Proofs.Quant.PlanarMinimumCellRank
public import Plank.Convex.ExtremeMinimumRank

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarLocalMinimumMotion

open Set MeasureTheory Filter PlanarQuantitative PlanarParameterDomain PlanarGapCells
  PlanarPolygonCharts PlanarPositiveCellRank
open Plank.Convex.DeficientHeightTilt
open PlanarShiftedDomain (deficit deficit_apply)
open PlanarMinimumCellRank (nonemptyCells)
open scoped BigOperators Topology

/-- An affine correction does not obstruct the constant motion forced by too
few nonempty closed cells at a local minimum. The open endpoint neighborhood
need only have ordered windows. Both affine terms and the actual gap remain
constant; neither positive gap nor a plank bound is required. -/
theorem exists_motion_affine {m : ℕ} {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (a b : Endpoints m →ᵃ[ℝ] ℝ) (U : Set (Endpoints m)) (hU : IsOpen U)
    (horder : ∀ e ∈ U, ∀ i, e.1 i ≤ e.2 i) (p : Endpoints m) (hp : p ∈ U)
    (hminimum : IsLocalMin (fun e => gapArea K f e + a e - (volume K).toReal * (b e)^2) p)
    (hcount : (nonemptyCells K f p).card < 2*m) :
    ∃ z : Endpoints m, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      p+t • z ∈ U ∧ a (p+t • z) = a p ∧ b (p+t • z) = b p ∧
      gapArea K f (p+t • z) = gapArea K f p := by
  classical
  let A (s : Finset (Fin m)) (e : Endpoints m) :=
    (volume (signCell K f e.1 e.2 s)).toReal
  let S := nonemptyCells K f p
  have hS (s) : s ∈ S ↔ (signCell K f p.1 p.2 s).Nonempty := by
    simp [S,nonemptyCells]
  have hL (s : S) : ∃ L : Endpoints m →ₗ[ℝ] ℝ, ∀ z, L z = 0 → ∀ t : ℝ,
      A s (p+t • z) ≤ A s p := by
    by_cases hs : 0 < A s p
    · obtain ⟨G,hG⟩ := PlanarEndpointMajorants.exists_majorant hK hc hne f hW s p hs
      refine ⟨G.toLinearMap,?_⟩
      intro z hz t
      change G z = 0 at hz
      have hh := hG (p+t • z)
      rw [add_sub_cancel_left,map_smul,hz,smul_zero,add_zero,
        Real.sq_sqrt ENNReal.toReal_nonneg] at hh
      exact hh
    · have hz : A s p = 0 := le_antisymm (le_of_not_gt hs) ENNReal.toReal_nonneg
      obtain ⟨L,hL⟩ := PlanarEndpointMajorants.exists_zero_constraint hK hc hne hV f hW s p hz
      refine ⟨L,?_⟩
      intro z hh t
      change (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤ _
      rw [hL z hh t]
      exact ENNReal.toReal_nonneg
  choose L hL using hL
  obtain ⟨z,hzne,hz⟩ := Plank.Convex.ExtremeMinimumRank.common_kernel_nonzero
    (fun s => (L s).toContinuousLinearMap)
    (by simpa only [Fintype.card_coe,endpoint_finrank] using hcount)
  have ht : Tendsto (fun t : ℝ => p+t • z) (𝓝 0) (𝓝 p) := by
    have hcont : Continuous (fun t : ℝ => p+t • z) := by fun_prop
    simpa only [zero_smul,add_zero] using (hcont.continuousAt (x := 0)).tendsto
  have hupper : ∀ᶠ t : ℝ in 𝓝 0, ∀ s, A s (p+t • z) ≤ A s p := by
    apply Filter.eventually_all.mpr
    intro s
    by_cases hs : s ∈ S
    · exact Filter.Eventually.of_forall (fun t => hL ⟨s,hs⟩ z (hz ⟨s,hs⟩) t)
    · have he : signCell K f p.1 p.2 s = ∅ :=
        not_nonempty_iff_eq_empty.mp (fun hh => hs ((hS s).mpr hh))
      filter_upwards [ht.eventually ((PlanarFewCellScaling.isOpen_empty_cell hK f s).mem_nhds he)]
        with t hzero
      change (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤ _
      rw [hzero,measure_empty,ENNReal.toReal_zero]
      exact ENNReal.toReal_nonneg
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      p+t • z ∈ U ∧ gapArea K f (p+t • z) ≤ gapArea K f p ∧
      gapArea K f p + a p - (volume K).toReal * (b p)^2 ≤
        gapArea K f (p+t • z) + a (p+t • z) - (volume K).toReal * (b (p+t • z))^2 := by
    filter_upwards [ht.eventually (hU.mem_nhds hp), hupper,
      ht.eventually hminimum] with t hD hA hmin
    refine ⟨hD,?_,hmin⟩
    simp only [gapArea]
    rw [area_gap_eq_sum_signCells hK hne f hW _ _
      (horder _ hD),
      area_gap_eq_sum_signCells hK hne f hW _ _ (horder _ hp)]
    exact Finset.sum_le_sum (fun s _ => hA s)
  have hsq : ∀ᶠ t : ℝ in 𝓝 0,
      (volume K).toReal * ((b p+t*b.linear z)^2-(b p)^2) ≤ t*a.linear z := by
    filter_upwards [hnear] with t hh
    have hm := hh.2.2
    rw [affine_eval_line a p z t, affine_eval_line b p z t] at hm
    nlinarith only [hm,hh.2.1]
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
  obtain ⟨t,ht0,hplus,hminus⟩ := (hsq.and (hneg.eventually hsq)).exists_gt
  have hd : b.linear z = 0 := by
    have hz : (volume K).toReal * (t*b.linear z)^2 ≤ 0 := by
      nlinarith only [hplus,hminus]
    have hzero : (t*b.linear z)^2 = 0 := le_antisymm
      ((_root_.mul_le_mul_iff_of_pos_left hV).mp
        (hz.trans_eq (mul_zero _).symm)) (sq_nonneg _)
    exact (mul_eq_zero.mp (sq_eq_zero_iff.mp hzero)).resolve_left ht0.ne'
  have ha : a.linear z = 0 := by
    rw [hd] at hplus hminus
    nlinarith only [hplus,hminus,ht0]
  have hmotion : ∀ᶠ t : ℝ in 𝓝 0,
      p+t • z ∈ U ∧ a (p+t • z) = a p ∧ b (p+t • z) = b p ∧
      gapArea K f (p+t • z) = gapArea K f p := by
    filter_upwards [hnear] with t hh
    have hae : a (p+t • z) = a p := by simp only [affine_eval_line,ha,mul_zero,add_zero]
    have hbe : b (p+t • z) = b p := by simp only [affine_eval_line,hd,mul_zero,add_zero]
    refine ⟨hh.1,hae,hbe,le_antisymm hh.2.1 ?_⟩
    have hm := hh.2.2
    rw [hae,hbe] at hm
    linarith only [hm]
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hmotion
  exact ⟨z,hzne,ε,hε,fun t ht => hball
    (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using ht)⟩

/-- At an actual local minimum of the shifted margin, fewer than `2*m`
nonempty closed cells leave a nonzero motion preserving both actual budget
and actual uncovered area. The margin need not be zero and the gap need not
be positive. No quantitative or qualitative plank bound is a premise. -/
theorem exists_motion {m : ℕ} {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (B : ℝ) (p : Endpoints m) (hp : p ∈ interior (domain K f))
    (hminimum : IsLocalMin (PlanarShiftedDomain.margin K f B) p)
    (hcount : (nonemptyCells K f p).card < 2*m) :
    ∃ z : Endpoints m, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      p+t • z ∈ interior (domain K f) ∧ budget K f (p+t • z) = budget K f p ∧
      gapArea K f (p+t • z) = gapArea K f p := by
  have hmin : IsLocalMin (fun e => gapArea K f e + (0 : Endpoints m →ᵃ[ℝ] ℝ) e -
      (volume K).toReal * ((deficit K f B) e)^2) p := by
    have heq : (fun e => gapArea K f e + (0 : Endpoints m →ᵃ[ℝ] ℝ) e -
        (volume K).toReal * ((deficit K f B) e)^2) = PlanarShiftedDomain.margin K f B := by
      funext e
      simp only [AffineMap.coe_zero,Pi.zero_apply,add_zero,deficit_apply,
        PlanarShiftedDomain.margin]
    rw [heq]
    exact hminimum
  obtain ⟨z,hzne,ε,hε,hm⟩ := exists_motion_affine hK hc hne hV f hW 0
    (deficit K f B) (interior (domain K f)) isOpen_interior
    (fun e he i => ((interior_subset he).1 i).2.1) p hp hmin hcount
  refine ⟨z,hzne,ε,hε,?_⟩
  intro t ht
  obtain ⟨hi,_,hb,hg⟩ := hm t ht
  refine ⟨hi,?_,hg⟩
  simp only [deficit_apply] at hb
  linarith only [hb]

/-- Equality in any supplied planar quantitative bound is a local minimum.
This specializes the actual-minimum motion without repeating its geometry. -/
theorem exists_motion_of_bound {m : ℕ} (hm : SharpPlanarBound m)
    {K : Set Point} (hK : IsCompact K) (hc : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (f : Fin m → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (p : Endpoints m)
    (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (he : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hcount : (nonemptyCells K f p).card < 2*m) :
    ∃ z : Endpoints m, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      p+t • z ∈ interior (domain K f) ∧ budget K f (p+t • z) = budget K f p ∧
      gapArea K f (p+t • z) = (1-budget K f p)^2*(volume K).toReal := by
  have hminimum : IsLocalMin (PlanarShiftedDomain.margin K f 1) p := by
    filter_upwards [isOpen_interior.mem_nhds hp,
      (continuous_budget K f).continuousAt.eventually_lt_const hR] with q hq hqR
    have hbound := hm K hK hc hne f q.1 q.2
      (fun i => ((interior_subset hq).1 i).2.1) hW
    change (max 0 (1-budget K f q))^2*(volume K).toReal ≤ gapArea K f q at hbound
    rw [max_eq_right (sub_pos.mpr hqR).le] at hbound
    dsimp only [PlanarShiftedDomain.margin]
    nlinarith only [he,hbound]
  obtain ⟨z,hzne,ε,hε,hmotion⟩ := exists_motion hK hc hne hV f hW 1 p hp hminimum hcount
  refine ⟨z,hzne,ε,hε,?_⟩
  intro t ht
  obtain ⟨hi,hb,hg⟩ := hmotion t ht
  exact ⟨hi,hb,hg.trans he⟩

end Plank.PlanarLocalMinimumMotion

/-- info: 'Plank.PlanarLocalMinimumMotion.exists_motion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarLocalMinimumMotion.exists_motion

/-- info: 'Plank.PlanarLocalMinimumMotion.exists_motion_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarLocalMinimumMotion.exists_motion_of_bound
