/- Exact equality motion with at most six potentially nonempty cells. -/
module

public import Plank.Proofs.Quant.PlanarFewCellScaling
public import Plank.Proofs.Quant.PlanarNonemptyCellGeometry

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFewCellEqualityLine

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells PlanarPolygonCharts
open PlanarFewCellScaling
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

/-- Common cell upper scaling is exact on the ordered part of a
line where the affine deficit is nonnegative and unlisted cells stay
empty, including negative times. -/
theorem scaling_eq {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (C : Finset (Finset (Fin 3)))
    (p z : Endpoints 3) (c : ℝ)
    (hp : ∀ i, p.1 i ≤ p.2 i) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hupper : ∀ s t, p+t • z ∈ region K f C → (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (t : ℝ) (ht : 0 ≤ 1+t*c) (ho : ∀ i, (p+t • z).1 i ≤ (p+t • z).2 i)
    (horder : p+t • z ∈ region K f C) :
    gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal ∧
      ∀ s, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal =
        (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
  classical
  have hdef : 1-budget K f (p+t • z) = (1-budget K f p)*(1+t*c) := by
    have hh := affine_eval_line (deficit K f 1) p z t
    simp only [deficit_apply] at hh
    rw [hd] at hh
    nlinarith only [hh]
  have hsum : (∑ s, (volume (signCell K f p.1 p.2 s)).toReal) =
      (1-budget K f p)^2*(volume K).toReal := by
    rw [← area_gap_eq_sum_signCells hK hne f hW p.1 p.2 hp]
    exact heq
  have hu : gapArea K f (p+t • z) ≤ (1-budget K f (p+t • z))^2*(volume K).toReal := by
    rw [gapArea,area_gap_eq_sum_signCells hK hne f hW _ _ ho]
    calc
      (∑ s, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal) ≤
          ∑ s, (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 :=
        Finset.sum_le_sum (fun s _ => hupper s t horder)
      _ = (1-budget K f (p+t • z))^2*(volume K).toReal := by
        rw [← Finset.sum_mul,hsum,hdef]
        ring
  have he : gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal := by
    apply le_antisymm hu
    have hh := PlanarThreePlank.sharpPlanarBound_three K hK hconv hne f
      (p+t • z).1 (p+t • z).2 ho hW
    change (max 0 (1-budget K f (p+t • z)))^2*(volume K).toReal ≤ gapArea K f (p+t • z) at hh
    rwa [max_eq_right (by rw [hdef]; exact mul_nonneg (sub_pos.mpr hR).le ht)] at hh
  refine ⟨he,?_⟩
  have hse : (∑ s, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal) =
      ∑ s, (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
    rw [← area_gap_eq_sum_signCells hK hne f hW _ _ ho]
    change gapArea K f (p+t • z) = _
    rw [he,← Finset.sum_mul,hsum,hdef]
    ring
  have hh := (Finset.sum_eq_sum_iff_of_le (fun s (_ : s ∈ Finset.univ) => hupper s t horder)).mp hse
  exact fun s => hh s (Finset.mem_univ s)

/-- The line and all of its stated upper bounds are obtained from the
actual geometric equality, not supplied as unproved extra hypotheses. -/
theorem exists_line {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (C : Finset (Finset (Fin 3))) (hC : C.card ≤ 6)
    (p : Endpoints 3) (hp : p ∈ interior (domain K f))
    (horder : p ∈ region K f C) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ z : Endpoints 3, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      (deficit K f 1).linear z = (1-budget K f p)*c ∧
      (∀ s t, p+t • z ∈ region K f C → (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
        (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2) ∧
      ∀ t : ℝ, 0 ≤ 1+t*c → (∀ i, (p+t • z).1 i ≤ (p+t • z).2 i) →
        p+t • z ∈ region K f C →
        gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal ∧
        ∀ s, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal =
          (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
  obtain ⟨z,hzne,c,hc,hd,hu⟩ := PlanarFewCellScaling.exists_common_upper_scaling
    hK hconv hne hV f hW C hC p hp horder hR heq
  exact ⟨z,hzne,c,hc,hd,hu,scaling_eq hK hconv hne f hW C p z c
    (fun i => ((interior_subset hp).1 i).2.1) hR heq hd hu⟩

/-- Retain the exact individual cell scaling on a whole local interval. -/
theorem exists_local_scaling {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p : Endpoints 3) (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hcount : (PlanarSevenNonemptyCells.nonemptyCells K f p).card ≤ 6) :
    ∃ z : Endpoints 3, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      (deficit K f 1).linear z = (1-budget K f p)*c ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
        p+t • z ∈ interior (domain K f) ∧ 0 < 1+t*c ∧
        ∀ s, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal =
          (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
  let C := PlanarSevenNonemptyCells.nonemptyCells K f p
  have hreg : p ∈ region K f C := by
    intro s hs
    apply not_nonempty_iff_eq_empty.mp
    intro hn
    exact hs ((PlanarSevenNonemptyCells.mem_nonemptyCells K f p s).mpr hn)
  obtain ⟨z,hzne,c,hc,hd,_,hline⟩ := exists_line hK hconv hne hV f hW C hcount
    p hp hreg hR heq
  have hcont : Continuous (fun t : ℝ => p+t • z) := by fun_prop
  have hfactor : Continuous (fun t : ℝ => 1+t*c) := by fun_prop
  have hopen : IsOpen {t : ℝ | p+t • z ∈ interior (domain K f) ∩ region K f C ∧
      0 < 1+t*c} :=
    ((isOpen_interior.inter (isOpen_region hK f C)).preimage hcont).inter
      (isOpen_lt continuous_const hfactor)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (0 : ℝ) ∈ {t : ℝ | p+t • z ∈ interior (domain K f) ∩ region K f C ∧
        0 < 1+t*c} by
      simpa only [mem_ofPred_eq,mem_inter_iff,zero_smul,add_zero,zero_mul] using
        And.intro (And.intro hp hreg) (show (0 : ℝ) < 1 from zero_lt_one)))
  refine ⟨z,hzne,c,hc,hd,ε,hε,?_⟩
  intro t ht
  have hm := hball (show t ∈ Metric.ball 0 ε by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using ht)
  exact ⟨hm.1.1,hm.2,(hline t hm.2.le
    (fun i => ((interior_subset hm.1.1).1 i).2.1) hm.1.2).2⟩

/-- The actual nonempty-cell list supplies the open region and the rank
bound. Thus the motion exists locally without any chart hypothesis. -/
theorem exists_local_motion {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p : Endpoints 3) (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hcount : (PlanarSevenNonemptyCells.nonemptyCells K f p).card ≤ 6) :
    ∃ z : Endpoints 3, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
      p+t • z ∈ interior (domain K f) ∧
      gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal ∧
      (0 ≤ t → budget K f (p+t • z) ≤ budget K f p) := by
  obtain ⟨z,hzne,c,hc,hd,ε,hε,hscale⟩ :=
    exists_local_scaling hK hconv hne hV f hW p hp hR heq hcount
  refine ⟨z,hzne,ε,hε,?_⟩
  intro t ht
  obtain ⟨hi,_,hs⟩ := hscale t ht
  have hh := affine_eval_line (deficit K f 1) p z t
  simp only [deficit_apply] at hh
  rw [hd] at hh
  refine ⟨hi,?_,?_⟩
  · rw [gapArea,area_gap_eq_sum_signCells hK hne f hW _ _
      (fun i => ((interior_subset hi).1 i).2.1)]
    simp_rw [hs]
    rw [← Finset.sum_mul,← area_gap_eq_sum_signCells hK hne f hW p.1 p.2
      (fun i => ((interior_subset hp).1 i).2.1)]
    change gapArea K f p*(1+t*c)^2 = _
    rw [heq]
    have hdef : 1-budget K f (p+t • z) = (1-budget K f p)*(1+t*c) := by
      nlinarith only [hh]
    rw [hdef]
    ring
  · intro ht0
    have hn := mul_nonneg ht0 (mul_nonneg (sub_pos.mpr hR).le hc)
    linarith only [hh,hn]

end Plank.PlanarFewCellEqualityLine

/-- info: 'Plank.PlanarFewCellEqualityLine.exists_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFewCellEqualityLine.exists_line

/-- info: 'Plank.PlanarFewCellEqualityLine.exists_local_motion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarFewCellEqualityLine.exists_local_motion
