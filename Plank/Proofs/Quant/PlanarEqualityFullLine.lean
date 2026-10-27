/- Continue common cell scaling backward as far as the deficit stays nonnegative. -/
module

public import Plank.Proofs.Quant.PlanarChartFreeScaling

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarEqualityFullLine

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells PlanarPolygonCharts
open PlanarShiftedDomain (deficit deficit_apply)
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

/-- Common cell upper scaling is exact on the entire ordered part of a
line where the affine deficit is nonnegative, including negative times. -/
theorem scaling_eq {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (p z : Endpoints 2) (c : ℝ)
    (hp : ∀ i, p.1 i ≤ p.2 i) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal)
    (hd : (deficit K f 1).linear z = (1-budget K f p)*c)
    (hupper : ∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
      (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2)
    (t : ℝ) (ht : 0 ≤ 1+t*c) (ho : ∀ i, (p+t • z).1 i ≤ (p+t • z).2 i) :
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
        Finset.sum_le_sum (fun s _ => hupper s t)
      _ = (1-budget K f (p+t • z))^2*(volume K).toReal := by
        rw [← Finset.sum_mul,hsum,hdef]
        ring
  have he : gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal := by
    apply le_antisymm hu
    have hh := PlanarTwoPlank.sharpPlanarBound_two K hK hconv hne f
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
  have hh := (Finset.sum_eq_sum_iff_of_le (fun s (_ : s ∈ Finset.univ) => hupper s t)).mp hse
  exact fun s => hh s (Finset.mem_univ s)

/-- The line and all of its global upper bounds are obtained from the
actual geometric equality, not supplied as unproved extra hypotheses. -/
theorem exists_line {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < rangeWidth K (f i))
    (p : Endpoints 2) (hp : p ∈ interior (domain K f)) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ z : Endpoints 2, z ≠ 0 ∧ ∃ c : ℝ, 0 ≤ c ∧
      (deficit K f 1).linear z = (1-budget K f p)*c ∧
      (∀ s t, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal ≤
        (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2) ∧
      ∀ t : ℝ, 0 ≤ 1+t*c → (∀ i, (p+t • z).1 i ≤ (p+t • z).2 i) →
        gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal ∧
        ∀ s, (volume (signCell K f (p+t • z).1 (p+t • z).2 s)).toReal =
          (volume (signCell K f p.1 p.2 s)).toReal*(1+t*c)^2 := by
  obtain ⟨z,hzne,c,hc,hd,hu⟩ := PlanarChartFreeScaling.exists_common_upper_scaling
    hK hconv hne hV f hW p hp hR heq
  exact ⟨z,hzne,c,hc,hd,hu,scaling_eq hK hconv hne f hW p z c
    (fun i => ((interior_subset hp).1 i).2.1) hR heq hd hu⟩

end Plank.PlanarEqualityFullLine

/-- info: 'Plank.PlanarEqualityFullLine.exists_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarEqualityFullLine.exists_line
