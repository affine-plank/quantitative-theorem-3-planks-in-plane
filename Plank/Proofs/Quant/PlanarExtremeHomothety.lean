/- Extreme-point rigidity for a local convex-body homothety. -/
module

public import Plank.Proofs.Quant.PlanarStatement
public import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarExtremeHomothety

open Set PlanarQuantitative
open scoped Topology

/-- An extreme point cannot contract into a region where the contracted
body already contains a neighbourhood of the original body, unless it is
the contraction center. No smoothness or polygon hypothesis is used. -/
theorem extreme_fixed_of_local_homothety {K O : Set Point} (hK : Convex ℝ K)
    (hO : IsOpen O) (x y : Point) (hx : x ∈ K.extremePoints ℝ) (hy : y ∈ K)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hz : AffineMap.homothety y r x ∈ O)
    (hlocal : K ∩ O ⊆ AffineMap.homothety y r '' K) : x = y := by
  let z := AffineMap.homothety y r x
  have hzK : z ∈ K := by
    change r • (x-y)+y ∈ K
    simpa only [add_comm] using hK.add_smul_sub_mem hy hx.1 ⟨hr.le,hr1.le⟩
  have hopen : IsOpen {t : ℝ | z+t • (x-z) ∈ O} := hO.preimage (by fun_prop)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (0 : ℝ) ∈ {t : ℝ | z+t • (x-z) ∈ O} by
      simpa only [mem_ofPred_eq,zero_smul,add_zero] using hz))
  let t := min (ε/2) (1/2 : ℝ)
  have ht : 0 < t := lt_min (by linarith only [hε]) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have htε : t < ε := (min_le_left _ _).trans_lt (by linarith only [hε])
  have hwO : z+t • (x-z) ∈ O := hball (by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos ht] using htε)
  have hwK : z+t • (x-z) ∈ K := hK.add_smul_sub_mem hzK hx.1 ⟨ht.le,ht1⟩
  obtain ⟨v,hv,hv_eq⟩ := hlocal ⟨hwK,hwO⟩
  let k := r+t*(1-r)
  have hkr : 0 < k-r := by
    have hp := mul_pos ht (sub_pos.mpr hr1)
    dsimp [k]
    linarith only [hp]
  have hk : 0 < k := by linarith only [hkr,hr]
  have hseg : x ∈ openSegment ℝ y v := by
    refine ⟨(k-r)/k,r/k,div_pos hkr hk,div_pos hr hk,?_,?_⟩
    · field_simp
      ring
    · ext i
      have hh := congrFun hv_eq i
      change r*(v i-y i)+y i = z i+t*(x i-z i) at hh
      have hz_i : z i = r*(x i-y i)+y i := rfl
      rw [hz_i] at hh
      change ((k-r)/k)*y i+(r/k)*v i = x i
      field_simp
      dsimp [k]
      nlinarith only [hh]
  exact (hx.2 hy hv hseg).symm

end Plank.PlanarExtremeHomothety

/-- info: 'Plank.PlanarExtremeHomothety.extreme_fixed_of_local_homothety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarExtremeHomothety.extreme_fixed_of_local_homothety
