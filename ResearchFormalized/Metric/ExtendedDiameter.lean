/- Standard extended-diameter continuity for increasing unions. -/
module

public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section
set_option autoImplicit false

open Set Metric Filter
open scoped Topology ENNReal

namespace ResearchFormalized.ExtendedDiameter

variable {X : Type*} [PseudoEMetricSpace X]

theorem ediam_iUnion_of_monotone (s : ℕ → Set X) (hs : Monotone s) :
    ediam (⋃ n, s n) = ⨆ n, ediam (s n) := by
  refine le_antisymm (ediam_le ?_) (iSup_le fun n => ediam_mono (subset_iUnion s n))
  intro x hx y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hy
  exact (edist_le_ediam_of_mem (hs (le_max_left i j) hi) (hs (le_max_right i j) hj)).trans
    (le_iSup (fun n => ediam (s n)) (max i j))

theorem tendsto_ediam_iUnion (s : ℕ → Set X) (hs : Monotone s) :
    Tendsto (fun n => ediam (s n)) atTop (𝓝 (ediam (⋃ n, s n))) := by
  rw [ediam_iUnion_of_monotone s hs]
  exact tendsto_atTop_iSup fun i j hij => ediam_mono (hs hij)

end ResearchFormalized.ExtendedDiameter
