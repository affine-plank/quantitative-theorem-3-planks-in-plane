/- Affine constraints keep inactive uncovered cells empty along a motion. -/
module

public import Plank.Proofs.Quant.PlanarPositiveCellRank
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Group.Pointwise

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarInactiveCellMotion

open Set MeasureTheory PlanarQuantitative PlanarCellArea PlanarGapCells
  PlanarPolygonCharts PlanarPlankCellCharts
open Plank.Convex.DeficientHeightTilt
open scoped Pointwise

variable {κ : Type*} [Fintype κ]

omit [Fintype κ] in
/-- Compactness of the body makes the feasible offset set closed, although
the offsets themselves are unbounded. -/
theorem isClosed_feasible {K : Set Point} (hK : IsCompact K)
    (f : κ → Point →L[ℝ] ℝ) : IsClosed {u | (cell K f u).Nonempty} :=
  FiniteDimensionalCellSupportingAffine.isClosed_feasible hK f

/-- Any nonempty cell acquires positive area when every offset is increased
strictly. This includes an initially degenerate cell on the body boundary. -/
theorem relaxed_area_pos {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : κ → Point →L[ℝ] ℝ) (u : κ → ℝ)
    (hne : (cell K f u).Nonempty) (ε : ℝ) (hε : 0 < ε) :
    0 < (volume (cell K f (u+ε • (1 : κ → ℝ)))).toReal :=
  FiniteDimensionalCellSupportingAffine.relaxed_volume_pos hK hconv hV f u hne ε hε

/-- An actual cell polynomial that vanishes on an open endpoint region
represents an empty cell at every point of that region, not just a null cell. -/
theorem empty_of_zero_on_open {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ)
    {U : Set (EndpointSpace κ)} (hU : IsOpen U) (p : EndpointSpace κ) (hp : p ∈ U)
    (hzero : ∀ e ∈ U, (volume (signCell K f e.1 e.2 s)).toReal = 0) :
    signCell K f p.1 p.2 s = ∅ := by
  classical
  apply not_nonempty_iff_eq_empty.mp
  intro hne
  let z : EndpointSpace κ := (1,-1)
  have hopen : IsOpen {t : ℝ | p+t • z ∈ U} := hU.preimage (by fun_prop)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds
    (show (0 : ℝ) ∈ {t | p+t • z ∈ U} by simpa using hp))
  let ε := δ/2
  have hε : 0 < ε := by dsimp [ε]; linarith only [hδ]
  have he : p+ε • z ∈ U := hball (by
    rw [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hε]
    dsimp [ε]; linarith only [hδ])
  have hz : cutDirection z.1 z.2 s = (1 : κ → ℝ) := by
    ext i
    by_cases hs : i ∈ s <;> simp [cutDirection,z,hs]
  have hcell : signCell K f (p+ε • z).1 (p+ε • z).2 s =
      cell K (cutForms f s) (cutOffsets f p.1 p.2 s+ε • (1 : κ → ℝ)) := by
    rw [signCell_eq_cell]
    change cell K (cutForms f s) (cutOffsets f (p.1+ε • z.1) (p.2+ε • z.2) s) = _
    rw [cutOffsets_motion,hz]
  have hpositive := relaxed_area_pos hK hconv hV (cutForms f s) (cutOffsets f p.1 p.2 s)
    (by rwa [← signCell_eq_cell]) ε hε
  rw [← hcell,hzero _ he] at hpositive
  exact lt_irrefl 0 hpositive

/-- The change of cell offsets is linear in the physical endpoint motion. -/
def cutLinear (s : Finset κ) : EndpointSpace κ →ₗ[ℝ] (κ → ℝ) where
  toFun z := cutDirection z.1 z.2 s
  map_add' x y := by
    classical
    ext i
    by_cases hs : i ∈ s <;> simp [cutDirection,hs,add_comm]
  map_smul' a x := by
    classical
    ext i
    by_cases hs : i ∈ s <;> simp [cutDirection,hs]

/-- One linear equation on the motion is enough to preserve an empty cell
for the entire line, even after changing its local area chart. -/
theorem exists_empty_preserving_constraint {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ)
    (p : EndpointSpace κ) (hempty : signCell K f p.1 p.2 s = ∅) :
    ∃ L : EndpointSpace κ →ₗ[ℝ] ℝ, ∀ z, L z = 0 → ∀ t : ℝ,
      signCell K f (p+t • z).1 (p+t • z).2 s = ∅ := by
  let u := cutOffsets f p.1 p.2 s
  let T := {v | (cell K (cutForms f s) v).Nonempty}
  have hu : u ∉ T := by
    change ¬ (cell K (cutForms f s) u).Nonempty
    rw [← signCell_eq_cell,hempty]
    exact Set.not_nonempty_empty
  obtain ⟨g,a,hbelow,habove⟩ := geometric_hahn_banach_closed_point
    (convex_feasible hconv (cutForms f s)) (isClosed_feasible hK (cutForms f s)) hu
  refine ⟨g.toLinearMap.comp (cutLinear s),?_⟩
  intro z hz t
  apply not_nonempty_iff_eq_empty.mp
  intro hne
  have hcell : signCell K f (p+t • z).1 (p+t • z).2 s =
      cell K (cutForms f s) (u+t • cutDirection z.1 z.2 s) := by
    rw [signCell_eq_cell]
    exact congrArg (cell K (cutForms f s)) (cutOffsets_motion f p.1 p.2 z.1 z.2 s t)
  have hbad := hbelow (u+t • cutDirection z.1 z.2 s) (by
    change (cell K (cutForms f s) (u+t • cutDirection z.1 z.2 s)).Nonempty
    rwa [← hcell])
  have hg : g (cutDirection z.1 z.2 s) = 0 := hz
  rw [map_add,map_smul,hg,smul_zero,add_zero] at hbad
  exact (habove.trans hbad).false

end Plank.PlanarInactiveCellMotion

/-- info: 'Plank.PlanarInactiveCellMotion.exists_empty_preserving_constraint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarInactiveCellMotion.exists_empty_preserving_constraint
