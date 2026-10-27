/- Curvature of a quadratic chart for actual convex-cell area.
The chart identity is an explicit geometric input. Brunn--Minkowski,
square-root concavity and the directional curvature estimate are proved. -/
module

public import Plank.Proofs.Quant.PlanarGapCells
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellCurvature

open Set MeasureTheory PlanarQuantitative PlanarCellArea
open scoped Topology

/-- A concave square root of a quadratic obeys the planar curvature bound.
Only a right-hand interval is needed. The quadratic is positive at zero;
its value at the other endpoint may be zero. -/
theorem curvature_of_concave_sqrt_quadratic (A g H t : ℝ)
    (hA : 0 < A) (ht : 0 < t) (hvalue : 0 ≤ A + g*t + H/2*t^2)
    (hconcave : ConcaveOn ℝ (Icc 0 t)
      (fun s => Real.sqrt (A + g*s + H/2*s^2))) :
    H ≤ g^2/(2*A) := by
  let d := g/(2*Real.sqrt A)
  have hq : HasDerivAt (fun s : ℝ => A + g*s + H/2*s^2) g 0 := by
    convert! (((hasDerivAt_id (0 : ℝ)).const_mul g).const_add A).fun_add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (H/2)) using 1
    norm_num
  have hd : HasDerivAt (fun s : ℝ => Real.sqrt (A + g*s + H/2*s^2)) d 0 := by
    simpa [d] using hq.sqrt (by simpa using ne_of_gt hA)
  have hslope := hconcave.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 t from ⟨le_rfl, ht.le⟩)
    (show t ∈ Icc 0 t from ⟨ht.le, le_rfl⟩) ht hd
  have hslope' : (Real.sqrt (A + g*t + H/2*t^2) - Real.sqrt A)/t ≤ d := by
    simpa [slope, div_eq_mul_inv, mul_comm] using hslope
  have hupper : Real.sqrt (A + g*t + H/2*t^2) ≤ Real.sqrt A + d*t := by
    have h := (div_le_iff₀ ht).mp hslope'
    linarith only [h]
  have hright : 0 ≤ Real.sqrt A + d*t := (Real.sqrt_nonneg _).trans hupper
  have hsquares := mul_nonneg (sub_nonneg.mpr hupper)
    (add_nonneg hright (Real.sqrt_nonneg (A + g*t + H/2*t^2)))
  have hspos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hgd : 2*Real.sqrt A*d = g := by
    dsimp [d]
    field_simp
  have hgdt := congrArg (fun x : ℝ => x*t) hgd
  have hscaled : H*t^2 ≤ (2*d^2)*t^2 := by
    nlinarith only [hsquares, Real.sq_sqrt hvalue, Real.sq_sqrt hA.le, hgdt]
  have hcurv : H ≤ 2*d^2 :=
    (mul_le_mul_iff_of_pos_right (sq_pos_of_pos ht)).mp hscaled
  calc
    H ≤ 2*d^2 := hcurv
    _ = g^2/(2*(Real.sqrt A)^2) := by
      dsimp [d]
      field_simp
    _ = g^2/(2*A) := by rw [Real.sq_sqrt hA.le]

/-- If the actual cell area agrees with a quadratic along a nontrivial
parameter interval, its curvature at a positive-area initial point satisfies
the Brunn--Minkowski bound. No concavity, derivative, or nonemptiness premise
is supplied: these follow from the actual convex cells and the chart identity.
Existence of such a quadratic chart is the remaining geometric obligation. -/
theorem curvature_of_quadratic_area {ι : Type*} {K : Set Point}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : ι → Point →L[ℝ] ℝ)
    (u z : ι → ℝ) (A g H t : ℝ) (hA : 0 < A) (ht : 0 < t)
    (hchart : ∀ s ∈ Icc 0 t,
      (volume (cell K f (u + s • z))).toReal = A + g*s + H/2*s^2) :
    H ≤ g^2/(2*A) := by
  let q : ℝ → ℝ := fun s => A + g*s + H/2*s^2
  have hopen : IsOpen {s : ℝ | 0 < q s} :=
    isOpen_lt continuous_const (by dsimp [q]; fun_prop)
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp
    (hopen.mem_nhds (show (0 : ℝ) ∈ {s | 0 < q s} by simpa [q] using hA))
  let tau := min (t/2) (epsilon/2)
  have htau : 0 < tau := lt_min (by linarith) (by linarith)
  have htaut : tau ≤ t := (min_le_left _ _).trans (by linarith)
  have hsub : Icc (0 : ℝ) tau ⊆ Icc 0 t :=
    fun _ hs => ⟨hs.1, hs.2.trans htaut⟩
  have hpos : ∀ s ∈ Icc (0 : ℝ) tau, 0 < q s := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt (hs.2.trans (min_le_right _ _)) (by linarith)
  have hfeasible : ∀ s ∈ Icc (0 : ℝ) tau, (cell K f (u + s • z)).Nonempty := by
    intro s hs
    have harea : 0 < (volume (cell K f (u + s • z))).toReal := by
      rw [hchart s (hsub hs)]
      exact hpos s hs
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    simp [hn] at harea
  apply curvature_of_concave_sqrt_quadratic A g H tau hA htau
  · rw [← hchart tau (hsub ⟨htau.le, le_rfl⟩)]
    exact ENNReal.toReal_nonneg
  · refine ⟨convex_Icc 0 tau, ?_⟩
    intro s hs r hr a b ha hb hab
    have hcomb := (convex_Icc (0 : ℝ) tau) hs hr ha hb hab
    have h := (concaveOn_sqrt_area_cell hK hconv f).2
      (hfeasible s hs) (hfeasible r hr) ha hb hab
    have he : a • (u + s • z) + b • (u + r • z) =
        u + (a • s + b • r) • z := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hsum := congrArg (fun x : ℝ => x*u i) hab
      nlinarith only [hsum]
    rw [he] at h
    dsimp only at h
    rw [hchart s (hsub hs), hchart r (hsub hr),
      hchart (a • s + b • r) (hsub hcomb)] at h
    exact h

end Plank.PlanarCellCurvature

namespace Plank.PlanarGapCells

open Set MeasureTheory PlanarQuantitative

variable {ι : Type*}

/-- The curvature estimate for an actual affine-plank exterior cell along
endpoint motion. Its only local geometric input is the quadratic area identity;
Brunn--Minkowski, the affine-cell adapter and differentiation are discharged. -/
theorem curvature_of_quadratic_signCell_area {K : Set Point}
    (hK : IsCompact K) (hconv : Convex ℝ K) (f : ι → Point →ᵃ[ℝ] ℝ)
    (lo hi dlo dhi : ι → ℝ) (s : Finset ι) (A g H t : ℝ)
    (hA : 0 < A) (ht : 0 < t)
    (hchart : ∀ r ∈ Icc 0 t,
      (volume (signCell K f (lo + r • dlo) (hi + r • dhi) s)).toReal =
        A + g*r + H/2*r^2) :
    H ≤ g^2/(2*A) := by
  apply PlanarCellCurvature.curvature_of_quadratic_area hK hconv (cutForms f s)
    (cutOffsets f lo hi s) (cutDirection dlo dhi s) A g H t hA ht
  intro r hr
  rw [← cutOffsets_motion, ← signCell_eq_cell]
  exact hchart r hr


end Plank.PlanarGapCells
