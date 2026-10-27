/- Positive-definite chart selection connected to actual polygonal gap cells. -/
module

public import Plank.Proofs.Quant.QuadraticChartSelection

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPositiveChart

open Set MeasureTheory PlanarQuantitative PlanarPolygonCharts PlanarPlankCellCharts
open PlanarParameterDerivatives PlanarChartRegularity QuadraticChartCalculus QuadraticChartSelection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual value identities on a finite closed chart cover prove
continuity on an arbitrary restricted parameter domain. -/
theorem continuousOn_of_closed_atlas {σ : Type*} [Finite σ]
    (G : E → ℝ) (D : Set E) (C : σ → Set E)
    (hcover : (⋃ i, closure (C i)) = univ)
    (q : σ → QuadraticFormula E)
    (hvalue : ∀ i, ∀ x ∈ closure (C i), x ∈ D → G x = (q i).eval x) :
    ContinuousOn G D := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_iff_isClosed.mpr
  intro S hS
  have heq : (fun x : D => G x) ⁻¹' S =
      ⋃ i, (Subtype.val ⁻¹' closure (C i)) ∩ (fun x : D => (q i).eval x) ⁻¹' S := by
    ext x
    simp only [mem_preimage, mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      have hc : (x : E) ∈ ⋃ i, closure (C i) := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := mem_iUnion.mp hc
      exact ⟨i, hi, by rwa [← hvalue i x hi x.property]⟩
    · rintro ⟨i, hi, hx⟩
      rwa [hvalue i x hi x.property]
  change IsClosed ((fun x : D => G x) ⁻¹' S)
  rw [heq]
  exact isClosed_iUnion_of_finite fun i =>
    (isClosed_closure.preimage continuous_subtype_val).inter
      (hS.preimage ((q i).continuous_eval.comp continuous_subtype_val))

omit [FiniteDimensional ℝ E] in
/-- The open sign regions cover every point away from the nontrivial walls. -/
theorem exists_region_of_off_walls {τ : Type*} (F : τ → E →ᵃ[ℝ] ℝ) (x : E)
    (hoff : ∀ w, F w ≠ 0 → F w x ≠ 0) : ∃ r, x ∈ openRegion F r := by
  classical
  refine ⟨fun w => decide (F w x ≤ 0), ?_⟩
  intro w
  by_cases hz : F w = 0
  · simp [hz]
  · simp only [hz, if_false]
    by_cases hle : F w x ≤ 0
    · simpa only [decide_eq_true hle, if_pos] using lt_of_le_of_ne hle (hoff w hz)
    · simpa only [decide_eq_false hle, Bool.false_eq_true, if_false] using lt_of_not_ge hle

variable {κ : Type*} [Fintype κ]

/-- Append the product representing the subtracted squared affine deficit. -/
def subtractSquare (q : QuadraticFormula (EndpointSpace κ)) (V : ℝ)
    (a : EndpointSpace κ →ᵃ[ℝ] ℝ) : QuadraticFormula (EndpointSpace κ) :=
  addFormula q ⟨1, fun _ => -V • a, fun _ => a⟩

omit [Fintype κ] in
theorem eval_subtractSquare (q : QuadraticFormula (EndpointSpace κ)) (V : ℝ)
    (a : EndpointSpace κ →ᵃ[ℝ] ℝ) (e : EndpointSpace κ) :
    (subtractSquare q V a).eval e = q.eval e-V*(a e)^2 := by
  rw [subtractSquare, eval_addFormula]
  simp [QuadraticFormula.eval, pow_two]
  ring

/-- A selected chart keeps the same actual cell formulas, total gap
formula and margin formula. Positive curvature is a proved property of
this margin formula at an actual global minimum. -/
structure PositiveMarginChart (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ)
    (D : Set (EndpointSpace κ)) (V : ℝ) (a : EndpointSpace κ →ᵃ[ℝ] ℝ) where
  region : Set (EndpointSpace κ)
  gapFormula : QuadraticFormula (EndpointSpace κ)
  cellFormula : Finset κ → QuadraticFormula (EndpointSpace κ)
  marginFormula : QuadraticFormula (EndpointSpace κ)
  point : EndpointSpace κ
  open_region : IsOpen region
  convex_region : Convex ℝ region
  interior_point : point ∈ interior D
  closure_point : point ∈ closure region
  strict_windows : ∀ i, point.1 i < point.2 i
  cell_area : ∀ s, ∀ e ∈ closure region,
    (volume (PlanarGapCells.signCell K f e.1 e.2 s)).toReal = (cellFormula s).eval e
  gap_sum : ∀ e, gapFormula.eval e = ∑ s : Finset κ, (cellFormula s).eval e
  gap_area : ∀ e ∈ closure region, (∀ i, e.1 i ≤ e.2 i) → area K f e = gapFormula.eval e
  margin_identity : ∀ e, marginFormula.eval e = gapFormula.eval e-V*(a e)^2
  minimum : IsMinOn (fun e => area K f e-V*(a e)^2) D point
  stationary : derivative marginFormula point = 0
  positive : ∀ z : EndpointSpace κ, z ≠ 0 → 0 < hessian marginFormula z z

namespace PositiveMarginChart

variable {K : Set Point} {f : κ → Point →ᵃ[ℝ] ℝ} {D : Set (EndpointSpace κ)}
  {V : ℝ} {a : EndpointSpace κ →ᵃ[ℝ] ℝ}

/-- The actual gap and margin formulas have the expected first-derivative
relation. It follows from their proved polynomial identity. -/
theorem derivative_identity (ch : PositiveMarginChart K f D V a) (x z : EndpointSpace κ) :
    derivative ch.gapFormula x z = derivative ch.marginFormula x z+2*V*(a x)*(a.linear z) := by
  have hp := ch.margin_identity (x+(1 : ℝ) • z)
  have hm := ch.margin_identity (x+(-1 : ℝ) • z)
  rw [QuadraticChartCalculus.eval_line, QuadraticChartCalculus.eval_line, affine_eval_line] at hp hm
  nlinarith only [hp, hm]

/-- The Hessians differ by the exact rank-one deficit term. -/
theorem hessian_identity (ch : PositiveMarginChart K f D V a) (z : EndpointSpace κ) :
    hessian ch.gapFormula z z = hessian ch.marginFormula z z+2*V*(a.linear z)^2 := by
  have hp := ch.margin_identity ((0 : EndpointSpace κ)+(1 : ℝ) • z)
  have hm := ch.margin_identity ((0 : EndpointSpace κ)+(-1 : ℝ) • z)
  have h0 := ch.margin_identity 0
  rw [QuadraticChartCalculus.eval_line, QuadraticChartCalculus.eval_line, affine_eval_line] at hp hm
  nlinarith only [hp, hm, h0]

theorem stationary_gap (ch : PositiveMarginChart K f D V a) :
    derivative ch.gapFormula ch.point = (2*V*(a ch.point)) • a.linear.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro z
  rw [ch.derivative_identity, ch.stationary, zero_apply, zero_add]
  rfl

theorem positive_gap_hessian (ch : PositiveMarginChart K f D V a) (hV : 0 ≤ V) :
    ∀ z : EndpointSpace κ, z ≠ 0 → 0 < hessian ch.gapFormula z z := by
  intro z hz
  rw [ch.hessian_identity]
  exact add_pos_of_pos_of_nonneg (ch.positive z hz)
    (mul_nonneg (mul_nonneg (by norm_num) hV) (sq_nonneg _))

end PositiveMarginChart

/-- Construct the actual quadratic atlas and select a positive-definite
margin chart from C1 regularity on the parameter-domain interior. Neither
body-facet nor pairwise plank transversality is required by this step. -/
theorem exists_actual_positive_margin_chart_of_regular {ι : Type*} [Fintype ι]
    [DecidableEq κ] (K : Set Point) (hcompact : IsCompact K) (hne : K.Nonempty)
    (F : ι → Point →ᵃ[ℝ] ℝ) (c : ι → ℝ) (hK : K = {x | ∀ j, F j x ≤ c j})
    (hF : ∀ j, (F j).linear ≠ 0)
    (f : κ → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, 0 < Plank.Convex.DeficientHeightTilt.rangeWidth K (f i))
    (D : Set (EndpointSpace κ)) (hD : IsCompact D)
    (hordered : ∀ e ∈ D, ∀ i, e.1 i ≤ e.2 i)
    (hstrict : ∀ e ∈ interior D, ∀ i, e.1 i < e.2 i)
    (hregular : ContDiffOn ℝ 1 (area K f) (interior D))
    (V : ℝ) (a : EndpointSpace κ →ᵃ[ℝ] ℝ) (e₀ : EndpointSpace κ) (he₀ : e₀ ∈ D)
    (hboundary : ∀ e ∈ D, e ∉ interior D →
      area K f e₀-V*(a e₀)^2 < area K f e-V*(a e)^2) :
    Nonempty (PositiveMarginChart K f D V a) := by
  classical
  let T := LinearEquiv.refl ℝ Point
  obtain ⟨M, _, hM⟩ := hcompact.isBounded.exists_pos_norm_le
  have hbox : K = PlanarPolygonHalfplanes.boxedRegion (-M) M (-M) M
      (PlanarDirectionDerivatives.bodyA T F) (PlanarDirectionDerivatives.bodyB T F)
      (PlanarDirectionDerivatives.bodyC F c) :=
    PlanarDirectionDerivatives.body_eq_boxed_preimage_of_bound K F c hK T M
      (fun x hx => hM x hx) (-M) M le_rfl le_rfl
  have hnormal (j) (hj : PlanarDirectionDerivatives.bodyB T F j = 0) :
      PlanarDirectionDerivatives.bodyA T F j ≠ 0 := by
    apply coefficients_nonzero (PlanarDirectionDerivatives.transform T (F j)) _ hj
    change (F j).linear ≠ 0
    exact hF j
  obtain ⟨Q, qc, hQ, hcover⟩ := exists_actual_gap_charts hcompact hne (-M) M (-M) M
    (PlanarDirectionDerivatives.bodyA T F) (PlanarDirectionDerivatives.bodyB T F)
    (PlanarDirectionDerivatives.bodyC F c) hbox hnormal f hf
  let (s : Finset κ) : Fintype (WallIndex
      (PlanarHalfplaneCharts.LowerY (cellB (PlanarDirectionDerivatives.bodyB T F) f s))
      (PlanarHalfplaneCharts.UpperY (cellB (PlanarDirectionDerivatives.bodyB T F) f s))) :=
    inferInstance
  let (s : Finset κ) : Fintype (PlanarHalfplaneCharts.HalfplaneWallIndex
      (cellA (PlanarDirectionDerivatives.bodyA T F) f s)
      (cellB (PlanarDirectionDerivatives.bodyB T F) f s)) := inferInstance
  let : Fintype (CellWallIndex (PlanarDirectionDerivatives.bodyA T F)
      (PlanarDirectionDerivatives.bodyB T F) f) := inferInstance
  let walls := cellWalls (-M) M (-M) M (PlanarDirectionDerivatives.bodyA T F)
    (PlanarDirectionDerivatives.bodyB T F) (PlanarDirectionDerivatives.bodyC F c) f
  let regions := openRegion walls
  let G (e : EndpointSpace κ) := area K f e-V*(a e)^2
  let qm r := subtractSquare (Q r) V a
  have harea : ContinuousOn (area K f) D := by
    apply continuousOn_of_closed_atlas (area K f) D regions hcover Q
    intro r e he hDmem
    exact (hQ r).2.2.2.2 e he (hordered e hDmem)
  have hGc : ContinuousOn G D := harea.sub
    (continuous_const.mul ((continuous_affine a).pow 2)).continuousOn
  have hreg : ContDiffOn ℝ 1 G (interior D) :=
    hregular.sub (contDiff_const.mul ((contDiff_affine a).pow 2)).contDiffOn
  have hvalue : ∀ r, ∀ e ∈ closure (regions r) ∩ interior D, G e = (qm r).eval e := by
    intro r e he
    rw [eval_subtractSquare]
    exact congrArg (fun t : ℝ => t-V*(a e)^2)
      ((hQ r).2.2.2.2 e he.1 (hordered e (interior_subset he.2)))
  obtain ⟨r, e, hi, hc, hmin, _, hs, hp⟩ := exists_positive_chart_minimizer G D hD hGc hreg
    e₀ he₀ hboundary regions (fun r => (hQ r).1) qm walls hcover
    (exists_region_of_off_walls walls) hvalue
  exact ⟨{
    region := regions r
    gapFormula := Q r
    cellFormula := qc r
    marginFormula := qm r
    point := e
    open_region := (hQ r).1
    convex_region := (hQ r).2.1
    interior_point := hi
    closure_point := hc
    strict_windows := hstrict e hi
    cell_area := (hQ r).2.2.2.1
    gap_sum := (hQ r).2.2.1
    gap_area := (hQ r).2.2.2.2
    margin_identity := eval_subtractSquare (Q r) V a
    minimum := hmin
    stationary := hs
    positive := hp }⟩

/-- The original transverse formulation, now a specialization of the
regularity-based selector. Its statement and geometric conclusion are unchanged. -/
theorem exists_actual_positive_margin_chart {ι : Type*} [Fintype ι] [Nonempty κ]
    [DecidableEq κ] (K : Set Point) (hcompact : IsCompact K) (hne : K.Nonempty)
    (F : ι → Point →ᵃ[ℝ] ℝ) (c : ι → ℝ) (hK : K = {x | ∀ j, F j x ≤ c j})
    (f : κ → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, 0 < Plank.Convex.DeficientHeightTilt.rangeWidth K (f i))
    (hbody : ∀ i j, PlanarDirectionDerivatives.cross (f i) (F j) ≠ 0)
    (hpairs : ∀ i j, i ≠ j → PlanarDirectionDerivatives.cross (f i) (f j) ≠ 0)
    (D : Set (EndpointSpace κ)) (hD : IsCompact D)
    (hordered : ∀ e ∈ D, ∀ i, e.1 i ≤ e.2 i)
    (hstrict : ∀ e ∈ interior D, ∀ i, e.1 i < e.2 i)
    (V : ℝ) (a : EndpointSpace κ →ᵃ[ℝ] ℝ) (e₀ : EndpointSpace κ) (he₀ : e₀ ∈ D)
    (hboundary : ∀ e ∈ D, e ∉ interior D →
      area K f e₀-V*(a e₀)^2 < area K f e-V*(a e)^2) :
    Nonempty (PositiveMarginChart K f D V a) := by
  have hF (j) : (F j).linear ≠ 0 := by
    intro hz
    have hc := hbody (Classical.choice (inferInstance : Nonempty κ)) j
    simp [PlanarDirectionDerivatives.cross, hz] at hc
  exact exists_actual_positive_margin_chart_of_regular K hcompact hne F c hK hF f hf
    D hD hordered hstrict
    ((contDiffOn_area_of_transverse_halfplanes K hcompact hne F c hK f hf hbody hpairs).mono
      hstrict) V a e₀ he₀ hboundary

end Plank.PlanarPositiveChart
