/- One constructed affine arrangement for all actual polygonal plank cells. -/
module

public import Plank.Proofs.Quant.PlanarHalfplaneCharts
public import Plank.Proofs.Quant.PlanarCellCurvature
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPlankCellCharts

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarPolygonCharts
open PlanarPolygonHalfplanes PlanarHalfplaneCharts

abbrev EndpointSpace (κ : Type*) := (κ → ℝ) × (κ → ℝ)

def loMap {κ : Type*} (i : κ) : EndpointSpace κ →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj i).comp (LinearMap.fst ℝ (κ → ℝ) (κ → ℝ))).toAffineMap

def hiMap {κ : Type*} (i : κ) : EndpointSpace κ →ᵃ[ℝ] ℝ :=
  ((LinearMap.proj i).comp (LinearMap.snd ℝ (κ → ℝ) (κ → ℝ))).toAffineMap

def cellA {ι κ : Type*} (A : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) : ι ⊕ κ → ℝ := by
  classical
  exact Sum.elim A (fun i => if i ∈ s then -(f i).linear (Pi.single 0 1)
    else (f i).linear (Pi.single 0 1))

def cellB {ι κ : Type*} (B : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) : ι ⊕ κ → ℝ := by
  classical
  exact Sum.elim B (fun i => if i ∈ s then -(f i).linear (Pi.single 1 1)
    else (f i).linear (Pi.single 1 1))

def cellC {ι κ : Type*} (C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) :
    ι ⊕ κ → EndpointSpace κ →ᵃ[ℝ] ℝ := by
  classical
  exact Sum.elim (fun i => AffineMap.const ℝ (EndpointSpace κ) (C i))
    (fun i => if i ∈ s then AffineMap.const ℝ (EndpointSpace κ) (f i 0)-hiMap i
      else loMap i-AffineMap.const ℝ (EndpointSpace κ) (f i 0))

/-- Exact set identification of every actual closed exterior plank cell
with the finite half-plane model, for arbitrary endpoint values. -/
theorem signCell_eq_boxedRegion {ι κ : Type*}
    (a b c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (e : EndpointSpace κ) (s : Finset κ) :
    signCell (boxedRegion a b c d A B C) f e.1 e.2 s =
      boxedRegion a b c d (cellA A f s) (cellB B f s) (fun i => cellC C f s i e) := by
  classical
  ext x
  constructor
  · rintro ⟨hK, hs⟩
    refine ⟨hK.1, hK.2.1, ?_⟩
    intro k
    cases k with
    | inl i => exact hK.2.2 i
    | inr i =>
      have hi := hs i
      have hf := affine_eval_coordinates (f i) x
      by_cases his : i ∈ s
      · simp only [his, if_pos] at hi
        simp only [cellA, cellB, cellC, Sum.elim_inr, his, if_pos]
        change -(f i).linear (Pi.single 0 1)*x 0 + -(f i).linear (Pi.single 1 1)*x 1 ≤ f i 0-e.2 i
        linarith only [hi, hf]
      · simp only [his, if_false] at hi
        simp only [cellA, cellB, cellC, Sum.elim_inr, his, if_false]
        change (f i).linear (Pi.single 0 1)*x 0 + (f i).linear (Pi.single 1 1)*x 1 ≤ e.1 i-f i 0
        linarith only [hi, hf]
  · intro hx
    refine ⟨⟨hx.1, hx.2.1, fun i => hx.2.2 (Sum.inl i)⟩, fun i => ?_⟩
    have hi := hx.2.2 (Sum.inr i)
    have hf := affine_eval_coordinates (f i) x
    by_cases his : i ∈ s
    · simp only [cellA, cellB, cellC, Sum.elim_inr, his, if_pos] at hi
      change -(f i).linear (Pi.single 0 1)*x 0 + -(f i).linear (Pi.single 1 1)*x 1 ≤ f i 0-e.2 i at hi
      simp only [his, if_pos]
      linarith only [hi, hf]
    · simp only [cellA, cellB, cellC, Sum.elim_inr, his, if_false] at hi
      change (f i).linear (Pi.single 0 1)*x 0 + (f i).linear (Pi.single 1 1)*x 1 ≤ e.1 i-f i 0 at hi
      simp only [his, if_false]
      linarith only [hi, hf]

theorem coefficients_nonzero (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (hB : f.linear (Pi.single 1 1) = 0) : f.linear (Pi.single 0 1) ≠ 0 := by
  intro hA
  apply hf
  apply LinearMap.ext
  intro x
  have hc : f x = f 0 := by simp only [affine_eval_coordinates f x, hA, hB, zero_mul, zero_add]
  have hd : f x = f.linear x + f 0 := congrFun f.decomp x
  change f.linear x = 0
  linarith only [hc, hd]

theorem cell_normals_nonzero {ι κ : Type*} (A B : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hbody : ∀ i, B i = 0 → A i ≠ 0) (hf : ∀ i, (f i).linear ≠ 0) (s : Finset κ) :
    ∀ i, cellB B f s i = 0 → cellA A f s i ≠ 0 := by
  classical
  intro k
  cases k with
  | inl i => exact hbody i
  | inr i =>
    by_cases his : i ∈ s
    · simp only [cellA, cellB, Sum.elim_inr, his, if_pos, neg_eq_zero, ne_eq]
      exact coefficients_nonzero (f i) (hf i)
    · simp only [cellA, cellB, Sum.elim_inr, his, if_false]
      exact coefficients_nonzero (f i) (hf i)

/-- One explicit finite wall index for all exterior sign cells. -/
abbrev CellWallIndex {ι κ : Type*} (A B : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ) :=
  Sigma (fun s : Finset κ => HalfplaneWallIndex (cellA A f s) (cellB B f s))

def cellWalls {ι κ : Type*} (a b c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ) :
    CellWallIndex A B f → EndpointSpace κ →ᵃ[ℝ] ℝ := fun w =>
  halfplaneWalls (AffineMap.const ℝ _ a) (AffineMap.const ℝ _ b)
    (AffineMap.const ℝ _ c) (AffineMap.const ℝ _ d)
    (cellA A f w.1) (cellB B f w.1) (cellC C f w.1) w.2

/-- The actual exterior cells of a finite-half-plane body have quadratic
areas on closures of one constructed finite affine arrangement in all plank
endpoints. Both body and plank directions are arbitrary and fixed. -/
theorem exists_actual_cell_charts {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b c d : ℝ) (A B C : ι → ℝ) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hbody : ∀ i, B i = 0 → A i ≠ 0) (hf : ∀ i, (f i).linear ≠ 0) :
    ∃ Q : (CellWallIndex A B f → Bool) → Finset κ → QuadraticFormula (EndpointSpace κ),
      (∀ r, IsOpen (openRegion (cellWalls a b c d A B C f) r) ∧
        Convex ℝ (openRegion (cellWalls a b c d A B C f) r) ∧
        ∀ s, ∀ e ∈ closure (openRegion (cellWalls a b c d A B C f) r),
          (volume (signCell (boxedRegion a b c d A B C) f e.1 e.2 s)).toReal = (Q r s).eval e) ∧
      (⋃ r, closure (openRegion (cellWalls a b c d A B C f) r)) = univ := by
  classical
  obtain ⟨Q, hQ, hcover⟩ := exists_common_boxed_area_charts
    (fun _ : Finset κ => AffineMap.const ℝ (EndpointSpace κ) a)
    (fun _ => AffineMap.const ℝ (EndpointSpace κ) b)
    (fun _ => AffineMap.const ℝ (EndpointSpace κ) c)
    (fun _ => AffineMap.const ℝ (EndpointSpace κ) d)
    (cellA A f) (cellB B f) (cellC C f) (cell_normals_nonzero A B f hbody hf)
  refine ⟨Q, fun r => ⟨(hQ r).1, (hQ r).2.1, fun s e he => ?_⟩, hcover⟩
  rw [signCell_eq_boxedRegion]
  exact (hQ r).2.2 s e he

def addFormula {κ : Type*} (q r : QuadraticFormula (EndpointSpace κ)) : QuadraticFormula (EndpointSpace κ) :=
  ⟨q.size+r.size, fun k => if k < q.size then q.left k else r.left (k-q.size),
    fun k => if k < q.size then q.right k else r.right (k-q.size)⟩

theorem eval_addFormula {κ : Type*} (q r : QuadraticFormula (EndpointSpace κ)) (x : EndpointSpace κ) :
    (addFormula q r).eval x = q.eval x+r.eval x := by
  unfold QuadraticFormula.eval addFormula
  dsimp only
  rw [Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [if_pos (Finset.mem_range.mp hk)]
  · apply Finset.sum_congr rfl
    intro k _
    have hk : ¬q.size+k < q.size := by omega
    simp only [if_neg hk, Nat.add_sub_cancel_left]

theorem exists_sumFormula {σ κ : Type*} (s : Finset σ)
    (q : σ → QuadraticFormula (EndpointSpace κ)) :
    ∃ Q : QuadraticFormula (EndpointSpace κ), ∀ x, Q.eval x = ∑ i ∈ s, (q i).eval x := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨QuadraticFormula.zero, by simp [QuadraticFormula.zero, QuadraticFormula.eval]⟩
  | @insert i s hi ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨addFormula (q i) Q, fun x => ?_⟩
    rw [eval_addFormula, hQ, Finset.sum_insert hi]

/-- The common cell atlas yields an actual uncovered-area quadratic on
every closed chart, for all ordered plank endpoints. All widths in the
hypotheses are the actual directional ranges from the final target. -/
theorem exists_actual_gap_charts {ι κ : Type*} [Fintype ι] [Fintype κ]
    {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (a b c d : ℝ) (A B C : ι → ℝ) (hrep : K = boxedRegion a b c d A B C)
    (hbody : ∀ i, B i = 0 → A i ≠ 0) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, 0 < Plank.Convex.DeficientHeightTilt.rangeWidth K (f i)) :
    ∃ (Q : (CellWallIndex A B f → Bool) → QuadraticFormula (EndpointSpace κ))
      (qc : (CellWallIndex A B f → Bool) → Finset κ → QuadraticFormula (EndpointSpace κ)),
      (∀ r, IsOpen (openRegion (cellWalls a b c d A B C f) r) ∧
        Convex ℝ (openRegion (cellWalls a b c d A B C f) r) ∧
        (∀ e, (Q r).eval e = ∑ s : Finset κ, (qc r s).eval e) ∧
        (∀ s, ∀ e ∈ closure (openRegion (cellWalls a b c d A B C f) r),
          (volume (signCell K f e.1 e.2 s)).toReal = (qc r s).eval e) ∧
        ∀ e ∈ closure (openRegion (cellWalls a b c d A B C f) r),
          (∀ i, e.1 i ≤ e.2 i) →
          (volume (K \ ⋃ i, {x | e.1 i ≤ f i x ∧ f i x ≤ e.2 i})).toReal = (Q r).eval e) ∧
      (⋃ r, closure (openRegion (cellWalls a b c d A B C f) r)) = univ := by
  classical
  have hfn (i : κ) : (f i).linear ≠ 0 := linear_ne_zero_of_rangeWidth_pos hne (f i) (hf i)
  obtain ⟨qc, hc, hcover⟩ := exists_actual_cell_charts a b c d A B C f hbody hfn
  have hsum (r : CellWallIndex A B f → Bool) :
      ∃ Q : QuadraticFormula (EndpointSpace κ), ∀ e, Q.eval e = ∑ s : Finset κ, (qc r s).eval e :=
    exists_sumFormula Finset.univ (qc r)
  choose Q hQ using hsum
  refine ⟨Q, qc, fun r => ⟨(hc r).1, (hc r).2.1, hQ r, ?_, ?_⟩, hcover⟩
  · intro s e he
    rw [hrep]
    exact (hc r).2.2 s e he
  · intro e he hwidth
    rw [area_gap_eq_sum_signCells hK hne f hf e.1 e.2 hwidth, hQ r]
    apply Finset.sum_congr rfl
    intro s _
    rw [hrep]
    exact (hc r).2.2 s e he

/-- A genuine open actual-area chart supplies the interval required by
the already proved Brunn--Minkowski curvature estimate. -/
theorem curvature_on_cell_chart {κ : Type*} [Fintype κ]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ)
    (q : QuadraticFormula (EndpointSpace κ)) {U : Set (EndpointSpace κ)} (hU : IsOpen U)
    (hchart : ∀ e ∈ closure U, (volume (signCell K f e.1 e.2 s)).toReal = q.eval e)
    (e : EndpointSpace κ) (he : e ∈ U)
    (hpos : 0 < (volume (signCell K f e.1 e.2 s)).toReal) (z : EndpointSpace κ) :
    ∃ g H : ℝ,
      (∀ t : ℝ, q.eval (e+t • z) =
        (volume (signCell K f e.1 e.2 s)).toReal+g*t+(H/2)*t^2) ∧
      H ≤ g^2/(2*(volume (signCell K f e.1 e.2 s)).toReal) := by
  obtain ⟨A, g, H, hline⟩ := q.eval_line e z
  have hA : A = (volume (signCell K f e.1 e.2 s)).toReal := by
    have h0 : q.eval e = A := by simpa using hline 0
    exact h0.symm.trans (hchart e (subset_closure he)).symm
  subst A
  have hopen : IsOpen {t : ℝ | e+t • z ∈ U} := hU.preimage (by fun_prop)
  have hzero : (0 : ℝ) ∈ {t : ℝ | e+t • z ∈ U} := by simpa using he
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hzero)
  have ht : 0 < epsilon/2 := by linarith
  have hinside : ∀ t ∈ Icc (0 : ℝ) (epsilon/2), e+t • z ∈ U := by
    intro t ht'
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht'.1]
    linarith only [ht'.2, hepsilon]
  refine ⟨g, H, hline, ?_⟩
  apply curvature_of_quadratic_signCell_area hK hconv f e.1 e.2 z.1 z.2 s
    _ g H (epsilon/2) hpos ht
  intro t ht'
  have hc := hchart (e+t • z) (subset_closure (hinside t ht'))
  exact hc.trans (hline t)

/-- Curvature for the actual polygonal plank cells now follows from a
constructed common atlas. No quadratic area identity is an input. -/
theorem exists_actual_cell_charts_with_curvature {ι κ : Type*} [Fintype ι] [Fintype κ]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (a b c d : ℝ) (A B C : ι → ℝ) (hrep : K = boxedRegion a b c d A B C)
    (hbody : ∀ i, B i = 0 → A i ≠ 0) (f : κ → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, 0 < Plank.Convex.DeficientHeightTilt.rangeWidth K (f i)) :
    ∃ qc : (CellWallIndex A B f → Bool) → Finset κ → QuadraticFormula (EndpointSpace κ),
      (∀ r, IsOpen (openRegion (cellWalls a b c d A B C f) r) ∧
        Convex ℝ (openRegion (cellWalls a b c d A B C f) r) ∧
        ∀ s,
          (∀ e ∈ closure (openRegion (cellWalls a b c d A B C f) r),
            (volume (signCell K f e.1 e.2 s)).toReal = (qc r s).eval e) ∧
          ∀ e ∈ openRegion (cellWalls a b c d A B C f) r,
            0 < (volume (signCell K f e.1 e.2 s)).toReal → ∀ z : EndpointSpace κ,
            ∃ g H : ℝ,
              (∀ t : ℝ, (qc r s).eval (e+t • z) =
                (volume (signCell K f e.1 e.2 s)).toReal+g*t+(H/2)*t^2) ∧
              H ≤ g^2/(2*(volume (signCell K f e.1 e.2 s)).toReal)) ∧
      (⋃ r, closure (openRegion (cellWalls a b c d A B C f) r)) = univ := by
  have hfn (i : κ) : (f i).linear ≠ 0 := linear_ne_zero_of_rangeWidth_pos hne (f i) (hf i)
  obtain ⟨qc, hc, hcover⟩ := exists_actual_cell_charts a b c d A B C f hbody hfn
  refine ⟨qc, fun r => ⟨(hc r).1, (hc r).2.1, fun s => ?_⟩, hcover⟩
  have hchart : ∀ e ∈ closure (openRegion (cellWalls a b c d A B C f) r),
      (volume (signCell K f e.1 e.2 s)).toReal = (qc r s).eval e := by
    intro e he
    rw [hrep]
    exact (hc r).2.2 s e he
  exact ⟨hchart, fun e he hpos z => curvature_on_cell_chart hK hconv f s
    (qc r s) (hc r).1 hchart e he hpos z⟩

end Plank.PlanarPlankCellCharts
