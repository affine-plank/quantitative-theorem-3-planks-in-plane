/- Local equality motions on polygons outside finitely many explicit
affine walls. No stationarity or curvature hypothesis is left unproved. -/
module

public import Plank.Proofs.Quant.PlanarEqualityFlatDirection

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPolygonEqualityMotion

open Set MeasureTheory PlanarQuantitative PlanarPolygonCharts PlanarPlankCellCharts
  PlanarParameterDomain PlanarPositiveChart PlanarEqualityFlatDirection
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators Topology

/-- The existing geometric cell atlas constructs the chart required by
the equality-motion theorem at every point off its nontrivial walls. -/
theorem exists_chart_off_walls {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hne : K.Nonempty)
    (a b c d : ℝ) (A B C : ι → ℝ)
    (hrep : K = PlanarPolygonHalfplanes.boxedRegion a b c d A B C)
    (hbody : ∀ i, B i = 0 → A i ≠ 0) (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (p : Endpoints 2)
    (hoff : ∀ w, cellWalls a b c d A B C f w ≠ 0 → cellWalls a b c d A B C f w p ≠ 0) :
    ∃ ch : OpenChart K f, ch.point = p ∧
      ∃ r, ch.region = openRegion (cellWalls a b c d A B C f) r := by
  obtain ⟨Q,qc,hQ,_⟩ := exists_actual_gap_charts hK hne a b c d A B C hrep hbody f hW
  obtain ⟨r,hr⟩ := exists_region_of_off_walls (cellWalls a b c d A B C f) p hoff
  exact ⟨{
    region := openRegion (cellWalls a b c d A B C f) r
    open_region := (hQ r).1
    point := p
    point_mem := hr
    cellFormula := qc r
    gapFormula := Q r
    cell_area := (hQ r).2.2.2.1
    gap_sum := (hQ r).2.2.1 },rfl,r,rfl⟩

/-- Every compact positive-area convex polygon has a finite list of affine
endpoint walls. Away from those walls, any interior two-plank equality
has an actual local equality motion that does not increase total width
for positive time. The third paragraph of the conclusion is not an
assumed polynomial equality: it is the original geometric gap area. -/
theorem finite_walls_for_polygon {ι : Type*} [Fintype ι]
    {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (F : ι → Point →ᵃ[ℝ] ℝ) (c : ι → ℝ) (hrep : K = {x | ∀ j, F j x ≤ c j})
    (hF : ∀ j, (F j).linear ≠ 0) (f : Fin 2 → Point →ᵃ[ℝ] ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) :
    ∃ n : ℕ, ∃ W : Fin n → Endpoints 2 →ᵃ[ℝ] ℝ,
      Dense {p | ∀ i, W i ≠ 0 → W i p ≠ 0} ∧
      ∀ p : Endpoints 2, (∀ i, W i ≠ 0 → W i p ≠ 0) →
        p ∈ interior (domain K f) → budget K f p < 1 →
        gapArea K f p = (1-budget K f p)^2*(volume K).toReal →
        ∃ z : Endpoints 2, z ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
          p+t • z ∈ interior (domain K f) ∧
          gapArea K f (p+t • z) = (1-budget K f (p+t • z))^2*(volume K).toReal ∧
          (0 ≤ t → budget K f (p+t • z) ≤ budget K f p) := by
  classical
  let T := LinearEquiv.refl ℝ Point
  obtain ⟨M,_,hM⟩ := hK.isBounded.exists_pos_norm_le
  let A := PlanarDirectionDerivatives.bodyA T F
  let B := PlanarDirectionDerivatives.bodyB T F
  let C := PlanarDirectionDerivatives.bodyC F c
  have hbox : K = PlanarPolygonHalfplanes.boxedRegion (-M) M (-M) M A B C :=
    PlanarDirectionDerivatives.body_eq_boxed_preimage_of_bound K F c hrep T M
      (fun x hx => hM x hx) (-M) M le_rfl le_rfl
  have hnormal (j) (hj : B j = 0) : A j ≠ 0 := by
    apply coefficients_nonzero (PlanarDirectionDerivatives.transform T (F j)) _ hj
    change (F j).linear ≠ 0
    exact hF j
  let (s : Finset (Fin 2)) : Fintype (PlanarPolygonCharts.WallIndex
      (PlanarHalfplaneCharts.LowerY (cellB B f s))
      (PlanarHalfplaneCharts.UpperY (cellB B f s))) := inferInstance
  let (s : Finset (Fin 2)) : Fintype (PlanarHalfplaneCharts.HalfplaneWallIndex
      (cellA A f s) (cellB B f s)) := inferInstance
  let : Fintype (CellWallIndex A B f) := inferInstance
  let e := Fintype.equivFin (CellWallIndex A B f)
  let walls := cellWalls (-M) M (-M) M A B C f
  let W := fun i => walls (e.symm i)
  refine ⟨Fintype.card (CellWallIndex A B f),W,dense_off_walls W,?_⟩
  intro p hoff hp hR heq
  have hoff' (w) (hw : walls w ≠ 0) : walls w p ≠ 0 := by
    have hh : walls w ≠ 0 → walls w p ≠ 0 := by
      simpa only [W,Equiv.symm_apply_apply] using hoff (e w)
    exact hh hw
  obtain ⟨ch,hch,_⟩ := exists_chart_off_walls hK hne (-M) M (-M) M A B C hbox hnormal f hW p hoff'
  obtain ⟨z,hzne,ε,hε,hmotion⟩ := ch.exists_actual_equality_motion hK hconv hne hV hW
    (by rwa [hch]) (by rwa [hch]) (by rwa [hch])
  refine ⟨z,hzne,ε,hε,?_⟩
  intro t ht
  have hh := (hmotion t ht).2
  simpa only [hch] using hh

end Plank.PlanarPolygonEqualityMotion

/-- info: 'Plank.PlanarPolygonEqualityMotion.finite_walls_for_polygon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarPolygonEqualityMotion.finite_walls_for_polygon
