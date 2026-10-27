/- Exhaustive arithmetic equality test for planks on normalized four-point bodies. -/
module

public import Plank.Proofs.Quant.FourPointBox
public import Plank.Proofs.Quant.PlanarPlankCellCharts

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FourPointPlacements

open Set MeasureTheory PlanarQuantitative FourPointHalfplanes FourPointBox
open PlanarPolygonArithmetic PlanarPolygonHalfplanes PlanarPlankCellCharts PlanarGapCells
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def lower (a b : ℝ) (f : Point →ᵃ[ℝ] ℝ) : ℝ :=
  min (min (f ![0,0]) (f ![1,0])) (min (f ![0,1]) (f ![a,b]))
def upper (a b : ℝ) (f : Point →ᵃ[ℝ] ℝ) : ℝ :=
  max (max (f ![0,0]) (f ![1,0])) (max (f ![0,1]) (f ![a,b]))
def width (a b : ℝ) (f : Point →ᵃ[ℝ] ℝ) : ℝ := upper a b f-lower a b f

/-- The actual directional range is computed by four evaluations and
finite maxima/minima, including every possible position of the fourth point. -/
theorem rangeWidth_eq (a b : ℝ) (f : Point →ᵃ[ℝ] ℝ) :
    rangeWidth (body a b) f = width a b f := by
  have hb : body a b ⊆ f ⁻¹' Icc (lower a b f) (upper a b f) := by
    apply convexHull_min _ ((convex_Icc _ _).affine_preimage f)
    intro x hx
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      simp [lower,upper]
  have hm {x y : ℝ} (hx : x ∈ f '' body a b) (hy : y ∈ f '' body a b) :
      min x y ∈ f '' body a b := by
    rcases min_choice x y with h | h <;> rwa [h]
  have hM {x y : ℝ} (hx : x ∈ f '' body a b) (hy : y ∈ f '' body a b) :
      max x y ∈ f '' body a b := by
    rcases max_choice x y with h | h <;> rwa [h]
  have h0 : f ![0,0] ∈ f '' body a b := ⟨_,subset_convexHull ℝ _ (by simp),rfl⟩
  have h1 : f ![1,0] ∈ f '' body a b := ⟨_,subset_convexHull ℝ _ (by simp),rfl⟩
  have h2 : f ![0,1] ∈ f '' body a b := ⟨_,subset_convexHull ℝ _ (by simp),rfl⟩
  have h3 : f ![a,b] ∈ f '' body a b := ⟨_,subset_convexHull ℝ _ (by simp),rfl⟩
  have hmax : IsGreatest (f '' body a b) (upper a b f) :=
    ⟨hM (hM h0 h1) (hM h2 h3),by rintro _ ⟨x,hx,rfl⟩; exact (hb hx).2⟩
  have hmin : IsLeast (f '' body a b) (lower a b f) :=
    ⟨hm (hm h0 h1) (hm h2 h3),by rintro _ ⟨x,hx,rfl⟩; exact (hb hx).1⟩
  unfold rangeWidth Plank.Body.width width
  rw [hmax.csSup_eq,hmin.csInf_eq]

variable {ι : Type*} [Fintype ι]

def relativeSum (a b : ℝ) (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) : ℝ :=
  ∑ i, (hi i-lo i)/width a b (f i)

def CellTest (a b : ℝ) (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (s : Finset ι) (z : ℝ) : Prop :=
  BoxTest (-radius a b) (radius a b) (-radius a b) (radius a b)
    (cellA (A a b) f s) (cellB (B a b) f s) (fun k => cellC (C a b) f s k (lo,hi)) z

theorem cellTest_iff (a b : ℝ) (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (s : Finset ι) (z : ℝ) :
    CellTest a b f lo hi s z ↔ (volume (signCell (body a b) f lo hi s)).toReal = z := by
  rw [body_eq_boxed,signCell_eq_boxedRegion _ _ _ _ _ _ _ f (lo,hi) s]
  exact boxTest_iff _ _ _ _ _ _ _ _

/-- Finite arithmetic classification of all placements. It uses only the
twenty body rows, the exterior plank rows, their finite crossing/facet tests,
and the displayed scalar equality. There is no area, set containment,
covering, convexity or tightness hypothesis in this predicate. -/
def TightParameters (a b : ℝ) (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) : Prop :=
  ∃ (z : ℝ) (v : Finset ι → ℝ),
    BoxTest (-radius a b) (radius a b) (-radius a b) (radius a b) (A a b) (B a b) (C a b) z ∧
    (∀ s, CellTest a b f lo hi s (v s)) ∧
    (∑ s, v s) = (max 0 (1-relativeSum a b f lo hi))^2*z

/-- Exhaustive iff for every finite family of physical closed planks on
the normalized hull of four points. Repeated or parallel directions,
zero-width planks, exterior endpoints, boundary contacts and R>=1 are all
included. Only the actual positive directional ranges and endpoint order
are required, and both are explicit arithmetic input conditions. -/
theorem equality_iff (a b : ℝ) (f : ι → Point →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hwidth : ∀ i, 0 < width a b (f i)) (horder : ∀ i, lo i ≤ hi i) :
    (volume (body a b \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal =
        (max 0 (1-∑ i, (hi i-lo i)/rangeWidth (body a b) (f i)))^2*(volume (body a b)).toReal ↔
      TightParameters a b f lo hi := by
  classical
  have hg := area_gap_eq_sum_signCells (compact_body a b) (nonempty_body a b) f
    (fun i => by rw [rangeWidth_eq]; exact hwidth i) lo hi horder
  have hr : (∑ i, (hi i-lo i)/rangeWidth (body a b) (f i)) = relativeSum a b f lo hi := by
    simp only [rangeWidth_eq,relativeSum]
  rw [hg,hr]
  constructor
  · intro he
    exact ⟨(volume (body a b)).toReal,fun s => (volume (signCell (body a b) f lo hi s)).toReal,
      (body_area_iff a b _).mpr rfl,fun s => (cellTest_iff a b f lo hi s _).mpr rfl,he⟩
  · rintro ⟨z,v,hz,hv,he⟩
    have hbody := (body_area_iff a b z).mp hz
    have hcell (s) := (cellTest_iff a b f lo hi s (v s)).mp (hv s)
    simpa only [hbody,hcell] using he

end Plank.FourPointPlacements

/-- info: 'Plank.FourPointPlacements.equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FourPointPlacements.equality_iff
