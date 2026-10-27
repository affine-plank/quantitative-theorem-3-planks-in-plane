/- Exhaustive geometric equality families for finite parallel planks on
arbitrary planar convex bodies, including zero-width windows. -/
module

public import Plank.Proofs.Quant.PlanarParallelActive
public import Plank.Proofs.Quant.PlanarParallelNoWaste

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelClassification

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParallelTranslations
  PlanarParallelActive PlanarOnePlankVertices
open Plank.Convex.DeficientHeightTilt

/-- The positive windows tile a single band. Its endpoints and total width
determine the common base level of the two triangles making up the body.
Zero-width planks can lie anywhere. -/
def Tiling {ι : Type*} [Fintype ι] (K : Set Point) (lo hi : ι → ℝ)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) : Prop :=
  ∃ L H : ℝ, 0 ≤ L ∧ H ≤ 1 ∧ L < H ∧
    (⋃ i : Active lo hi, Icc (lo i.1) (hi i.1)) = Icc L H ∧ H-L = total lo hi ∧
    ∃ c ∈ K, ∃ d ∈ K, f c = L/(1-total lo hi) ∧
      f d = L/(1-total lo hi) ∧ K = fourPointBody a b c d

theorem Tiling.bounds {ι : Type*} [Fintype ι] {K : Set Point} {lo hi : ι → ℝ}
    {f : Point →ᵃ[ℝ] ℝ} {a b : Point} (ht : Tiling K lo hi f a b) (i : Active lo hi) :
    0 ≤ lo i.1 ∧ hi i.1 ≤ 1 := by
  obtain ⟨L,H,hL,hH,_,hu,_⟩ := ht
  have hl : lo i.1 ∈ Icc L H := hu ▸ mem_iUnion.mpr ⟨i,le_rfl,i.2.le⟩
  have hh : hi i.1 ∈ Icc L H := hu ▸ mem_iUnion.mpr ⟨i,i.2.le,le_rfl⟩
  exact ⟨hL.trans hl.1,hh.2.trans hH⟩

/-- Full finite parallel-plank classification in a common normalized affine
coordinate. There is no prior restriction on where the windows lie, and
zero-width windows are allowed. Both directions concern actual area. -/
theorem equality_iff_tiling {ι : Type*} [Fintype ι] {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR : 0 < total lo hi) (hR1 : total lo hi < 1)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0) (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) :
    (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
        (1-total lo hi)^2*(volume K).toReal ↔ Tiling K lo hi f a b := by
  classical
  have hW : rangeWidth K f = 1 := by
    have hw : rangeWidth K f = f a-f b := Body.width_eq_of_realisers ha hb
      (fun x hx => by rw [hfa]; exact (hf x hx).2)
      (fun x hx => by rw [hfb]; exact (hf x hx).1)
    rw [hw,hfa,hfb,sub_zero]
  have hWp : 0 < rangeWidth K f := by rw [hW]; norm_num
  have hlinear := linear_ne_zero_of_rangeWidth_pos ⟨a,ha⟩ f hWp
  have : Nonempty (Active lo hi) := active_nonempty lo hi ho hR
  let al := fun i : Active lo hi => lo i.1
  let ah := fun i : Active lo hi => hi i.1
  have htot : total al ah = total lo hi := total_active lo hi ho
  have hgap := gap_eq_active K lo hi ho f hlinear
  have hiff (hl : ∀ i, 0 ≤ al i) (hh : ∀ i, ah i ≤ 1) :=
    PlanarParallelPositive.equality_iff_tiling hK hconv hV al ah (fun i => i.2) hl hh
      (by rw [htot]; exact hR) (by rw [htot]; exact hR1) f a b ha hb hfa hfb hf
  constructor
  · intro he
    have hbound (i : Active lo hi) : 0 ≤ al i ∧ ah i ≤ 1 :=
      PlanarParallelNoWaste.positive_window_no_waste hK hconv hV lo hi ho hR1
        f a b ha hb hfa hfb hf he i.1 i.2
    have heactive : (volume (K \ ⋃ i, LinearBands.closedBand f (al i) (ah i))).toReal =
        (1-total al ah)^2*(volume K).toReal := by rw [← hgap,htot]; exact he
    have ht := (hiff (fun i => (hbound i).1) (fun i => (hbound i).2)).mp heactive
    simpa only [Tiling,htot] using ht
  · intro ht
    have heactive := (hiff (fun i => (ht.bounds i).1) (fun i => (ht.bounds i).2)).mpr
      (by simpa only [Tiling,htot] using ht)
    rw [← hgap,htot] at heactive
    exact heactive

end Plank.PlanarParallelClassification

/-- info: 'Plank.PlanarParallelClassification.equality_iff_tiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelClassification.equality_iff_tiling
