/- Complete geometric equality families for positive parallel windows
inside their normalized support interval, on arbitrary convex bodies. -/
module

public import Plank.Proofs.Quant.PlanarParallelInterval

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelPositive

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParallelTranslations
  PlanarParallelInterval PlanarOnePlankVertices
open Plank.Convex.DeficientHeightTilt

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem bands_eq_of_intervals_eq (lo hi : ι → ℝ) (f : Point →ᵃ[ℝ] ℝ)
    (L H : ℝ) (he : (⋃ i, Icc (lo i) (hi i)) = Icc L H) :
    (⋃ i, LinearBands.closedBand f (lo i) (hi i)) = {x | L ≤ f x ∧ f x ≤ H} := by
  ext x
  rw [mem_iUnion]
  change (∃ i, f x ∈ Icc (lo i) (hi i)) ↔ f x ∈ Icc L H
  rw [← mem_iUnion,he]

/-- Positive parallel windows are tight exactly when they tile a single
interval, whose associated one-plank body is a calibrated double triangle.
The right side specifies actual shapes and windows, with no area equation. -/
theorem equality_iff_tiling [Nonempty ι] {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (lo hi : ι → ℝ) (ho : ∀ i, lo i < hi i)
    (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hR : 0 < total lo hi) (hR1 : total lo hi < 1)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0) (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1) :
    (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
        (1-total lo hi)^2*(volume K).toReal ↔
      ∃ L H : ℝ, 0 ≤ L ∧ H ≤ 1 ∧ L < H ∧
        (⋃ i, Icc (lo i) (hi i)) = Icc L H ∧ H-L = total lo hi ∧
        ∃ c ∈ K, ∃ d ∈ K, f c = L/(1-total lo hi) ∧
          f d = L/(1-total lo hi) ∧ K = fourPointBody a b c d := by
  classical
  constructor
  · intro he
    obtain ⟨iL,_,hL⟩ := Finset.exists_min_image Finset.univ lo Finset.univ_nonempty
    obtain ⟨iH,_,hH⟩ := Finset.exists_max_image Finset.univ hi Finset.univ_nonempty
    have hl (i) : lo iL ≤ lo i := hL i (Finset.mem_univ i)
    have hh (i) : hi i ≤ hi iH := hH i (Finset.mem_univ i)
    have hunion := union_eq_interval_of_equality hK hconv hV lo hi ho hlo hhi
      hR hR1 f a b ha hb hfa hfb he iL iH hl hh
    have hLH : lo iL < hi iH := (ho iL).trans_le (hh iL)
    have hW : rangeWidth K f = 1 := by
      have hw : rangeWidth K f = f a-f b := Body.width_eq_of_realisers ha hb
        (fun x hx => by rw [hfa]; exact (hf x hx).2)
        (fun x hx => by rw [hfb]; exact (hf x hx).1)
      rw [hw,hfa,hfb,sub_zero]
    have hlen := length_eq_total_of_equality hK hconv hV lo hi (fun i => (ho i).le)
      hR1 f hW he (lo iL) (hi iH) hLH.le hunion
    have hend : lo iL+total lo hi = hi iH := by linarith only [hlen]
    have hmerged : (volume (K \ {x | lo iL ≤ f x ∧ f x ≤ lo iL+total lo hi})).toReal =
        (1-total lo hi)^2*(volume K).toReal := by
      rw [hend,← bands_eq_of_intervals_eq lo hi f _ _ hunion]
      exact he
    have hshape := (PlanarOnePlankVertices.equality_iff_fourPointBody hK hconv hV f
      a b ha hb hfa hfb hf (lo iL) (total lo hi) hR hR1).mp hmerged
    exact ⟨lo iL,hi iH,hlo iL,hhi iH,hLH,hunion,hlen,hshape.2.2⟩
  · rintro ⟨L,H,hL,hH,_,hunion,hlen,hshape⟩
    have hend : L+total lo hi = H := by linarith only [hlen]
    rw [bands_eq_of_intervals_eq lo hi f L H hunion,← hend]
    apply (PlanarOnePlankVertices.equality_iff_fourPointBody hK hconv hV f
      a b ha hb hfa hfb hf L (total lo hi) hR hR1).mpr
    exact ⟨hL,hend ▸ hH,hshape⟩

end Plank.PlanarParallelPositive

/-- info: 'Plank.PlanarParallelPositive.equality_iff_tiling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelPositive.equality_iff_tiling
