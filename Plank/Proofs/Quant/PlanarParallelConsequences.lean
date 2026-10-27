/- Explicit geometric consequences of the parallel classification. -/
module

public import Plank.Proofs.Quant.PlanarParallelClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelClassification

open Set MeasureTheory PlanarQuantitative PlanarParallelTranslations
  PlanarParallelActive PlanarOnePlankVertices

/-- The width identity in the tiling description really forbids every
positive overlap: two distinct active windows have disjoint interiors. -/
theorem Tiling.separated {ι : Type*} [Fintype ι] {K : Set Point} {lo hi : ι → ℝ}
    (ho : ∀ i, lo i ≤ hi i) {f : Point →ᵃ[ℝ] ℝ} {a b : Point}
    (ht : Tiling K lo hi f a b) (i j : Active lo hi) (hne : i ≠ j) :
    hi i.1 ≤ lo j.1 ∨ hi j.1 ≤ lo i.1 := by
  classical
  obtain ⟨L,H,_,_,_,hu,hlen,_⟩ := ht
  have he : volume (⋃ i : Active lo hi, Icc (lo i.1) (hi i.1)) =
      ∑ i : Active lo hi, volume (Icc (lo i.1) (hi i.1)) := by
    rw [hu,Real.volume_Icc,hlen,← total_active lo hi ho]
    simp only [total,widths,Real.volume_Icc]
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr i.2.le)
  have hpair := (Quant.TranslationEquality.union_measure_eq_sum_iff volume
    (fun i : Active lo hi => Icc (lo i.1) (hi i.1)) (fun _ => measurableSet_Icc)
    (fun _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).mp he
  have hz : volume (Icc (lo i.1) (hi i.1) ∩ Icc (lo j.1) (hi j.1)) = 0 := hpair hne
  rw [Icc_inter_Icc,Real.volume_Icc,ENNReal.ofReal_eq_zero] at hz
  have hle := sub_nonpos.mp hz
  rcases le_total (lo i.1) (lo j.1) with hl | hl
  · rw [max_eq_right hl] at hle
    rcases min_le_iff.mp hle with hh | hh
    · exact Or.inl hh
    · exact (not_lt_of_ge hh j.2).elim
  · rw [max_eq_left hl] at hle
    rcases min_le_iff.mp hle with hh | hh
    · exact (not_lt_of_ge hh i.2).elim
    · exact Or.inr hh

/-- No convex body requiring more than four vertices can be tight for
parallel planks with total positive relative width strictly below one. -/
theorem equality_implies_four_vertices {ι : Type*} [Fintype ι] {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR : 0 < total lo hi) (hR1 : total lo hi < 1)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0) (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (he : (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
      (1-total lo hi)^2*(volume K).toReal) :
    ∃ c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨_,_,_,_,_,_,_,c,_,d,_,_,_,hshape⟩ :=
    (equality_iff_tiling hK hconv hV lo hi ho hR hR1 f a b ha hb hfa hfb hf).mp he
  exact ⟨c,d,hshape.trans (fourPointBody_eq_hull a b c d (by rwa [← hshape]))⟩

end Plank.PlanarParallelClassification

/-- info: 'Plank.PlanarParallelClassification.Tiling.separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelClassification.Tiling.separated
/-- info: 'Plank.PlanarParallelClassification.equality_implies_four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelClassification.equality_implies_four_vertices
