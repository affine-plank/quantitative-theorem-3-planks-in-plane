/- Tight positive parallel windows merge into one interval. -/
module

public import Plank.Proofs.Quant.PlanarParallelGaps

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelInterval

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarParallelTranslations
  PlanarParallelGaps
open Plank.Convex.DeficientHeightTilt

variable {ι : Type*} [Fintype ι]

/-- With positive widths and endpoints in the support interval, equality
forces the union of all windows to equal its interval hull. -/
theorem union_eq_interval_of_equality {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (lo hi : ι → ℝ) (ho : ∀ i, lo i < hi i)
    (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hR : 0 < total lo hi) (hR1 : total lo hi < 1)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0)
    (he : (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
      (1-total lo hi)^2*(volume K).toReal)
    (iL iH : ι) (hL : ∀ i, lo iL ≤ lo i) (hH : ∀ i, hi i ≤ hi iH) :
    (⋃ i, Icc (lo i) (hi i)) = Icc (lo iL) (hi iH) := by
  classical
  apply Subset.antisymm
  · intro t ht
    obtain ⟨i,hi'⟩ := mem_iUnion.mp ht
    exact ⟨(hL i).trans hi'.1,hi'.2.trans (hH i)⟩
  · intro t ht
    by_contra hnot
    have hout (i) : t < lo i ∨ hi i < t := by
      by_cases hlow : t < lo i
      · exact Or.inl hlow
      · exact Or.inr (lt_of_not_ge (fun hhigh =>
          hnot (mem_iUnion.mpr ⟨i,le_of_not_gt hlow,hhigh⟩)))
    have hleft : hi iL < t := (hout iL).resolve_left (not_lt_of_ge ht.1)
    have hright : t < lo iH := (hout iH).resolve_right (not_lt_of_ge ht.2)
    let s := Finset.univ.filter (fun i => hi i < t)
    have hs (i) : i ∈ s ↔ hi i < t := by simp [s]
    have hil : iL ∈ s := (hs iL).mpr hleft
    have hih : iH ∉ s := fun hh =>
      (not_lt_of_ge ht.2) ((hs iH).mp hh)
    have hpos : 0 < selected lo hi s := by
      have hle : widths lo hi iL ≤ selected lo hi s :=
        Finset.single_le_sum (fun i _ => sub_nonneg.mpr (ho i).le) hil
      exact (sub_pos.mpr (ho iL)).trans_le hle
    have hless : selected lo hi s < total lo hi := by
      have hle := (selected_bounds lo hi (fun i => (ho i).le) (insert iH s)).2
      rw [selected,Finset.sum_insert hih] at hle
      have hp : 0 < widths lo hi iH := sub_pos.mpr (ho iH)
      change widths lo hi iH+selected lo hi s ≤ total lo hi at hle
      linarith only [hle,hp]
    have hext := gap_selected_extreme hK hconv hV lo hi (fun i => (ho i).le)
      hR hR1 f a b ha hb hfa hfb he t ((hlo iL).trans_lt ((ho iL).trans hleft))
      (hright.trans ((ho iH).trans_le (hhi iH))) hout s hs
    exact hext.elim hpos.ne' hless.ne

/-- Covering an interval spends at least its length in total window width. -/
theorem interval_length_le_total (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (L H : ℝ) (_hLH : L ≤ H) (hcover : Icc L H ⊆ ⋃ i, Icc (lo i) (hi i)) :
    H-L ≤ total lo hi := by
  have hh := (measure_mono hcover).trans (measure_iUnion_fintype_le volume (fun i => Icc (lo i) (hi i)))
  simp only [Real.volume_Icc] at hh
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (ho i))] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg
    (fun i _ => sub_nonneg.mpr (ho i)))).mp hh

/-- Equality forbids overlap after the windows have merged: the interval
hull has exactly the original total width. -/
theorem length_eq_total_of_equality {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i) (hR1 : total lo hi < 1)
    (f : Point →ᵃ[ℝ] ℝ) (hW : rangeWidth K f = 1)
    (he : (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
      (1-total lo hi)^2*(volume K).toReal)
    (L H : ℝ) (hLH : L ≤ H) (hunion : (⋃ i, Icc (lo i) (hi i)) = Icc L H) :
    H-L = total lo hi := by
  have hle := interval_length_le_total lo hi ho L H hLH hunion.symm.subset
  have hband : (⋃ i, LinearBands.closedBand f (lo i) (hi i)) =
      {x | L ≤ f x ∧ f x ≤ H} := by
    ext x
    rw [mem_iUnion]
    change (∃ i, f x ∈ Icc (lo i) (hi i)) ↔ f x ∈ Icc L H
    rw [← mem_iUnion, hunion]
  have hne : K.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn,measure_empty,ENNReal.toReal_zero] at hV
    exact lt_irrefl 0 hV
  have hlower := PlanarOnePlank.uncovered_area_lower_bound hK hconv hne f L H hLH
    (by rw [hW]; norm_num)
  rw [hW,div_one,← hband,he,max_eq_right (by linarith only [hle,hR1])] at hlower
  have hsq := (mul_le_mul_iff_left₀ hV).mp hlower
  have hlin := (sq_le_sq₀ (by linarith only [hle,hR1]) (by linarith only [hR1])).mp hsq
  linarith only [hle,hlin]

end Plank.PlanarParallelInterval

/-- info: 'Plank.PlanarParallelInterval.union_eq_interval_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelInterval.union_eq_interval_of_equality
/-- info: 'Plank.PlanarParallelInterval.length_eq_total_of_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelInterval.length_eq_total_of_equality
