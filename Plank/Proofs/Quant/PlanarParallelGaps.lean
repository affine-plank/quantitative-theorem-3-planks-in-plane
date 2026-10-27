/- A tight collection of parallel planks has no gap with positive-width
planks on both sides. This is a geometric necessity, on arbitrary bodies. -/
module

public import Plank.Proofs.Quant.PlanarParallelTranslations

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarParallelGaps

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarOnePlankShape
  PlanarParallelSections PlanarParallelTranslations
open scoped Pointwise

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Every gap level has a unique weak side assignment. -/
theorem weakCell_unique (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (f : Point →ᵃ[ℝ] ℝ) (t : ℝ) (ht : ∀ i, t < lo i ∨ hi i < t)
    (s : Finset ι) (hs : ∀ i, i ∈ s ↔ hi i < t)
    (u : Finset ι) (x : Point) (hfx : f x = t)
    (hx : x ∈ LinearBands.weakCell (fun _ : ι => f) lo hi u) : u = s := by
  classical
  apply Finset.ext
  intro i
  rw [hs]
  have hh := hx i
  by_cases hiu : i ∈ u
  · simp only [hiu,↓reduceIte,hfx] at hh
    exact iff_of_true hiu ((ht i).resolve_left (not_lt_of_ge ((ho i).trans hh)))
  · simp only [hiu,↓reduceIte,hfx] at hh
    exact iff_of_false hiu (not_lt_of_ge (hh.trans (ho i)))

/-- At an uncovered level, the closed equality cover uses one homothetic
copy, so it must contain the entire section of the original body. -/
theorem section_subset_copy_of_closedCover {K : Set Point}
    (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i) (hR : total lo hi ≠ 0)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (t : ℝ)
    (ht : ∀ i, t < lo i ∨ hi i < t) (s : Finset ι)
    (hs : ∀ i, i ∈ s ↔ hi i < t) (hcover : K ⊆ closedCover K lo hi f a b) :
    levelSection K f t ⊆ homotheticCopy K (1-total lo hi) (center lo hi a b s) := by
  intro x hx
  rcases hcover hx.1 with hband | hpiece
  · obtain ⟨i,hbi⟩ := mem_iUnion.mp hband
    change lo i ≤ f x ∧ f x ≤ hi i at hbi
    rw [hx.2] at hbi
    exact ((ht i).elim (fun hh => (not_lt_of_ge hbi.1 hh))
      (fun hh => (not_lt_of_ge hbi.2 hh))).elim
  · obtain ⟨u,hu⟩ := mem_iUnion.mp hpiece
    have hus := weakCell_unique lo hi ho f t ht s hs u x hx.2 hu.2
    subst u
    obtain ⟨y,hy,he⟩ := hu.1
    refine ⟨y,hy,?_⟩
    change (1-total lo hi) • y = x-translations lo hi a b s at he
    change (1-total lo hi) • y+(1-(1-total lo hi)) • center lo hi a b s = x
    rw [sub_sub_cancel,he,← translations_eq lo hi a b s hR]
    exact sub_add_cancel x _

/-- Under equality, a gap level has either no positive width below it or
all positive width below it. An internal split is impossible. -/
theorem gap_selected_extreme {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR : 0 < total lo hi) (hR1 : total lo hi < 1)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0)
    (he : (volume (K \ ⋃ i, LinearBands.closedBand f (lo i) (hi i))).toReal =
      (1-total lo hi)^2*(volume K).toReal)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (ht : ∀ i, t < lo i ∨ hi i < t)
    (s : Finset ι) (hs : ∀ i, i ∈ s ↔ hi i < t) :
    selected lo hi s = 0 ∨ selected lo hi s = total lo hi := by
  have hbounds := selected_bounds lo hi ho s
  by_contra hbad
  push Not at hbad
  have hp : 0 < selected lo hi s := lt_of_le_of_ne hbounds.1 (Ne.symm hbad.1)
  have hp1 : selected lo hi s < total lo hi := lt_of_le_of_ne hbounds.2 hbad.2
  have hc := equality_implies_closedCover hK hconv hV lo hi ho hR hR1 f a b ha hb hfa hfb he
  obtain ⟨x,hx,hfx⟩ := exists_interior_level hK hconv hV f a b ha hb hfa hfb ht0 ht1
  apply not_section_subset_copy hK hconv hV f a b ha hb hfa hfb
    (sub_pos.mpr hR1) (by linarith only [hR]) (center lo hi a b s)
    (by rw [center_level lo hi f a b hfa hfb]; exact div_pos hp hR)
    (by rw [center_level lo hi f a b hfa hfb]; exact (div_lt_one hR).mpr hp1)
    t ⟨x,interior_subset hx,hfx⟩
  exact section_subset_copy_of_closedCover lo hi ho hR.ne' f a b t ht s hs hc

end Plank.PlanarParallelGaps

/-- info: 'Plank.PlanarParallelGaps.gap_selected_extreme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarParallelGaps.gap_selected_extreme
