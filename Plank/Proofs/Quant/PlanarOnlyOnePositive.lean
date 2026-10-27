/- Remove any number of null planks in the one-positive-width equality stratum. -/
module

public import Plank.Proofs.Quant.PlanarSingleActivePlank
public import Plank.Proofs.Quant.PlanarParameterDomain

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOnlyOnePositive

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Null planks at arbitrary positions and directions do not change the
actual gap or budget of the sole positive plank. -/
theorem gap_and_budget {m : ℕ} {K : Set Point} (hne : K.Nonempty)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (j : Fin m)
    (hz : ∀ i, i ≠ j → p.1 i = p.2 i) :
    gapArea K f p = (volume (K \ {x | p.1 j ≤ f j x ∧ f j x ≤ p.2 j})).toReal ∧
    budget K f p = (p.2 j-p.1 j)/rangeWidth K (f j) := by
  classical
  constructor
  · let bad : Set Point := ⋃ i : {i : Fin m // i ≠ j},
      {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}
    have hbad : volume bad = 0 := by
      apply measure_iUnion_null
      intro i
      rw [← hz i i.property]
      exact PlanarSingleActivePlank.volume_band_zero hne (f i) (hW i) _
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hbad] with x hx
    apply propext
    constructor
    · rintro ⟨hK,hp⟩
      exact ⟨hK,fun h => hp (mem_iUnion.mpr ⟨j,h⟩)⟩
    · rintro ⟨hK,hp⟩
      refine ⟨hK,?_⟩
      intro hu
      obtain ⟨i,hi⟩ := mem_iUnion.mp hu
      by_cases he : i = j
      · exact hp (he ▸ hi)
      · exact hx (mem_iUnion.mpr ⟨⟨i,he⟩,hi⟩)
  · apply Finset.sum_eq_single j
    · intro i _ hij
      rw [hz i hij,sub_self,zero_div]
    · simp

/-- The four-vertex consequence is independent of the number and indexing
of the null planks. The area equality is for the actual original union. -/
theorem equality_implies_four_vertices {m : ℕ} {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (p : Endpoints m)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (j : Fin m) (hj : p.1 j < p.2 j)
    (hz : ∀ i, i ≠ j → p.1 i = p.2 i) (hR : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨hg,hb⟩ := gap_and_budget hne f p hW j hz
  rw [hg,hb] at heq
  rw [hb] at hR
  exact PlanarOnePlankClassification.equality_implies_four_vertices hK hconv hne hV
    (f j) (p.1 j) (p.2 j) hj (hW j) hR heq

/-- A tight two-plank configuration with a zero-width member and positive
total width has a body with at most four vertices. -/
theorem two_of_zero_window {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 2)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, p.1 i ≤ p.2 i)
    (hz : ∃ i, p.1 i = p.2 i) (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  have honly (i j : Fin 2) (hij : i ≠ j) (he : p.1 i = p.2 i) :
      p.1 j < p.2 j := by
    by_contra h
    have hj : p.1 j = p.2 j := le_antisymm (ho j) (le_of_not_gt h)
    have hall : ∀ k : Fin 2, p.1 k = p.2 k := by
      intro k
      fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
    have hb : budget K f p = 0 := by simp [budget,hall]
    exact (lt_irrefl 0) (hb ▸ hR0)
  obtain ⟨i,hi⟩ := hz
  fin_cases i
  · apply equality_implies_four_vertices hK hconv hne hV f p hW 1
      (honly 0 1 (by decide) hi) _ hR1 heq
    intro i h
    fin_cases i
    · exact hi
    · exact (h rfl).elim
  · apply equality_implies_four_vertices hK hconv hne hV f p hW 0
      (honly 1 0 (by decide) hi) _ hR1 heq
    intro i h
    fin_cases i
    · exact (h rfl).elim
    · exact hi

end Plank.PlanarOnlyOnePositive

/-- info: 'Plank.PlanarOnlyOnePositive.two_of_zero_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnlyOnePositive.two_of_zero_window
