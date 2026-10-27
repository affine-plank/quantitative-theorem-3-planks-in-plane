/- A closed full-measure subset of a positive-measure convex set is the whole set. -/
module

public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section
set_option autoImplicit false

namespace Plank.ConvexMeasureRigidity

open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem eq_of_full_measure (μ : Measure E) [μ.IsAddHaarMeasure] {K Q : Set E}
    (hconv : Convex ℝ K) (hQ : IsClosed Q) (hQK : Q⊆K)
    (hpos : 0<μ K) (hfin : μ K≠⊤) (harea : μ Q=μ K) : Q=K := by
  have hInt : (interior K).Nonempty := by
    by_contra hn
    have he : interior K=∅ := not_nonempty_iff_eq_empty.mp hn
    have hs : K⊆frontier K := by rw [frontier,he,sdiff_empty]; exact subset_closure
    exact hpos.ne' (measure_mono_null hs (hconv.addHaar_frontier μ))
  have hd : μ (K\Q)=0 := by
    rw [measure_sdiff hQK hQ.measurableSet.nullMeasurableSet (by rw [harea]; exact hfin),
      harea,tsub_self]
  have hi : interior K⊆Q := by
    apply sdiff_eq_empty.mp
    have ho : IsOpen (interior K\Q) := isOpen_interior.inter hQ.isOpen_compl
    exact ho.eq_empty_of_measure_zero
      (measure_mono_null (sdiff_subset_sdiff_left interior_subset) hd)
  apply Subset.antisymm hQK
  calc
    K ⊆ closure K := subset_closure
    _ = closure (interior K) := (hconv.closure_interior_eq_closure_of_nonempty_interior hInt).symm
    _ ⊆ Q := closure_minimal hi hQ

end Plank.ConvexMeasureRigidity

#print axioms Plank.ConvexMeasureRigidity.eq_of_full_measure
