/- An actual support-preserving pruning retains every deficient-volume counterexample. -/
module

public import CoveredSetPruning
public import SupportPruningGeometry
public import ConvexMeasureRigidity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SupportPrunedGap

open Set MeasureTheory SupportPruningGeometry

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [BorelSpace E] in
/-- A strict counterexample has a positive-volume pruned representative with the same widths. -/
theorem exists_counterexample (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (U : Set E) (hU : MeasurableSet U) (f : ι → E →ᵃ[ℝ] ℝ)
    {q : ℝ} (hq : q≤1) (hbad : μ.real (K\U)<q*μ.real K) :
    ∃ (C : Set E) (P Q : ι → E),
      C=prune K U P Q ∧ IsCompact C ∧ Convex ℝ C ∧ C⊆K ∧
      0<μ.real C ∧ C∩U=K∩U ∧
      (∀ i, Body.width C (f i)=Body.width K (f i)) ∧
      prune C U P Q=C ∧ μ.real (C\U)<q*μ.real C := by
  obtain ⟨C,P,Q,hdef,hC,hCc,hCK,hcover,hw,hfix,_⟩ :=
    exists_support_pruning hK hconv hne U f (fun i => (f i).continuous_of_finiteDimensional)
  have hb := CoveredSetPruning.bad_transfer μ hK.measure_ne_top hCK hU hcover hq hbad
  have hpos : 0<μ.real C := by
    by_contra! hn
    have hz : μ.real C=0 := le_antisymm hn measureReal_nonneg
    rw [hz,mul_zero] at hb
    exact (not_lt_of_ge measureReal_nonneg) hb
  exact ⟨C,P,Q,hdef,hC,hCc,hCK,hpos,hcover,hw,hfix,hb⟩

/-- A proper pruning of a positive-volume convex body strictly improves every coefficient q<1. -/
theorem strict_descent_of_ne (μ : Measure E) [μ.IsAddHaarMeasure]
    {K C U : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0<μ.real K) (hC : IsCompact C) (hCK : C⊆K)
    (hU : MeasurableSet U) (hcover : C∩U=K∩U) (hne : C≠K)
    {q : ℝ} (hq : q<1) :
    μ.real (C\U)-q*μ.real C < μ.real (K\U)-q*μ.real K := by
  have hv : μ.real C<μ.real K := by
    apply lt_of_le_of_ne (measureReal_mono hCK hK.measure_ne_top)
    intro he
    apply hne
    exact ConvexMeasureRigidity.eq_of_full_measure μ hconv hC.isClosed hCK
      (ENNReal.toReal_pos_iff.mp hV).1 hK.measure_ne_top
      ((ENNReal.toReal_eq_toReal_iff' hC.measure_ne_top hK.measure_ne_top).mp he)
  exact CoveredSetPruning.strict_descent μ hK.measure_ne_top hCK hU hcover hq hv

end Plank.SupportPrunedGap

#print axioms Plank.SupportPrunedGap.exists_counterexample
#print axioms Plank.SupportPrunedGap.strict_descent_of_ne
