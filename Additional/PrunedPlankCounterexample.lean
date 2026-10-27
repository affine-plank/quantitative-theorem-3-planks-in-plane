/- Every quantitative counterexample has at most twice the plank count uncovered extreme points. -/
module

public import SupportPrunedGap
public import PrunedPlankExtremes

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PrunedPlankCounterexample

open Set MeasureTheory SupportPruningGeometry
open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def covered (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) : Set E :=
  ⋃ i, {x | lo i≤f i x ∧ f i x≤hi i}

def budget (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) : ℝ :=
  ∑ i, (hi i-lo i)/Body.width K (f i)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An actual strict quantitative counterexample can be pruned without changing any plank width.
The resulting convex body has positive volume and at most 2n uncovered extreme points.
This is a reduction, not a proof that such a counterexample exists or is impossible. -/
theorem exists_pruned (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i, lo i≤hi i)
    (hW : ∀ i, 0<Body.width K (f i)) (d : ℕ) {B : ℝ} (hB : B≤1)
    (hbad : μ.real (K\covered f lo hi)<(max 0 (B-budget K f lo hi))^d*μ.real K) :
    ∃ (C : Set E) (P Q : ι → E),
      IsCompact C ∧ Convex ℝ C ∧ C⊆K ∧ 0<μ.real C ∧
      (∀ i, P i∈C ∧ Q i∈C ∧
        (∀ x∈C, f i x≤f i (P i)) ∧ (∀ x∈C, f i (Q i)≤f i x)) ∧
      (∀ i, Body.width C (f i)=Body.width K (f i)) ∧
      C∩covered f lo hi=K∩covered f lo hi ∧
      C=convexHull ℝ ((C∩covered f lo hi)∪range P∪range Q) ∧
      C.extremePoints ℝ\covered f lo hi⊆range P∪range Q ∧
      (C.extremePoints ℝ\covered f lo hi).ncard≤2*Fintype.card ι ∧
      μ.real (C\covered f lo hi)<(max 0 (B-budget C f lo hi))^d*μ.real C := by
  let S : ι → Set E := fun i => {x | lo i≤f i x ∧ f i x≤hi i}
  have hS (i) : IsClosed (S i) :=
    (isClosed_le continuous_const (f i).continuous_of_finiteDimensional).inter
      (isClosed_le (f i).continuous_of_finiteDimensional continuous_const)
  have hSc (i) : Convex ℝ (S i) := (convex_Icc (lo i) (hi i)).affine_preimage (f i)
  have hU : MeasurableSet (covered f lo hi) := (isClosed_iUnion_of_finite hS).measurableSet
  have hR : 0≤budget K f lo hi :=
    Finset.sum_nonneg (fun i _ => div_nonneg (sub_nonneg.mpr (horder i)) (hW i).le)
  have hmax : max 0 (B-budget K f lo hi)≤1 :=
    max_le zero_le_one (by linarith only [hB,hR])
  have hq : (max 0 (B-budget K f lo hi))^d≤1 :=
    pow_le_one₀ (le_max_left _ _) hmax
  obtain ⟨C,P,Q,hdef,hC,hCc,hCK,hcover,hw,hfix,_,_,hmaxC,hminC⟩ :=
    exists_support_pruning hK hconv hne (covered f lo hi) f
      (fun i => (f i).continuous_of_finiteDimensional)
  have hbadC := CoveredSetPruning.bad_transfer μ hK.measure_ne_top hCK hU hcover hq hbad
  have hV : 0<μ.real C := by
    by_contra! hn
    have hz : μ.real C=0 := le_antisymm hn measureReal_nonneg
    rw [hz,mul_zero] at hbadC
    exact (not_lt_of_ge measureReal_nonneg) hbadC
  have hsupports (i) : P i∈C ∧ Q i∈C ∧
      (∀ x∈C, f i x≤f i (P i)) ∧ (∀ x∈C, f i (Q i)≤f i x) := by
    refine ⟨?_,?_,fun x hx => hmaxC i x (hCK hx),fun x hx => hminC i x (hCK hx)⟩
    · rw [hdef]
      exact pointP_mem_prune _ _ _ _ _
    · rw [hdef]
      exact pointQ_mem_prune _ _ _ _ _
  have hhull : C=convexHull ℝ ((C∩covered f lo hi)∪range P∪range Q) :=
    hfix.symm.trans (PrunedPlankExtremes.prune_eq_hull hC hCc S hS hSc P Q)
  have hext : C.extremePoints ℝ\covered f lo hi⊆range P∪range Q := by
    rw [hdef]
    exact PrunedPlankExtremes.uncovered_extremes_subset hK hconv S hS hSc P Q
  have hrange (p : ι → E) : (range p).ncard≤Fintype.card ι := by
    simpa only [image_univ,ncard_univ,Nat.card_eq_fintype_card] using
      (ncard_image_le (f := p) (s := (univ : Set ι)))
  have hcount : (C.extremePoints ℝ\covered f lo hi).ncard≤2*Fintype.card ι := by
    calc
      _ ≤ (range P∪range Q).ncard := ncard_le_ncard hext
      _ ≤ (range P).ncard+(range Q).ncard := ncard_union_le _ _
      _ ≤ Fintype.card ι+Fintype.card ι := add_le_add (hrange P) (hrange Q)
      _ = 2*Fintype.card ι := (two_mul _).symm
  have hb : budget C f lo hi=budget K f lo hi := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hw i]
  refine ⟨C,P,Q,hC,hCc,hCK,hV,hsupports,hw,hcover,hhull,hext,hcount,?_⟩
  rw [hb]
  exact hbadC

end Plank.PrunedPlankCounterexample

#print axioms Plank.PrunedPlankCounterexample.exists_pruned
