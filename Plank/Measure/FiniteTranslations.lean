module
/-
# Finite families of translations and measure

Measurable finite covers admit disjoint measurable refinements. A map which is
a translation on each piece is measurable, and preserves the measure of every
measurable set when it is injective. Disjoint target cells also give a direct
measure lower bound without choosing a piecewise map.
-/
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

noncomputable section

namespace Plank.FiniteTranslations

open Set MeasureTheory Function

variable {ι E : Type*}

/-- Refine a finite measurable cover to a measurable partition, allowing empty
pieces. The index set is unchanged. -/
theorem exists_measurable_partition_subordinate [Fintype ι] [MeasurableSpace E]
    (C : ι → Set E) (hC : ∀ i, MeasurableSet (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i) :
    ∃ A : ι → Set E,
      (∀ i, MeasurableSet (A i)) ∧ Pairwise (Disjoint on A) ∧
      (∀ x, ∃ i, x ∈ A i) ∧ (∀ i, A i ⊆ C i) := by
  classical
  let e := Fintype.equivFin ι
  let D : Fin (Fintype.card ι) → Set E := fun i => C (e.symm i)
  let A : ι → Set E := fun i => disjointed D (e i)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro i
    exact disjointedRec (f := D) (fun _ j ht => ht.diff (hC (e.symm j)))
      (hC (e.symm (e i)))
  · intro i j hij
    exact disjoint_disjointed D (e.injective.ne hij)
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    have hx : x ∈ ⋃ j, D j := mem_iUnion.mpr ⟨e i, by simpa [D] using hi⟩
    rw [← iUnion_disjointed] at hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact ⟨e.symm j, by simpa [A] using hj⟩
  · intro i
    simpa [A, D] using disjointed_subset D (e i)

section AddGroup

variable [AddGroup E] [MeasurableSpace E] [MeasurableAdd E]

/-- A function agreeing with translations on a finite measurable cover is
measurable. Disjointness of the source pieces is unnecessary for this step. -/
theorem measurable_of_finite_translations [Fintype ι]
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ x, ∃ i, x ∈ A i) (v : ι → E) (F : E → E)
    (hF : ∀ i x, x ∈ A i → F x = x + v i) : Measurable F := by
  intro T hT
  have hpre : F ⁻¹' T = ⋃ i, A i ∩ (fun x => x + v i) ⁻¹' T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hcover x
      exact mem_iUnion.mpr ⟨i, hi, by simpa [← hF i x hi] using hx⟩
    · intro hx
      obtain ⟨i, hi, hx⟩ := mem_iUnion.mp hx
      simpa [hF i x hi] using hx
  rw [hpre]
  exact MeasurableSet.iUnion fun i => (hA i).inter (hT.preimage (measurable_add_const _))

omit [MeasurableSpace E] [MeasurableAdd E] in
/-- Distinct image cells prevent collisions between pieces; a translation
itself prevents collisions within each piece. -/
theorem injective_of_disjoint_translations
    (A : ι → Set E) (hcover : ∀ x, ∃ i, x ∈ A i)
    (v : ι → E) (F : E → E)
    (hF : ∀ i x, x ∈ A i → F x = x + v i)
    (hdis : Pairwise (Disjoint on fun i => (fun x => x + v i) '' A i)) :
    Injective F := by
  intro x y hxy
  obtain ⟨i, hi⟩ := hcover x
  obtain ⟨j, hj⟩ := hcover y
  have hij : i = j := by
    by_contra hne
    exact (Set.disjoint_left.mp (hdis hne))
      ⟨x, hi, (hF i x hi).symm⟩ ⟨y, hj, (hF j y hj).symm.trans hxy.symm⟩
  subst j
  exact add_right_cancel ((hF i x hi).symm.trans (hxy.trans (hF i y hj)))

/-- Construct a measurable translation map on a finite measurable partition.
Empty pieces are permitted. -/
theorem exists_measurable_translation_map [Fintype ι]
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise (Disjoint on A)) (hcover : ∀ x, ∃ i, x ∈ A i)
    (v : ι → E) :
    ∃ F : E → E, Measurable F ∧ (∀ i x, x ∈ A i → F x = x + v i) := by
  classical
  let F : E → E := fun x => x + v (hcover x).choose
  have hF : ∀ i x, x ∈ A i → F x = x + v i := by
    intro i x hi
    have heq : (hcover x).choose = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdis hne) (hcover x).choose_spec hi
    simp [F, heq]
  exact ⟨F, measurable_of_finite_translations A hA hcover v F hF, hF⟩

variable (μ : Measure E) [μ.IsAddRightInvariant]

/-- A translated measurable seed can be assigned to disjoint measurable cells
inside a target, giving a lower bound for the target measure. -/
theorem measure_le_of_translations [Fintype ι]
    (core : Set E) (hcore : MeasurableSet core) (v : ι → E)
    (C : ι → Set E) (hC : ∀ i, MeasurableSet (C i))
    (hdis : Pairwise (Disjoint on C)) (target : Set E)
    (hassign : ∀ x ∈ core, ∃ i, x + v i ∈ C i)
    (hinside : ∀ i x, x ∈ core → x + v i ∈ C i → x + v i ∈ target) :
    μ core ≤ μ target := by
  classical
  let B : ι → Set E := fun i => (fun x => x - v i) ⁻¹' core ∩ C i
  let A : ι → Set E := fun i => (fun x => x + v i) ⁻¹' B i
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    have hsub : Measurable (fun x : E => x - v i) := by
      simpa only [sub_eq_add_neg] using measurable_add_const (-v i)
    exact (hcore.preimage hsub).inter (hC i)
  have hdisB : Pairwise (Disjoint on B) := by
    intro i j hij
    exact (hdis hij).mono inter_subset_right inter_subset_right
  have hcover : core ⊆ ⋃ i, A i := by
    intro x hx
    obtain ⟨i, hi⟩ := hassign x hx
    exact mem_iUnion.mpr ⟨i, by simpa [A, B] using And.intro hx hi⟩
  have himage : (⋃ i, B i) ⊆ target := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    simpa using hinside i (x - v i) hi.1 (by simpa using hi.2)
  calc
    μ core ≤ μ (⋃ i, A i) := measure_mono hcover
    _ ≤ ∑ i, μ (A i) := measure_iUnion_fintype_le μ A
    _ = ∑ i, μ (B i) := by
      exact Finset.sum_congr rfl fun i _ => measure_preimage_add_right μ (v i) (B i)
    _ = μ (⋃ i, B i) := by rw [measure_iUnion hdisB hB, tsum_fintype]
    _ ≤ μ target := measure_mono himage

/-- An injective map which translates each piece of a finite measurable
partition preserves the measure of every measurable set, including infinite
measure. Surjectivity onto the ambient space is not required. -/
theorem measure_image_eq_of_finite_translations [Fintype ι]
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdis : Pairwise (Disjoint on A)) (hcover : ∀ x, ∃ i, x ∈ A i)
    (v : ι → E) (F : E → E)
    (hF : ∀ i x, x ∈ A i → F x = x + v i) (hinj : Injective F)
    (T : Set E) (hT : MeasurableSet T) : μ (F '' T) = μ T := by
  classical
  let B : ι → Set E := fun i => A i ∩ T
  have hB : ∀ i, MeasurableSet (B i) := fun i => (hA i).inter hT
  have hdisB : Pairwise (Disjoint on B) := by
    intro i j hij
    exact (hdis hij).mono inter_subset_left inter_subset_left
  have hcoverB : (⋃ i, B i) = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact hi.2
    · intro hx
      obtain ⟨i, hi⟩ := hcover x
      exact mem_iUnion.mpr ⟨i, hi, hx⟩
  have himage : ∀ i, F '' B i = (fun x => x + v i) '' B i := by
    intro i
    exact Set.image_congr fun x hx => hF i x hx.1
  have hmeas : ∀ i, MeasurableSet (F '' B i) := by
    intro i
    rw [himage i]
    exact (measurableEmbedding_addRight (v i)).measurableSet_image' (hB i)
  have hdisImage : Pairwise (Disjoint on fun i => F '' B i) := by
    intro i j hij
    exact Set.disjoint_image_of_injective hinj (hdisB hij)
  have hmeasure : ∀ i, μ (F '' B i) = μ (B i) := by
    intro i
    rw [himage i]
    change μ ((MeasurableEquiv.addRight (v i)) '' B i) = μ (B i)
    rw [MeasurableEquiv.image_eq_preimage_symm]
    exact measure_preimage_add_right μ (-v i) (B i)
  calc
    μ (F '' T) = μ (⋃ i, F '' B i) := by rw [← image_iUnion, hcoverB]
    _ = ∑ i, μ (F '' B i) := by rw [measure_iUnion hdisImage hmeas, tsum_fintype]
    _ = ∑ i, μ (B i) := Finset.sum_congr rfl fun i _ => hmeasure i
    _ = μ (⋃ i, B i) := by rw [measure_iUnion hdisB hB, tsum_fintype]
    _ = μ T := by rw [hcoverB]

end AddGroup

end Plank.FiniteTranslations
