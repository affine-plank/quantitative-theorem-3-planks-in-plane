module
/-
# The finite Bang map and the volume of uncovered sets

The finite symmetric potential selects a measurable partition of seed space.
Translation of each piece into its exterior sign cell gives an injective map
preserving the measure of every measurable set. This is the finite Bang-map
step in Section 2 of Bakaev–Polyanskii, Optimal partial plank coverings.

The interface uses additive functionals and a symmetrizing positive weight;
Euclidean inner products are a client rather than a built-in restriction.
-/
public import Plank.Algebra.SymmetricSubset
public import Plank.Measure.FiniteTranslations
public import Plank.Measure.LinearBands
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Plank.BangMap

open Set MeasureTheory Function
open LinearBands

variable {E ι : Type*} [AddCommGroup E] [Fintype ι]

/-- Seeds for which every finite subset translation remains in the body.
Translating this set by half the total shift gives the usual symmetric
Minkowski difference by the finite Bang set. -/
def seed (K : Set E) (v : ι → E) : Set E :=
  {t | ∀ s : Finset ι, t + s.sum v ∈ K}

theorem exists_side_assignment (f : ι → E →+ ℝ) (lo hi : ι → ℝ)
    (v : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hself : ∀ i, f i (v i) = hi i - lo i)
    (hsym : ∀ i j, w i * f i (v j) = w j * f j (v i)) (t : E) :
    ∃ s : Finset ι, t + s.sum v ∈ weakCell (fun i => f i) lo hi s := by
  classical
  obtain ⟨s, hhigh, hlow⟩ := SymmetricSubset.exists_side_assignment w (fun i => f i t)
    lo hi (fun i j => f i (v j)) hw hself hsym
  refine ⟨s, ?_⟩
  intro i
  by_cases his : i ∈ s
  · simpa only [his, ↓reduceIte, map_add, map_sum] using hhigh i his
  · simpa only [his, ↓reduceIte, map_add, map_sum] using hlow i his

section Measurable

variable [MeasurableSpace E] [MeasurableAdd E]

theorem measurableSet_seed (K : Set E) (hK : MeasurableSet K) (v : ι → E) :
    MeasurableSet (seed K v) := by
  rw [seed, Set.ofPred_forall]
  exact MeasurableSet.iInter fun s => hK.preimage (measurable_add_const (s.sum v))

/-- The finite Bang map is measurable and injective, and preserves the measure
of images. Strictly positive band widths make the weak exterior cells disjoint.
Closed boundaries are dealt with separately using null level sets. -/
theorem exists_bang_map (μ : Measure E) [μ.IsAddRightInvariant]
    (f : ι → E →+ ℝ) (hf : ∀ i, Measurable (f i)) (lo hi : ι → ℝ)
    (hwidth : ∀ i, lo i < hi i) (v : ι → E) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hself : ∀ i, f i (v i) = hi i - lo i)
    (hsym : ∀ i j, w i * f i (v j) = w j * f j (v i)) :
    ∃ F : E → E, Measurable F ∧ Injective F ∧
      (∀ t, ∃ s : Finset ι,
        F t = t + s.sum v ∧ F t ∈ weakCell (fun i => f i) lo hi s) ∧
      (∀ T : Set E, MeasurableSet T → μ (F '' T) = μ T) := by
  classical
  let P (t : E) (s : Finset ι) :=
    SymmetricSubset.potential w (fun i => f i t) lo (fun i j => f i (v j)) s
  have hP (s : Finset ι) : Measurable (fun t => P t s) := by
    dsimp only [P, SymmetricSubset.potential, SymmetricSubset.score]
    fun_prop
  let M : Finset ι → Set E := fun s => {t | ∀ r, P t r ≤ P t s}
  have hM : ∀ s, MeasurableSet (M s) := by
    intro s
    change MeasurableSet {t | ∀ r, P t r ≤ P t s}
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun r => measurableSet_le (hP r) (hP s)
  have hcoverM : ∀ t, ∃ s, t ∈ M s := by
    intro t
    obtain ⟨s, _, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Finset ι)) (P t) Finset.univ_nonempty
    exact ⟨s, fun r => hmax r (Finset.mem_univ _)⟩
  have hcell : ∀ s t, t ∈ M s → t + s.sum v ∈ weakCell (fun i => f i) lo hi s := by
    intro s t ht
    obtain ⟨hhigh, hlow⟩ := SymmetricSubset.side_assignment_of_maximal
      w (fun i => f i t) lo hi (fun i j => f i (v j)) hw hself hsym s ht
    intro i
    by_cases his : i ∈ s
    · simpa only [his, ↓reduceIte, map_add, map_sum] using hhigh i his
    · simpa only [his, ↓reduceIte, map_add, map_sum] using hlow i his
  obtain ⟨A, hA, hdisA, hcoverA, hsub⟩ :=
    FiniteTranslations.exists_measurable_partition_subordinate M hM hcoverM
  obtain ⟨F, hmeasF, hF⟩ := FiniteTranslations.exists_measurable_translation_map
    A hA hdisA hcoverA (fun s => s.sum v)
  have himage : ∀ s, (fun t => t + s.sum v) '' A s ⊆ weakCell (fun i => f i) lo hi s := by
    rintro s _ ⟨t, ht, rfl⟩
    exact hcell s t (hsub s ht)
  have hdisImage : Pairwise (Disjoint on fun s => (fun t => t + s.sum v) '' A s) := by
    intro s r hsr
    exact (disjoint_weakCells (fun i => f i) lo hi hwidth hsr).mono (himage s) (himage r)
  have hinj : Injective F := FiniteTranslations.injective_of_disjoint_translations
    A hcoverA (fun s => s.sum v) F hF hdisImage
  refine ⟨F, hmeasF, hinj, ?_, ?_⟩
  · intro t
    obtain ⟨s, hs⟩ := hcoverA t
    exact ⟨s, hF s t hs, by rw [hF s t hs]; exact hcell s t (hsub s hs)⟩
  · intro T hT
    exact FiniteTranslations.measure_image_eq_of_finite_translations
      μ A hA hdisA hcoverA (fun s => s.sum v) F hF hinj T hT

/-- BP's finite Bang-set volume comparison, in subset-shift coordinates. -/
theorem measure_seed_le_open_gap (μ : Measure E) [μ.IsAddRightInvariant]
    (f : ι → E →+ ℝ) (hf : ∀ i, Measurable (f i)) (lo hi : ι → ℝ)
    (hwidth : ∀ i, lo i < hi i) (v : ι → E) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (hself : ∀ i, f i (v i) = hi i - lo i)
    (hsym : ∀ i j, w i * f i (v j) = w j * f j (v i))
    (K : Set E) (hK : MeasurableSet K) :
    μ (seed K v) ≤ μ (K \ ⋃ i, openBand (f i) (lo i) (hi i)) := by
  obtain ⟨F, _, _, hF, hμ⟩ := exists_bang_map μ f hf lo hi hwidth v w hw hself hsym
  rw [← hμ (seed K v) (measurableSet_seed K hK v)]
  apply measure_mono
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hcell⟩ := hF t
  exact ⟨by rw [hs]; exact ht s, weakCell_subset_gap (fun i => f i) lo hi s hcell⟩

/-- The volume comparison for closed bands, allowing zero widths. The null-level
hypotheses hold for every nonzero continuous linear functional in finite dimension. -/
theorem measure_core_le_closed_gap (μ : Measure E) [μ.IsAddRightInvariant]
    (f : ι → E →+ ℝ) (hf : ∀ i, Measurable (f i)) (lo hi : ι → ℝ)
    (hwidth : ∀ i, lo i ≤ hi i)
    (hlo : ∀ i, μ {x | f i x = lo i} = 0)
    (hhi : ∀ i, μ {x | f i x = hi i} = 0)
    (v : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hself : ∀ i, f i (v i) = hi i - lo i)
    (hsym : ∀ i j, w i * f i (v j) = w j * f j (v i))
    (K core : Set E) (hcore : MeasurableSet core) (hsub : core ⊆ seed K v) :
    μ core ≤ μ (K \ ⋃ i, closedBand (f i) (lo i) (hi i)) := by
  apply measure_le_closed_gap_of_translations μ (fun i => f i) hf lo hi hwidth hlo hhi
    core hcore (fun s => s.sum v)
  · intro t _
    exact exists_side_assignment f lo hi v w hw hself hsym t
  · intro s t ht
    exact hsub ht s

/-- The finite Bang-set comparison with closed plank boundaries and possibly
zero widths. Convexity is only needed later to construct a large seed set. -/
theorem measure_seed_le_closed_gap (μ : Measure E) [μ.IsAddRightInvariant]
    (f : ι → E →+ ℝ) (hf : ∀ i, Measurable (f i)) (lo hi : ι → ℝ)
    (hwidth : ∀ i, lo i ≤ hi i)
    (hlo : ∀ i, μ {x | f i x = lo i} = 0)
    (hhi : ∀ i, μ {x | f i x = hi i} = 0)
    (v : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hself : ∀ i, f i (v i) = hi i - lo i)
    (hsym : ∀ i j, w i * f i (v j) = w j * f j (v i))
    (K : Set E) (hK : MeasurableSet K) :
    μ (seed K v) ≤ μ (K \ ⋃ i, closedBand (f i) (lo i) (hi i)) :=
  measure_core_le_closed_gap μ f hf lo hi hwidth hlo hhi v w hw hself hsym
    K (seed K v) (measurableSet_seed K hK v) Subset.rfl

end Measurable

end Plank.BangMap
