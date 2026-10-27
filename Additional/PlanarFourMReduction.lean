/- A planar quantitative counterexample has a polygonal representative with
at most four times as many vertices as planks. -/
module

public import Plank.Proofs.Quant.IrredundantHalfspaces
public import Plank.Proofs.Quant.PlanarStripVertices
public import PhysicalFacetVariation
public import GlobalPlankBoundaryMinimum
public import ActivePlankRestriction
public import PlanarGlobalPositivePolygon
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.Set.Card.Arithmetic

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarFourMReduction

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum

variable {E ι η : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- In dimension two, a nonconstant affine form is a first coordinate. -/
theorem exists_plank_chart (hdim : Module.finrank ℝ E = 2)
    (f : E →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) :
    ∃ A : PlanarStripVertices.Plane ≃ₗ[ℝ] E, ∀ x, f (A x) = x.1 + f 0 := by
  obtain ⟨v, hv⟩ := FiniteDimensionalCutCoordinates.exists_unit_vector f.linear hf
  have hdker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hd : Module.finrank ℝ ℝ = Module.finrank ℝ f.linear.ker := by
    rw [Module.finrank_self, hdim] at *
    omega
  let V : ℝ ≃ₗ[ℝ] f.linear.ker := LinearEquiv.ofFinrankEq ℝ f.linear.ker hd
  let A := (LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ) V).trans
    (FiniteDimensionalCutCoordinates.split f.linear v hv)
  refine ⟨A, ?_⟩
  intro x
  exact FiniteDimensionalCutCoordinates.affine_split f v hv (x.1, V x.2)

variable [Fintype ι] [MeasurableSpace E] [BorelSpace E]

/-- Move every null window to level two. This changes neither the budget
nor the gap measure, and keeps the same indexed family. -/
theorem move_null_windows (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ) (hf : ∀ i, (f i).linear ≠ 0)
    (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i) :
    ∃ a b : ι → ℝ, (∀ i, a i ≤ b i) ∧
      budget K f a b = budget K f lo hi ∧
      μ.real (K \ covered f a b) = μ.real (K \ covered f lo hi) ∧
      ∀ i, (lo i < hi i ∧ a i = lo i ∧ b i = hi i) ∨ (a i = 2 ∧ b i = 2) := by
  classical
  let a (i) := if lo i < hi i then lo i else 2
  let b (i) := if lo i < hi i then hi i else 2
  have ha : (fun i : {i // lo i < hi i} => a i) = fun i => lo i.val := by
    funext i
    simp [a, i.property]
  have hb : (fun i : {i // lo i < hi i} => b i) = fun i => hi i.val := by
    funext i
    simp [b, i.property]
  have hgap := ActivePlankRestriction.gap_restrict_to μ (fun i => lo i < hi i)
    K f a b hf (by intro i hi'; simp [a, b, hi'])
  rw [ha, hb] at hgap
  refine ⟨a, b, ?_, ?_, hgap.symm.trans
    (ActivePlankRestriction.gap_restrict μ K f lo hi hf), ?_⟩
  · intro i
    by_cases h : lo i < hi i <;> simp [a, b, h, ho i]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : lo i < hi i
    · simp [a, b, h]
    · have he : hi i = lo i := le_antisymm (le_of_not_gt h) (ho i)
      simp [a, b, he]
  · intro i
    by_cases h : lo i < hi i
    · exact Or.inl ⟨h, by simp [a, h], by simp [b, h]⟩
    · exact Or.inr ⟨by simp [a, h], by simp [b, h]⟩

/-- A facet cannot be fully covered when each indexed window is either
strictly interior in its direction or wholly above the body. -/
theorem no_fully_covered_facet (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K)
    (g : E →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    {κ : Type*} [Fintype κ] (H : κ → E →ᵃ[ℝ] ℝ) (c : κ → ℝ) (b : ℝ)
    (hrep : K = {x | g x ≤ b ∧ ∀ j, H j x ≤ c j})
    (p : E) (hp : g p = b) (hstrict : ∀ j, H j p < c j)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hV : 0 < μ.real K) (hW : ∀ i, 0 < Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi ≤ B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0 < μ.real (K \ covered f lo hi))
    (hends : ∀ i, (∀ x ∈ K, f i x < lo i ∧ f i x < hi i) ∨
      ((∃ x ∈ K, f i x < lo i) ∧ (∃ y ∈ K, hi i < f i y))) :
    ¬∀ x ∈ K, g x = b → x ∈ covered f lo hi := by
  intro hcover
  have hpK : p ∈ K := by rw [hrep]; exact ⟨hp.le, fun j => (hstrict j).le⟩
  have hside : ∀ x ∈ K, g x ≤ b := by intro x hx; rw [hrep] at hx; exact hx.1
  obtain ⟨i, hlevel⟩ := PhysicalFacetVariation.exists_coincident_boundary
    μ hK g hg H c b hrep p hp hstrict f lo hi ho hV hW d hbudget hglobal hgap hcover
  have hfi := AffineLevelCoincidence.linear_ne_zero_of_width_pos hK ⟨p, hpK⟩ (f i) (hW i)
  have hcontr (u : ℝ) (hu : u = lo i ∨ u = hi i)
      (hlev : ∀ x, g x = b → f i x = u) : False := by
    have hpu := hlev p hp
    rcases hends i with hout | ⟨⟨x, hx, hxl⟩, ⟨y, hy, hhy⟩⟩
    · have hh := hout p hpK
      rcases hu with rfl | rfl <;> linarith [hh.1, hh.2]
    · have hs := (PhysicalFacetVariation.support_of_level g (f i) hg hfi b u hlev p hp hside).1
      rcases hs with hmax | hmin
      · have hh : f i y ≤ f i p := hmax hy
        rcases hu with rfl | rfl <;> linarith [ho i]
      · have hh : f i p ≤ f i x := hmin hx
        rcases hu with rfl | rfl <;> linarith [ho i]
  rcases hlevel with hl | hh
  · exact hcontr (lo i) (Or.inl rfl) hl
  · exact hcontr (hi i) (Or.inr rfl) hh

/-- A polygonal negative minimum with interior or disjoint windows has at
most 2m covered and 2m uncovered extreme points. -/
theorem minimum_extremes_finite_ncard_le_four_mul
    (hdim : Module.finrank ℝ E = 2) (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (hint : (interior K).Nonempty) (hV : 0 < μ.real K)
    (s : Finset η) (H : η → E →ᵃ[ℝ] ℝ) (c : η → ℝ)
    (hrep : ∀ x, x ∈ K ↔ ∀ j ∈ s, H j x ≤ c j)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hW : ∀ i, 0 < Body.width K (f i)) {B : ℝ} (hB : B ≤ 1)
    (hbudget : budget K f lo hi ≤ B)
    (hneg : GlobalPlankBodyMinimum.margin μ K f lo hi 2 B < 0)
    (hglobal : IsGlobalMinimum μ K f lo hi 2 B)
    (hgap : 0 < μ.real (K \ covered f lo hi))
    (hends : ∀ i, (∀ x ∈ K, f i x < lo i ∧ f i x < hi i) ∨
      ((∃ x ∈ K, f i x < lo i) ∧ (∃ y ∈ K, hi i < f i y))) :
    (K.extremePoints ℝ).Finite ∧ (K.extremePoints ℝ).ncard ≤ 4 * Fintype.card ι := by
  classical
  obtain ⟨t, _, hrep', hfacets⟩ :=
    IrredundantHalfspaces.exists_facet_presentation s H c hrep hint
  have hne : K.Nonempty := hint.mono interior_subset
  have hface : ∀ j ∈ t, ¬∀ x ∈ K, H j x = c j → x ∈ covered f lo hi := by
    intro j hj
    obtain ⟨hjnonzero, p, hp, hstrict⟩ := hfacets j hj
    let J := {k // k ∈ t.erase j}
    let H' : J → E →ᵃ[ℝ] ℝ := fun k => H k.val
    let c' : J → ℝ := fun k => c k.val
    have hdesc : K = {x | H j x ≤ c j ∧ ∀ k, H' k x ≤ c' k} := by
      ext x
      rw [hrep' x]
      constructor
      · intro hx
        exact ⟨hx j hj, fun k => hx k.val (Finset.mem_erase.mp k.property).2⟩
      · rintro ⟨ha, hb⟩ k hk
        by_cases he : k = j
        · simpa [he] using ha
        · exact hb ⟨k, Finset.mem_erase.mpr ⟨he, hk⟩⟩
    have hstrict' : ∀ k, H' k p < c' k := fun k =>
      hstrict k.val (Finset.mem_erase.mp k.property).2 (Finset.mem_erase.mp k.property).1
    exact no_fully_covered_facet μ hK (H j) hjnonzero H' c' (c j)
      hdesc p hp hstrict' f lo hi ho hV hW 2 hbudget hglobal hgap hends
  let A (i) := K.extremePoints ℝ ∩ {x | lo i ≤ f i x ∧ f i x ≤ hi i}
  have hA (i) : (A i).Finite ∧ (A i).ncard ≤ 2 := by
    have hfi := AffineLevelCoincidence.linear_ne_zero_of_width_pos hK hne (f i) (hW i)
    obtain ⟨L, hL⟩ := exists_plank_chart hdim (f i) hfi
    apply PlanarStripVertices.strip_extremes_finite_ncard_le_two_of_chart
      L (f i) (f i 0) hL t H c hK hc hrep' (lo i) (hi i)
    intro j hj hn
    apply hface j hj
    intro x hx hHx
    exact mem_iUnion.mpr ⟨i, hn x hx hHx⟩
  have hcovered : (K.extremePoints ℝ ∩ covered f lo hi).Finite ∧
      (K.extremePoints ℝ ∩ covered f lo hi).ncard ≤ 2 * Fintype.card ι := by
    have he : K.extremePoints ℝ ∩ covered f lo hi = ⋃ i, A i := inter_iUnion _ _
    rw [he]
    refine ⟨finite_iUnion fun i => (hA i).1, ?_⟩
    calc
      (⋃ i, A i).ncard ≤ ∑ i, (A i).ncard := ncard_iUnion_le_of_fintype A
      _ ≤ ∑ _i : ι, 2 := Finset.sum_le_sum fun i _ => (hA i).2
      _ = 2 * Fintype.card ι := by simp [Nat.mul_comm]
  obtain ⟨huncovered, hcount⟩ := uncovered_ncard_le_singletonFaces μ hK hc hne hV
    f lo hi ho hW 2 hB hbudget hneg hglobal
  have hsingle : (singletonFaces K f).ncard ≤ 2 * Fintype.card ι := by
    simpa [Nat.card_prod, Nat.card_eq_fintype_card, Nat.mul_comm]
      using (singletonFaces K f).ncard_le_card
  have he : (K.extremePoints ℝ \ covered f lo hi) ∪
      (K.extremePoints ℝ ∩ covered f lo hi) = K.extremePoints ℝ := sdiff_union_inter _ _
  refine ⟨he ▸ huncovered.union hcovered.1, ?_⟩
  calc
    (K.extremePoints ℝ).ncard = ((K.extremePoints ℝ \ covered f lo hi) ∪
        (K.extremePoints ℝ ∩ covered f lo hi)).ncard := congrArg Set.ncard he.symm
    _ ≤ (K.extremePoints ℝ \ covered f lo hi).ncard +
        (K.extremePoints ℝ ∩ covered f lo hi).ncard := ncard_union_le _ _
    _ ≤ 4 * Fintype.card ι := by have := hcovered.2; omega

/-- Null windows may initially meet the body. Move them outside for the
count; the body and its extreme points remain unchanged. -/
theorem normalized_minimum_extremes_finite_ncard_le_four_mul
    (hdim : Module.finrank ℝ E = 2) (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0 < μ.real K)
    (s : Finset η) (H : η → E →ᵃ[ℝ] ℝ) (c : η → ℝ)
    (hrep : ∀ x, x ∈ K ↔ ∀ j ∈ s, H j x ≤ c j)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hW : ∀ i, 0 < Body.width K (f i))
    (hnorm : ∀ i x, x ∈ K → f i x ≤ 1) {B : ℝ} (hB : B ≤ 1)
    (hbudget : budget K f lo hi ≤ B)
    (hneg : GlobalPlankBodyMinimum.margin μ K f lo hi 2 B < 0)
    (hglobal : IsGlobalMinimum μ K f lo hi 2 B)
    (hgap : 0 < μ.real (K \ covered f lo hi)) :
    (K.extremePoints ℝ).Finite ∧ (K.extremePoints ℝ).ncard ≤ 4 * Fintype.card ι := by
  have hint : (interior K).Nonempty := by
    by_contra hn
    have he : interior K = ∅ := not_nonempty_iff_eq_empty.mp hn
    have hs : K ⊆ frontier K := by rw [frontier, he, sdiff_empty]; exact subset_closure
    have hz := measure_mono_null hs (hc.addHaar_frontier μ)
    simp [Measure.real, hz] at hV
  have hf (i) := AffineLevelCoincidence.linear_ne_zero_of_width_pos hK
    (hint.mono interior_subset) (f i) (hW i)
  obtain ⟨a, b, hab, hbud, hgap', hcases⟩ := move_null_windows μ K f hf lo hi ho
  have hmargin : GlobalPlankBodyMinimum.margin μ K f a b 2 B =
      GlobalPlankBodyMinimum.margin μ K f lo hi 2 B := by
    simp only [GlobalPlankBodyMinimum.margin, hbud, hgap']
  have hglobal' : IsGlobalMinimum μ K f a b 2 B := by
    intro C g l u hC hCc hCV hCW horder hCB
    rw [hmargin]
    exact hglobal C g l u hC hCc hCV hCW horder hCB
  apply minimum_extremes_finite_ncard_le_four_mul hdim μ hK hc hint hV s H c hrep
    f a b hab hW hB (hbud ▸ hbudget) (hmargin ▸ hneg) hglobal' (hgap' ▸ hgap)
  intro i
  rcases hcases i with ⟨hpos, ha, hb⟩ | ⟨ha, hb⟩
  · right
    rw [ha, hb]
    apply GlobalPlankBoundaryMinimum.active_window_interior μ (by omega)
      hK hc hV f lo hi ho hW hB hbudget
    · simpa only [hdim] using hneg
    · simpa only [hdim] using hglobal
    · exact hpos
  · left
    intro x hx
    rw [ha, hb]
    have := hnorm i x hx
    constructor <;> linarith

/-- Every strict planar quantitative counterexample has a representative
which is the convex hull of at most 4m points, with no larger defect.
There is no preliminary polygon-size assumption, and null windows are allowed. -/
theorem exists_counterexample_with_at_most_four_mul_vertices
    {m : ℕ} {K : Set PlanarQuantitative.Point}
    (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0 < volume.real K)
    (f : Fin m → PlanarQuantitative.Point →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ)
    (hW : ∀ i, 0 < Body.width K (f i)) (ho : ∀ i, lo i ≤ hi i) {B : ℝ}
    (hB : B ≤ 1) (hbudget : budget K f lo hi ≤ B)
    (hneg : GlobalPlankBodyMinimum.margin volume K f lo hi 2 B < 0) :
    ∃ (C : Set PlanarQuantitative.Point)
      (g : Fin m → PlanarQuantitative.Point →ᵃ[ℝ] ℝ) (a b : Fin m → ℝ),
      IsCompact C ∧ Convex ℝ C ∧ 0 < volume.real C ∧
      (∀ i, Body.width C (g i) = 1) ∧ (∀ i, a i ≤ b i) ∧ budget C g a b ≤ B ∧
      GlobalPlankBodyMinimum.margin volume C g a b 2 B < 0 ∧
      GlobalPlankBodyMinimum.margin volume C g a b 2 B ≤
        GlobalPlankBodyMinimum.margin volume K f lo hi 2 B ∧
      ∃ V : Finset PlanarQuantitative.Point, V.card ≤ 4 * m ∧ C = convexHull ℝ (V : Set _) := by
  classical
  obtain ⟨C, g, a, b, hC, hCc, hCV, hunit, hnorm, hab, hbud, hnegative,
      hglobal, _, hgap, n, H, c, hrep⟩ :=
    PlanarGlobalPositivePolygon.exists_negative_polygonal_minimum_positive_gap
      hK hc hV f lo hi hW ho hB hbudget hneg
  have hdim : Module.finrank ℝ PlanarQuantitative.Point = 2 := by
    simp [PlanarQuantitative.Point]
  obtain ⟨hfinite, hcard⟩ := normalized_minimum_extremes_finite_ncard_le_four_mul
    hdim volume hC hCc hCV Finset.univ H c (by intro x; simp [hrep]) g a b hab
    (fun i => by rw [hunit]; norm_num) (fun i x hx => (hnorm i x hx).2)
    hB hbud hnegative hglobal hgap
  have hconv := closure_convexHull_extremePoints hC hCc
  rw [(hfinite.isClosed_convexHull ℝ).closure_eq] at hconv
  refine ⟨C, g, a, b, hC, hCc, hCV, hunit, hab, hbud, hnegative,
    hglobal K f lo hi hK hc hV hW ho hbudget, hfinite.toFinset, ?_, ?_⟩
  · rw [← ncard_eq_toFinset_card _ hfinite]
    simpa using hcard
  · simpa using hconv.symm

end Plank.PlanarFourMReduction
