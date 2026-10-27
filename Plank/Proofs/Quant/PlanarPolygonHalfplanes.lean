/- Closed finite half-plane intersections and their actual polygon area. -/
module

public import Plank.Proofs.Quant.PlanarAffineCoordinates

public import Plank.Proofs.Quant.PlanarPolygonPartition
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FinCases

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPolygonHalfplanes

open Set MeasureTheory PlanarQuantitative PlanarPolygonSlabs PlanarPolygonPartition

/-- The closed version of the slab model, in the final theorem's coordinates. -/
def closedSlab {ι κ : Type*} (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) : Set Point :=
  {x | x 0 ∈ Icc a b ∧ (∀ i, ls i*x 0+lc i ≤ x 1) ∧
    ∀ j, x 1 ≤ us j*x 0+uc j}

theorem measure_vertical_line (a : ℝ) : volume {x : Point | x 0 = a} = 0 := by
  have heq : {x : Point | x 0 = a} =
      MeasurableEquiv.finTwoArrow ⁻¹' (({a} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext x
    simp
  rw [heq, (volume_preserving_finTwoArrow ℝ).measure_preimage_equiv,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Closing the omitted left edge changes no area, including when the
horizontal interval has length zero. -/
theorem measure_closedSlab {ι κ : Type*}
    (a b : ℝ) (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    volume (closedSlab a b ls lc us uc) = volume (coordinateSlab a b ls lc us uc) := by
  have heq : closedSlab a b ls lc us uc \ {x : Point | x 0 = a} =
      coordinateSlab a b ls lc us uc := by
    ext x
    constructor
    · rintro ⟨⟨hx, hl, hu⟩, hn⟩
      exact ⟨⟨lt_of_le_of_ne hx.1 (Ne.symm hn), hx.2⟩, hl, hu⟩
    · rintro ⟨hx, hl, hu⟩
      exact ⟨⟨⟨hx.1.le, hx.2⟩, hl, hu⟩, ne_of_gt hx.1⟩
  rw [← heq, measure_sdiff_null (measure_vertical_line a)]

/-- A finite half-plane intersection inside a closed rectangle. Zero normal
vectors, vertical boundaries and empty rectangles are permitted. -/
def boxedRegion {ι : Type*} (a b c d : ℝ) (A B C : ι → ℝ) : Set Point :=
  {x | x 0 ∈ Icc a b ∧ x 1 ∈ Icc c d ∧ ∀ i, A i*x 0+B i*x 1 ≤ C i}

/-- Include a bounding side along with the sides indexed by a subtype. -/
def withBound {ι : Type*} {p : ι → Prop} (f : ι → ℝ) (c : ℝ) : Option {i // p i} → ℝ
  | none => c
  | some i => f i

def graphSlope {ι : Type*} {p : ι → Prop} (A B : ι → ℝ) : Option {i // p i} → ℝ :=
  withBound (fun i => -A i/B i) 0

def graphOffset {ι : Type*} {p : ι → Prop} (B C : ι → ℝ) (c : ℝ) :
    Option {i // p i} → ℝ := withBound (fun i => C i/B i) c

theorem lower_graph_iff {A B C x y : ℝ} (hB : B < 0) :
    -A/B*x+C/B ≤ y ↔ A*x+B*y ≤ C := by
  have heq : -A/B*x+C/B = (C-A*x)/B := by ring
  rw [heq, div_le_iff_of_neg hB]
  constructor <;> intro h <;> nlinarith only [h]

theorem upper_graph_iff {A B C x y : ℝ} (hB : 0 < B) :
    y ≤ -A/B*x+C/B ↔ A*x+B*y ≤ C := by
  have heq : -A/B*x+C/B = (C-A*x)/B := by ring
  rw [heq, le_div_iff₀ hB]
  constructor <;> intro h <;> nlinarith only [h]

/-- All nonvertical half-planes become lower or upper graphs; the two
horizontal bounding sides ensure both finite families are nonempty. -/
theorem boxedRegion_eq_closedSlab {ι : Type*}
    (a b c d : ℝ) (A B C : ι → ℝ) (hB : ∀ i, B i ≠ 0) :
    boxedRegion a b c d A B C = closedSlab a b
      (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
      (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d) := by
  ext x
  constructor
  · rintro ⟨hx, hy, h⟩
    refine ⟨hx, ?_, ?_⟩
    · intro i
      cases i with
      | none => simpa [graphSlope, graphOffset, withBound] using hy.1
      | some i => exact (lower_graph_iff i.property).mpr (h i)
    · intro i
      cases i with
      | none => simpa [graphSlope, graphOffset, withBound] using hy.2
      | some i => exact (upper_graph_iff i.property).mpr (h i)
  · rintro ⟨hx, hl, hu⟩
    refine ⟨hx, ⟨?_, ?_⟩, fun i => ?_⟩
    · simpa [graphSlope, graphOffset, withBound] using hl none
    · simpa [graphSlope, graphOffset, withBound] using hu none
    · rcases lt_or_gt_of_ne (hB i) with hneg | hpos
      · exact (lower_graph_iff hneg).mp (hl (some ⟨i, hneg⟩))
      · exact (upper_graph_iff hpos).mp (hu (some ⟨i, hpos⟩))

/-- The actual area formula now applies to closed half-plane intersections,
without supplying any partition or active-facet certificates. -/
theorem exists_closed_area_decomposition {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ] {a b : ℝ} (hab : a ≤ b)
    (ls lc : ι → ℝ) (us uc : κ → ℝ) :
    ∃ n ≤ (crossingSet ls lc us uc).card+1,
      ∃ (r : ℕ → ℝ) (i : ℕ → ι) (j : ℕ → κ),
      Monotone r ∧ r 0 = a ∧ r n = b ∧
      (∀ k, r k ∈ insert a (insert b (crossingSet ls lc us uc))) ∧
      (volume (closedSlab a b ls lc us uc)).toReal =
        ∑ k ∈ Finset.range n, max 0
          ((r (k+1)-r k)*((us (j k)-ls (i k))*(r k+r (k+1))+
            2*(uc (j k)-lc (i k)))/2) := by
  rw [measure_closedSlab]
  exact exists_actual_area_decomposition hab ls lc us uc

/-- The vertical inequalities, together with the bounding interval, form
one closed interval. Constant inequalities are required to be consistent;
the interval is allowed to be empty. -/
theorem exists_vertical_interval {ι : Type*} [Fintype ι]
    (a b : ℝ) (A B C : ι → ℝ)
    (hzero : ∀ i, A i = 0 → B i = 0 → 0 ≤ C i) :
    ∃ l u : ℝ, ∀ x : ℝ,
      x ∈ Icc l u ↔ x ∈ Icc a b ∧ ∀ i, B i = 0 → A i*x ≤ C i := by
  classical
  let L : Option {i // B i = 0 ∧ A i < 0} → ℝ := withBound (fun i => C i/A i) a
  let U : Option {i // B i = 0 ∧ 0 < A i} → ℝ := withBound (fun i => C i/A i) b
  obtain ⟨li, _, hL⟩ := Finset.exists_max_image Finset.univ L Finset.univ_nonempty
  obtain ⟨ui, _, hU⟩ := Finset.exists_min_image Finset.univ U Finset.univ_nonempty
  refine ⟨L li, U ui, fun x => ?_⟩
  constructor
  · intro hx
    have hl (k) : L k ≤ x := (hL k (Finset.mem_univ _)).trans hx.1
    have hu (k) : x ≤ U k := hx.2.trans (hU k (Finset.mem_univ _))
    refine ⟨⟨?_, ?_⟩, fun i hBi => ?_⟩
    · simpa [L, withBound] using hl none
    · simpa [U, withBound] using hu none
    · rcases lt_trichotomy (A i) 0 with hneg | heq | hpos
      · have h : C i/A i ≤ x := hl (some ⟨i, hBi, hneg⟩)
        simpa only [mul_comm] using (div_le_iff_of_neg hneg).mp h
      · simpa only [heq, zero_mul] using hzero i heq hBi
      · have h : x ≤ C i/A i := hu (some ⟨i, hBi, hpos⟩)
        simpa only [mul_comm] using (le_div_iff₀ hpos).mp h
  · rintro ⟨hx, h⟩
    constructor
    · cases li with
      | none => exact hx.1
      | some i =>
        apply (div_le_iff_of_neg i.property.2).mpr
        simpa only [mul_comm] using h i i.property.1
    · cases ui with
      | none => exact hx.2
      | some i =>
        apply (le_div_iff₀ i.property.2).mpr
        simpa only [mul_comm] using h i i.property.1

/-- Splitting by the vertical coefficient handles every orientation of a
half-plane. No generic coordinate rotation is needed for this set equality. -/
theorem boxedRegion_eq_closedSlab_of_vertical_interval {ι : Type*}
    (a b c d l u : ℝ) (A B C : ι → ℝ)
    (hvertical : ∀ x : ℝ,
      x ∈ Icc l u ↔ x ∈ Icc a b ∧ ∀ i, B i = 0 → A i*x ≤ C i) :
    boxedRegion a b c d A B C = closedSlab l u
      (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
      (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d) := by
  ext x
  constructor
  · rintro ⟨hx, hy, h⟩
    refine ⟨(hvertical (x 0)).mpr ⟨hx, ?_⟩, ?_, ?_⟩
    · intro i hBi
      simpa only [hBi, zero_mul, add_zero] using h i
    · intro i
      cases i with
      | none => simpa [graphSlope, graphOffset, withBound] using hy.1
      | some i => exact (lower_graph_iff i.property).mpr (h i)
    · intro i
      cases i with
      | none => simpa [graphSlope, graphOffset, withBound] using hy.2
      | some i => exact (upper_graph_iff i.property).mpr (h i)
  · rintro ⟨hx, hl, hu⟩
    obtain ⟨hx', hv⟩ := (hvertical (x 0)).mp hx
    refine ⟨hx', ⟨?_, ?_⟩, fun i => ?_⟩
    · simpa [graphSlope, graphOffset, withBound] using hl none
    · simpa [graphSlope, graphOffset, withBound] using hu none
    · rcases lt_trichotomy (B i) 0 with hneg | heq | hpos
      · exact (lower_graph_iff hneg).mp (hl (some ⟨i, hneg⟩))
      · simpa only [heq, zero_mul, add_zero] using hv i heq
      · exact (upper_graph_iff hpos).mp (hu (some ⟨i, hpos⟩))

/-- Every finite closed half-plane intersection in a box is either empty or
is exactly the closed graph model on an ordered horizontal interval. The
choice of interval is constructed, including vertical and zero normals. -/
theorem boxedRegion_empty_or_eq_closedSlab {ι : Type*} [Fintype ι]
    (a b c d : ℝ) (A B C : ι → ℝ) :
    boxedRegion a b c d A B C = ∅ ∨ ∃ l u : ℝ, l ≤ u ∧
      boxedRegion a b c d A B C = closedSlab l u
        (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
        (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d) := by
  classical
  by_cases hzero : ∀ i, A i = 0 → B i = 0 → 0 ≤ C i
  · obtain ⟨l, u, hv⟩ := exists_vertical_interval a b A B C hzero
    have heq := boxedRegion_eq_closedSlab_of_vertical_interval a b c d l u A B C hv
    by_cases hlu : l ≤ u
    · exact Or.inr ⟨l, u, hlu, heq⟩
    · left
      rw [heq]
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hlu (hx.1.1.trans hx.1.2)
  · left
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply hzero
    intro i hAi hBi
    simpa only [hAi, hBi, zero_mul, add_zero] using hx.2.2 i

/-- An unconditional actual-area decomposition for a box clipped by any
finite family of closed half-planes. The only alternative is an empty set. -/
theorem exists_boxed_area_decomposition {ι : Type*} [Fintype ι]
    (a b c d : ℝ) (A B C : ι → ℝ) :
    let ls := graphSlope (p := fun i => B i < 0) A B
    let lc := graphOffset (p := fun i => B i < 0) B C c
    let us := graphSlope (p := fun i => 0 < B i) A B
    let uc := graphOffset (p := fun i => 0 < B i) B C d
    boxedRegion a b c d A B C = ∅ ∨
      ∃ n ≤ (crossingSet ls lc us uc).card+1,
        ∃ (r : ℕ → ℝ) (i : ℕ → Option {k // B k < 0})
          (j : ℕ → Option {k // 0 < B k}), Monotone r ∧
        (volume (boxedRegion a b c d A B C)).toReal =
          ∑ k ∈ Finset.range n, max 0
            ((r (k+1)-r k)*((us (j k)-ls (i k))*(r k+r (k+1))+
              2*(uc (j k)-lc (i k)))/2) := by
  classical
  dsimp only
  rcases boxedRegion_empty_or_eq_closedSlab a b c d A B C with hempty | ⟨l, u, hlu, heq⟩
  · exact Or.inl hempty
  · right
    obtain ⟨n, hn, r, i, j, hmono, _, _, _, harea⟩ :=
      exists_closed_area_decomposition hlu
        (graphSlope (p := fun i => B i < 0) A B) (graphOffset B C c)
        (graphSlope (p := fun i => 0 < B i) A B) (graphOffset B C d)
    exact ⟨n, hn, r, i, j, hmono, heq ▸ harea⟩

/-- Any bounded intersection of affine half-planes has an enclosing box,
whose addition leaves the actual set unchanged. The box is constructed from
boundedness, so the area calculation needs no supplied coordinate bounds. -/
theorem bounded_affine_region_eq_boxed {ι : Type*}
    (f : ι → Point →ᵃ[ℝ] ℝ) (t : ι → ℝ)
    (hbounded : Bornology.IsBounded {x : Point | ∀ i, f i x ≤ t i}) :
    ∃ R > 0, {x : Point | ∀ i, f i x ≤ t i} =
      boxedRegion (-R) R (-R) R
        (fun i => (f i).linear (Pi.single 0 1))
        (fun i => (f i).linear (Pi.single 1 1)) (fun i => t i-f i 0) := by
  obtain ⟨R, hR, hbound⟩ := hbounded.exists_pos_norm_le
  refine ⟨R, hR, ?_⟩
  ext x
  constructor
  · intro hx
    have hcoord (k : Fin 2) : x k ∈ Icc (-R) R := by
      apply abs_le.mp
      exact (norm_le_pi_norm x k).trans (hbound x hx)
    refine ⟨hcoord 0, hcoord 1, fun i => ?_⟩
    have hi := hx i
    rw [affine_eval_coordinates (f i) x] at hi
    linarith only [hi]
  · intro hx i
    rw [affine_eval_coordinates (f i) x]
    linarith only [hx.2.2 i]

/-- Actual Lebesgue area of any bounded finite intersection of affine
half-planes, with its enclosing box, cuts and active facets all constructed.
No general-position or positive-area hypothesis is required. -/
theorem exists_bounded_affine_area_decomposition {ι : Type*} [Fintype ι]
    (f : ι → Point →ᵃ[ℝ] ℝ) (t : ι → ℝ)
    (hbounded : Bornology.IsBounded {x : Point | ∀ i, f i x ≤ t i}) :
    let A := fun i => (f i).linear (Pi.single 0 1)
    let B := fun i => (f i).linear (Pi.single 1 1)
    let C := fun i => t i-f i 0
    let ls := graphSlope (p := fun i => B i < 0) A B
    let us := graphSlope (p := fun i => 0 < B i) A B
    {x : Point | ∀ i, f i x ≤ t i} = ∅ ∨ ∃ R > 0,
      let lc := graphOffset (p := fun i => B i < 0) B C (-R)
      let uc := graphOffset (p := fun i => 0 < B i) B C R
      ∃ n ≤ (crossingSet ls lc us uc).card+1,
        ∃ (r : ℕ → ℝ) (i : ℕ → Option {k // B k < 0})
          (j : ℕ → Option {k // 0 < B k}), Monotone r ∧
        (volume {x : Point | ∀ i, f i x ≤ t i}).toReal =
          ∑ k ∈ Finset.range n, max 0
            ((r (k+1)-r k)*((us (j k)-ls (i k))*(r k+r (k+1))+
              2*(uc (j k)-lc (i k)))/2) := by
  classical
  dsimp only
  obtain ⟨R, hR, hbox⟩ := bounded_affine_region_eq_boxed f t hbounded
  rcases exists_boxed_area_decomposition (-R) R (-R) R
      (fun i => (f i).linear (Pi.single 0 1))
      (fun i => (f i).linear (Pi.single 1 1)) (fun i => t i-f i 0) with
    hempty | ⟨n, hn, r, i, j, hmono, harea⟩
  · exact Or.inl (hbox.trans hempty)
  · exact Or.inr ⟨R, hR, n, hn, r, i, j, hmono, hbox ▸ harea⟩

end Plank.PlanarPolygonHalfplanes
