/- Pure geometry of seven nonempty closed exterior cells. -/
module

public import Plank.Proofs.Quant.PlanarSignPatterns
public import Plank.Proofs.Quant.PlanarWindowData
public import Plank.Proofs.Quant.FiniteDimensionalEndpointCells
public import Plank.Convex.PlanarAffineRelation
public import ResearchFormalized.Algebra.SignedSum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenNonemptyCells

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open FiniteDimensionalEndpointMajorants (signCell)
open FiniteDimensionalCapWindowScaling (measure_level_zero)
open PlanarSevenCellGeometry
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

/-- Count closed exterior cells, including line segments and singletons. -/
def nonemptyCells (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3) :
    Finset (Finset (Fin 3)) := by
  classical
  exact Finset.univ.filter (fun s => (signCell K f p s).Nonempty)

theorem mem_nonemptyCells (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints 3) (s : Finset (Fin 3)) :
    s ∈ nonemptyCells K f p ↔ (signCell K f p s).Nonempty := by
  simp [nonemptyCells]

theorem corners_of_seven (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints 3) (hcount : 7 ≤ (nonemptyCells K f p).card)
    (i j : Fin 3) (hij : i ≠ j) :
    ∀ b c : Bool, ∃ x ∈ K,
      (if b then p.2 i ≤ f i x else f i x ≤ p.1 i) ∧
      (if c then p.2 j ≤ f j x else f j x ≤ p.1 j) := by
  intro b c
  obtain ⟨s,hs,hsi,hsj⟩ := exists_pair_pattern (nonemptyCells K f p) hcount i j hij b c
  obtain ⟨x,hx⟩ := (mem_nonemptyCells K f p s).mp hs
  refine ⟨x,hx.1,?_,?_⟩
  · simpa only [hsi] using hx.2 i
  · simpa only [hsj] using hx.2 j

/-- A strict triple-intersection point excludes the two opposed weak
exterior sign patterns selected by a nonzero affine relation. -/
theorem weakCell_empty_of_strict_triple_relation {κ : Type*} [Fintype κ]
    (f : κ → Point →ᵃ[ℝ] ℝ) (lo hi : κ → ℝ) (s : Finset κ)
    (a : κ → ℝ) (ha : ∃ i, a i ≠ 0) (d : ℝ) (hrel : ∀ x, ∑ i, a i*f i x = d)
    (hsign : ∀ i, (0 < a i → i ∈ s) ∧ (a i < 0 → i ∉ s))
    (y : Point) (hy : ∀ i, lo i < f i y ∧ f i y < hi i) :
    LinearBands.weakCell (fun i x => f i x) lo hi s = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := ResearchFormalized.sum_mul_lt_sum_mul_of_signs a
    (fun i => f i y) (fun i => f i x) ha fun i => by
      constructor
      · intro hp
        exact (hy i).2.trans_le (by simpa only [(hsign i).1 hp, ite_true] using hx i)
      · intro hn
        exact (show f i x ≤ lo i by
          simpa only [(hsign i).2 hn, ite_false] using hx i).trans_lt (hy i).1
  rw [hrel,hrel] at hh
  exact lt_irrefl d hh

/-- Meeting at least one exterior cell from each opposite pair excludes
a strict common window point. -/
theorem strict_triple_empty_of_complement_pairs (K : Set Point)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (p : Endpoints 3)
    (hpresent : ∀ s, s ∈ nonemptyCells K f p ∨ sᶜ ∈ nonemptyCells K f p) :
    {x | ∀ i, p.1 i < f i x ∧ f i x < p.2 i} = ∅ := by
  classical
  obtain ⟨a,ha,d,hrel⟩ := Plank.Convex.PlanarAffineRelation.exists_relation f
  let s := Finset.univ.filter (fun i => 0 < a i)
  have hsign : ∀ i, (0 < a i → i ∈ s) ∧ (a i < 0 → i ∉ s) := by
    intro i
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨id,fun hn => not_lt_of_ge hn.le⟩
  have hasign : ∀ i, (0 < -a i → i ∈ sᶜ) ∧ (-a i < 0 → i ∉ sᶜ) := by
    intro i
    simp only [Finset.mem_compl,s,Finset.mem_filter,Finset.mem_univ,true_and,not_not]
    constructor <;> intro hh <;> linarith
  have harel : ∀ x, ∑ i, (-a i)*f i x = -d := by
    intro x
    simpa only [neg_mul,Finset.sum_neg_distrib] using congrArg Neg.neg (hrel x)
  have hane : ∃ i, (-a i) ≠ 0 := by
    obtain ⟨i,hi⟩ := ha
    exact ⟨i,neg_ne_zero.mpr hi⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hs := weakCell_empty_of_strict_triple_relation f p.1 p.2 s a ha d hrel hsign y hy
  have ht := weakCell_empty_of_strict_triple_relation f p.1 p.2 sᶜ
    (fun i => -a i) hane (-d) harel hasign y hy
  rcases hpresent s with hmem | hmem
  · obtain ⟨x,hx⟩ := (mem_nonemptyCells K f p s).mp hmem
    have hh : x ∈ LinearBands.weakCell (fun i x => f i x) p.1 p.2 s := hx.2
    rw [hs] at hh
    exact hh
  · obtain ⟨x,hx⟩ := (mem_nonemptyCells K f p sᶜ).mp hmem
    have hh : x ∈ LinearBands.weakCell (fun i x => f i x) p.1 p.2 sᶜ := hx.2
    rw [ht] at hh
    exact hh

theorem strict_triple_empty_of_seven (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (p : Endpoints 3) (hcount : 7 ≤ (nonemptyCells K f p).card) :
    {x | ∀ i, p.1 i < f i x ∧ f i x < p.2 i} = ∅ :=
  strict_triple_empty_of_complement_pairs K f p fun s =>
    mem_or_mem_of_seven (nonemptyCells K f p) hcount s sᶜ ne_compl_self

/-- With null affine levels, an empty strict intersection leaves only a
null closed intersection. -/
theorem triple_null_of_strict_empty (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (p : Endpoints 3)
    (hempty : {x | ∀ i, p.1 i < f i x ∧ f i x < p.2 i} = ∅) :
    volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0 := by
  have he : {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} =ᵐ[volume]
      {x | ∀ i, p.1 i < f i x ∧ f i x < p.2 i} := by
    filter_upwards [LinearBands.ae_mem_closedBand_iff_openBand volume (fun i x => f i x)
      p.1 p.2 (fun i => measure_level_zero (f i) (hf i) (p.1 i))
      (fun i => measure_level_zero (f i) (hf i) (p.2 i))] with x hx
    exact propext (forall_congr' hx)
  rw [measure_congr he, hempty, measure_empty]

/-- The closed triple intersection may survive as a null boundary set. -/
theorem triple_null_of_seven (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (p : Endpoints 3)
    (hcount : 7 ≤ (nonemptyCells K f p).card) :
    volume {x | ∀ i, p.1 i ≤ f i x ∧ f i x ≤ p.2 i} = 0 :=
  triple_null_of_strict_empty f hf p (strict_triple_empty_of_seven K f p hcount)

end Plank.PlanarSevenNonemptyCells
