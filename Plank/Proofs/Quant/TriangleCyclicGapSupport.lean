/- Equality excludes three corner regions of the individual actual widths. -/
module
public import Plank.Proofs.Quant.TriangleCyclicVertices

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicGapSupport
open Set MeasureTheory CommonVertex OrdinalArea CyclicArea
open CyclicTranslationEquality TriangleEqualityReductions TriangleCyclicVertices
open scoped BigOperators

theorem core_support (C : Config) (hr : ∀ i, 0 ≤ widths C i)
    (hd : C.deficit=1-(widths C 0+widths C 1+widths C 2))
    (s : Finset (Fin 3)) {z : ℝ × ℝ}
    (hz : z-translations C s ∈ RowDeletion.triangle C.deficit) :
    widths C 2 ≤ z.1+z.2 ∧ z.1 ≤ 1-widths C 1 ∧ z.2 ≤ 1-widths C 0 := by
  classical
  have he : shift (steps (widths C)) s =
      ∑ i : Fin 3, if i ∈ s then steps (widths C) i else 0 := by
    simp [shift,Finset.sum_ite_mem]
  rw [translations,base,he,Fin.sum_univ_three,hd] at hz
  dsimp [RowDeletion.triangle] at hz
  by_cases h0 : (0 : Fin 3) ∈ s <;>
    by_cases h1 : (1 : Fin 3) ∈ s <;>
    by_cases h2 : (2 : Fin 3) ∈ s <;>
    simp only [h0,h1,h2,↓reduceIte] at hz <;>
    dsimp [steps] at hz <;>
    rcases hz with ⟨hx,hy,hs⟩ <;>
    constructor <;> (try constructor) <;> linarith [hr 0,hr 1,hr 2]

/-- The whole actual gap is confined by three explicit support lines.
No positivity of the individual widths is required for this conclusion. -/
theorem gap_support (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hδ : 0 < C.deficit) (he : Equality C)
    {z : ℝ × ℝ} (hz : z ∈ C.uncovered) :
    widths C 2 ≤ z.1+z.2 ∧ z.1 ≤ 1-widths C 1 ∧ z.2 ≤ 1-widths C 0 := by
  obtain ⟨s,hs⟩ := uncovered_mem_cell C hz
  exact core_support C (fun i => sub_nonneg.mpr (C.plank i).lo_le_hi)
    (CyclicArea.deficit_eq C hb ha hc hu0 hu1 hu2) s
    (cell_core C hb ha hc hu0 hu1 hu2 hδ he s hz.1 hs)

def corner (C : Config) : Fin 3 → Set (ℝ × ℝ) :=
  ![{z | z.1+z.2 < widths C 2}, {z | 1-widths C 1 < z.1},
    {z | 1-widths C 0 < z.2}]

theorem corner_open (C : Config) (j : Fin 3) : IsOpen (corner C j) := by
  fin_cases j
  · exact isOpen_lt (continuous_fst.add continuous_snd) continuous_const
  · exact isOpen_lt continuous_const continuous_fst
  · exact isOpen_lt continuous_const continuous_snd

theorem corner_contains_vertex (C : Config) (hp : ∀ i, 0 < widths C i) (j : Fin 3) :
    vertex j ∈ corner C j := by
  fin_cases j
  · change 0+0 < widths C 2
    linarith only [hp 2]
  · change 1-widths C 1 < 1
    linarith only [hp 1]
  · change 1-widths C 0 < 1
    linarith only [hp 0]

theorem corner_covered (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hδ : 0 < C.deficit) (he : Equality C) (j : Fin 3) :
    stdTriangle.set ∩ corner C j ⊆ ⋃ i, (C.plank i).set := by
  intro z hz
  by_contra hn
  have hs := gap_support C hb ha hc hu0 hu1 hu2 hδ he ⟨hz.1,hn⟩
  have hh := hz.2
  fin_cases j
  · exact (not_lt_of_ge hs.1) hh
  · exact (not_lt_of_ge hs.2.1) hh
  · exact (not_lt_of_ge hs.2.2) hh

end Quant.TriangleCyclicGapSupport

/-- info: 'Quant.TriangleCyclicGapSupport.gap_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicGapSupport.gap_support
