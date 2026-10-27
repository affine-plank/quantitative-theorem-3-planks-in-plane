/- Every strict cyclic equality band covers its own middle vertex. -/
module
public import Plank.Proofs.Quant.TriangleEndpointPositions
public import Plank.Proofs.Quant.TriangleTranslationBoundary
public import Plank.Proofs.Quant.CyclicTranslationEquality

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicVertices
open Set MeasureTheory CommonVertex OrdinalArea CyclicArea
open CyclicTranslationEquality TriangleEqualityReductions
open scoped BigOperators

def vertex : Fin 3 → ℝ × ℝ := ![(0,0),(1,0),(0,1)]

theorem vertex_mem (j : Fin 3) : vertex j ∈ stdTriangle.set := by
  fin_cases j <;> norm_num [vertex,Proofs.Quant.stdTriangle_set_eq]

theorem vertex_outside_translates (C : Config)
    (hp : ∀ i, 0 < widths C i)
    (hd : C.deficit=1-(widths C 0+widths C 1+widths C 2))
    (j : Fin 3) (s : Finset (Fin 3)) :
    vertex j-translations C s ∉ RowDeletion.triangle C.deficit := by
  classical
  have he : shift (steps (widths C)) s =
      ∑ i : Fin 3, if i ∈ s then steps (widths C) i else 0 := by
    simp [shift,Finset.sum_ite_mem]
  intro hz
  rw [translations,base,he,Fin.sum_univ_three,hd] at hz
  fin_cases j <;> dsimp [vertex,RowDeletion.triangle] at hz <;>
    by_cases h0 : (0 : Fin 3) ∈ s <;>
    by_cases h1 : (1 : Fin 3) ∈ s <;>
    by_cases h2 : (2 : Fin 3) ∈ s <;>
    simp only [h0,h1,h2,↓reduceIte] at hz <;>
    dsimp [steps] at hz <;>
    rcases hz with ⟨hx,hy,hs⟩ <;> linarith [hp 0,hp 1,hp 2]

theorem uncovered_mem_cell (C : Config) {z : ℝ × ℝ} (hz : z ∈ C.uncovered) :
    ∃ s, z ∈ exteriorCells C s := by
  classical
  let s := Finset.univ.filter (fun i => (C.plank i).hi < dot (C.plank i).u z)
  refine ⟨s,fun i => ?_⟩
  by_cases hi : i ∈ s
  · simpa only [hi,↓reduceIte] using (Finset.mem_filter.mp hi).2
  · simp only [hi,↓reduceIte]
    have hn : ¬ z ∈ (C.plank i).set := by
      intro h
      exact hz.2 (mem_iUnion.mpr ⟨i,h⟩)
    have hmax : dot (C.plank i).u z ≤ (C.plank i).hi := by
      simpa only [s,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hi
    exact lt_of_not_ge (fun h => hn ⟨h,hmax⟩)

theorem cell_core (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hδ : 0 < C.deficit) (he : Equality C)
    (s : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ stdTriangle.set)
    (hs : z ∈ exteriorCells C s) :
    z-translations C s ∈ RowDeletion.triangle C.deficit := by
  have hp := ((equality_iff_partition C hb ha hc hu0 hu1 hu2 hδ).mp he).2
  exact TriangleTranslationBoundary.cell_core_of_exhaustion C _
    (TriangleTranslationBoundary.triangle_closed _) _ hp.2 s hz hs

theorem vertices_covered (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C)
    (j : Fin 3) : ∃ i, vertex j ∈ (C.plank i).set := by
  classical
  have hr : ∀ i, 0 < widths C i := by
    intro i
    simpa only [Config.relW,Plank.relWidth,
      BalancedArea.abc_width_one C hb ha hc hu0 hu1 hu2,div_one,widths] using hp i
  by_contra hn
  have hz : vertex j ∈ C.uncovered := by
    refine ⟨vertex_mem j,?_⟩
    simpa only [mem_iUnion] using hn
  obtain ⟨s,hs⟩ := uncovered_mem_cell C hz
  exact vertex_outside_translates C hr (CyclicArea.deficit_eq C hb ha hc hu0 hu1 hu2)
    j s (cell_core C hb ha hc hu0 hu1 hu2 hδ he s hz.1 hs)

/-- In the open cyclic direction sector, every equality band must straddle
its distinct middle vertex. No endpoint or clipping assumption is imposed. -/
theorem middle_covered (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    ((C.plank 0).lo ≤ b ∧ b ≤ (C.plank 0).hi) ∧
    ((C.plank 1).lo ≤ a ∧ a ≤ (C.plank 1).hi) ∧
    ((C.plank 2).lo ≤ 0 ∧ 0 ≤ (C.plank 2).hi) := by
  have hi := TriangleEndpointPositions.abc_internal C hb ha hc hu0 hu1 hu2 hp hδ he
  have hv := vertices_covered C hb ha hc hu0 hu1 hu2 hp hδ he
  constructor
  · obtain ⟨i,h⟩ := hv 2
    change (C.plank i).lo ≤ dot (C.plank i).u (0,1) ∧
      dot (C.plank i).u (0,1) ≤ (C.plank i).hi at h
    fin_cases i <;> norm_num [hu0,hu1,hu2,dot] at h
    · exact h
    · linarith only [h.2,hi.2.1.2]
    · linarith only [h.1,hi.2.2.1]
  constructor
  · obtain ⟨i,h⟩ := hv 1
    change (C.plank i).lo ≤ dot (C.plank i).u (1,0) ∧
      dot (C.plank i).u (1,0) ≤ (C.plank i).hi at h
    fin_cases i <;> norm_num [hu0,hu1,hu2,dot] at h
    · linarith only [h.2,hi.1.2]
    · exact h
    · linarith only [h.2,hi.2.2.2]
  · obtain ⟨i,h⟩ := hv 0
    change (C.plank i).lo ≤ dot (C.plank i).u (0,0) ∧
      dot (C.plank i).u (0,0) ≤ (C.plank i).hi at h
    fin_cases i <;> norm_num [hu0,hu1,hu2,dot] at h
    · linarith only [h.1,hi.1.1]
    · linarith only [h.1,hi.2.1.1]
    · exact h

end Quant.TriangleCyclicVertices

/-- info: 'Quant.TriangleCyclicVertices.middle_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicVertices.middle_covered
