/- Positive-budget equality on the endpoint-domain boundary has a four-vertex body. -/
module

public import Plank.Proofs.Quant.PlanarSupportPairTransport
public import Plank.Proofs.Quant.PlanarOnlyOnePositive
public import Plank.Proofs.Quant.PlanarCriticalNormalForm

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarBoundaryShape

open Set MeasureTheory PlanarQuantitative PlanarParameterDomain PlanarGapCells
open Plank.Convex.DeficientHeightTilt
open Plank.Convex.PlanarTight TwoPlankClassification
open scoped BigOperators Topology

theorem support_pair {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0 < (volume K).toReal) (X Y : Point →ᵃ[ℝ] ℝ) (H : Ranges K X Y)
    (l u m v : ℝ) (hface : l = 0 ∨ u = 1) (hlu : l ≤ u) (hmv : m < v)
    (hR : (u-l)+(v-m) < 1)
    (heq : (volume (K \ ({x | l ≤ X x ∧ X x ≤ u} ∪ {x | m ≤ Y x ∧ Y x ≤ v}))).toReal =
      (1-((u-l)+(v-m)))^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨a,ha,hXa⟩ := H.maxX
  obtain ⟨b,hb,hXb⟩ := H.minX
  obtain ⟨hWX,hWY⟩ := PlanarCriticalNormalForm.rangeWidth_eq_one X Y H
  have hsupport : X b = l ∨ X a = u := by
    rcases hface with hl | hu
    · exact Or.inl (hXb.trans hl.symm)
    · exact Or.inr (hXa.trans hu.symm)
  have hmax (x) (hx : x ∈ K) : X x ≤ X a := (H.box x hx).1.2.trans_eq hXa.symm
  have hmin (x) (hx : x ∈ K) : X b ≤ X x := hXb.trans_le (H.box x hx).1.1
  apply PlanarSupportPairClassification.equality_implies_four_vertices_of_support
    hK hconv hV X Y a b ha hb hmax hmin l u m v hsupport hlu hmv
    (by rw [hWX]; exact zero_lt_one) (by rw [hWY]; exact zero_lt_one)
    (by simpa only [hWX,hWY,div_one] using hR)
  have hd : max 0 (1-(u-l)-(v-m)) = 1-((u-l)+(v-m)) := by
    rw [max_eq_right (by linarith only [hR])]
    ring
  simpa only [hWX,hWY,div_one,hd] using heq

/-- All positive-budget boundary equalities are covered: either window
can have zero width or touch either support endpoint. No cell-count or
genericity assumption is needed. -/
theorem four_vertices {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 2 → Point →ᵃ[ℝ] ℝ) (H : Ranges K (f 0) (f 1))
    (p : Endpoints 2) (hp : p ∈ domain K f) (hnot : p ∉ interior (domain K f))
    (hR0 : 0 < budget K f p) (hR1 : budget K f p < 1)
    (heq : gapArea K f p = (1-budget K f p)^2*(volume K).toReal) :
    ∃ a b c d : Point, K = convexHull ℝ {a,b,c,d} := by
  obtain ⟨hW0,hW1⟩ := PlanarCriticalNormalForm.rangeWidth_eq_one (f 0) (f 1) H
  have hW : ∀ i, 0 < rangeWidth K (f i) := by
    intro i
    fin_cases i
    · change 0 < rangeWidth K (f 0)
      rw [hW0]
      exact zero_lt_one
    · change 0 < rangeWidth K (f 1)
      rw [hW1]
      exact zero_lt_one
  by_cases hz : ∃ i, p.1 i = p.2 i
  · exact PlanarOnlyOnePositive.two_of_zero_window hK hconv hne hV f p hW
      (fun i => (hp.1 i).2.1) hz hR0 hR1 heq
  have hstrict (i) : p.1 i < p.2 i :=
    lt_of_le_of_ne (hp.1 i).2.1 (fun he => hz ⟨i,he⟩)
  have hbudget : budget K f p = (p.2 0-p.1 0)+(p.2 1-p.1 1) := by
    simp only [budget,Fin.sum_univ_two,hW0,hW1,div_one]
  have hunion : (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) =
      {x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪
      {x | p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1} := by
    ext x
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, hx⟩
      fin_cases i
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (hx | hx)
      · exact mem_iUnion.mpr ⟨0,hx⟩
      · exact mem_iUnion.mpr ⟨1,hx⟩
  have harea : (volume (K \
      ({x | p.1 0 ≤ f 0 x ∧ f 0 x ≤ p.2 0} ∪
       {x | p.1 1 ≤ f 1 x ∧ f 1 x ≤ p.2 1}))).toReal =
      (1-((p.2 0-p.1 0)+(p.2 1-p.1 1)))^2*(volume K).toReal := by
    simpa only [gapArea,hunion,hbudget] using heq
  rcases boundary_cases K f hp hnot with hbad | ⟨i,hi⟩
  · exact (lt_irrefl 1 (hbad ▸ hR1)).elim
  · have hface : p.1 i = 0 ∨ p.2 i = 1 := by
      rcases hi with h | h | h
      · exact Or.inl h
      · exact (hz ⟨i,h⟩).elim
      · exact Or.inr h
    fin_cases i
    · exact support_pair hK hconv hV (f 0) (f 1) H (p.1 0) (p.2 0) (p.1 1) (p.2 1) hface
        (hp.1 0).2.1 (hstrict 1) (by rwa [← hbudget]) harea
    · apply support_pair hK hconv hV (f 1) (f 0) H.swap (p.1 1) (p.2 1) (p.1 0) (p.2 0) hface
        (hp.1 1).2.1 (hstrict 0)
      · rw [add_comm,← hbudget]
        exact hR1
      · simpa only [union_comm,add_comm (p.2 1-p.1 1) (p.2 0-p.1 0)] using harea

end Plank.PlanarBoundaryShape

/-- info: 'Plank.PlanarBoundaryShape.four_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarBoundaryShape.four_vertices
