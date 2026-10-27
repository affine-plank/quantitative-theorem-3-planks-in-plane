/- Strict source assignments near the corners of the deficit triangle. -/
module
public import Plank.Proofs.Quant.TriangleCyclicCompatibility

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicCornerAssignments
open Set MeasureTheory CommonVertex OrdinalArea CyclicArea TranslationEquality
open CyclicTranslationEquality TriangleEqualityReductions TriangleCyclicEdgeSeeds
open scoped BigOperators

theorem unique_at_interior (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1)) (hδ : 0 < C.deficit) (he : Equality C)
    {z : ℝ × ℝ} (hz : 0 < z.1 ∧ 0 < z.2 ∧ z.1+z.2 < C.deficit)
    (s t : Finset (Fin 3))
    (hs : z+translations C s ∈ exteriorCells C s)
    (ht : z+translations C t ∈ exteriorCells C t) : s=t := by
  by_contra hne
  let U : Set (ℝ × ℝ) := {w | 0 < w.1 ∧ 0 < w.2 ∧ w.1+w.2 < C.deficit} ∩
    ((fun w => w+translations C s) ⁻¹' exteriorCells C s) ∩
    ((fun w => w+translations C t) ⁻¹' exteriorCells C t)
  have ho : IsOpen U := by
    apply IsOpen.inter
    · apply IsOpen.inter
      · exact (isOpen_lt continuous_const continuous_fst).inter
          ((isOpen_lt continuous_const continuous_snd).inter
            (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
      · exact (TriangleTranslationBoundary.exterior_open C s).preimage (by fun_prop)
    · exact (TriangleTranslationBoundary.exterior_open C t).preimage (by fun_prop)
  have hp := ho.measure_pos volume ⟨z,⟨⟨hz,hs⟩,ht⟩⟩
  have hsub : U ⊆ sourcePiece (RowDeletion.triangle C.deficit) (translations C)
      (exteriorCells C) s ∩ sourcePiece (RowDeletion.triangle C.deficit)
        (translations C) (exteriorCells C) t := by
    intro w hw
    have hc' : w ∈ RowDeletion.triangle C.deficit :=
      ⟨hw.1.1.1.le,hw.1.1.2.1.le,hw.1.1.2.2.le⟩
    exact ⟨⟨hc',hw.1.2⟩,⟨hc',hw.2⟩⟩
  have hd := (((equality_iff_partition C hb ha hc hu0 hu1 hu2 hδ).mp he).2.1) hne
  change volume (_ ∩ _) = 0 at hd
  exact (not_le_of_gt hp) (hd ▸ measure_mono hsub)

theorem strict_seed_between (C : Config) (j : Fin 3) {l h : ℝ}
    (hl : 0 ≤ l) (hlh : l < h) (hh : h ≤ C.deficit)
    (hn : ∀ i, slope (C.plank i).u j ≠ 0)
    (hw : ∀ z ∈ RowDeletion.triangle C.deficit, ∃ s,
      z+translations C s ∈ Plank.LinearBands.weakCell
        (fun i => dot (C.plank i).u) (fun i => (C.plank i).lo)
        (fun i => (C.plank i).hi) s) :
    ∃ t : ℝ, l < t ∧ t < h ∧ ∃ s,
      seed C.deficit j t+translations C s ∈ exteriorCells C s := by
  classical
  let bad : Finset ℝ := Finset.univ.image
    (fun q : Finset (Fin 3) × Fin 3 =>
      ((if q.2 ∈ q.1 then (C.plank q.2).hi else (C.plank q.2).lo)-
        dot (C.plank q.2).u (seed C.deficit j 0+translations C q.1))/
        slope (C.plank q.2).u j)
  obtain ⟨t,ht,hnot⟩ := (Set.Ioo_infinite hlh).exists_notMem_finite bad.finite_toSet
  obtain ⟨s,hs⟩ := hw (seed C.deficit j t)
    (seed_mem _ _ ⟨hl.trans ht.1.le,ht.2.le.trans hh⟩ j)
  have hneq (i : Fin 3) : dot (C.plank i).u (seed C.deficit j t+translations C s) ≠
      (if i ∈ s then (C.plank i).hi else (C.plank i).lo) := by
    intro heq
    apply hnot
    change t ∈ bad
    apply Finset.mem_image.mpr
    refine ⟨(s,i),Finset.mem_univ _,?_⟩
    dsimp only
    apply (div_eq_iff (hn i)).mpr
    have hd := seed_dot (C.plank i).u (translations C s) C.deficit t j
    rw [heq] at hd
    linarith only [hd]
  refine ⟨t,ht.1,ht.2,s,fun i => ?_⟩
  have hh := hs i
  have hne := hneq i
  by_cases his : i ∈ s
  · simp only [his,↓reduceIte] at hh hne ⊢
    exact lt_of_le_of_ne hh hne.symm
  · simp only [his,↓reduceIte] at hh hne ⊢
    exact lt_of_le_of_ne hh hne

theorem edge_seed_near_end (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1)) (hδ : 0 < C.deficit) (he : Equality C)
    (j : Fin 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ C.deficit-ε < t ∧ t < C.deficit ∧ ∃ s,
      seed C.deficit j t+translations C s ∈ exteriorCells C s ∧
      onEdge j (seed C.deficit j t+translations C s) := by
  have hnorm : ∀ i, (C.plank i).u= ![(1,b),(a,1),(c,c-1)] i := by
    intro i
    fin_cases i
    · exact hu0
    · exact hu1
    · exact hu2
  have hn : ∀ i, slope (C.plank i).u j ≠ 0 := by
    intro i
    rw [hnorm]
    fin_cases i <;> fin_cases j <;> dsimp [TriangleCyclicEdgeSeeds.slope] <;>
      intro hh <;> linarith only [hh,hb.1,hb.2,ha.1,ha.2,hc.1,hc.2]
  have hno := ((equality_iff_partition C hb ha hc hu0 hu1 hu2 hδ).mp he).1
  obtain ⟨t,htl,hth,s,hs⟩ := strict_seed_between C j (le_max_left 0 (C.deficit-ε))
    (max_lt hδ (by linarith only [hε])) le_rfl hn
    (weak_assignments_of_no_bad_seed C hb ha hc hu0 hu1 hu2 hno)
  have ht : 0 < t := (le_max_left _ _).trans_lt htl
  let z := seed C.deficit j t+translations C s
  have hzT : z ∈ stdTriangle.set := by
    apply OrdinalArea.translated_mem_triangle (widths C)
      (fun i => sub_nonneg.mpr (C.plank i).lo_le_hi) s
    rw [← CyclicArea.deficit_eq C hb ha hc hu0 hu1 hu2]
    exact seed_mem _ _ ⟨ht.le,hth.le⟩ j
  refine ⟨t,ht,(le_max_right _ _).trans_lt htl,hth,s,hs,?_⟩
  have hstrict := strict_core C hb ha hc hu0 hu1 hu2 hδ he s hzT hs
  rw [Proofs.Quant.stdTriangle_set_eq] at hzT
  fin_cases j
  · change z.2=0
    apply le_antisymm _ hzT.2.1
    by_contra hh
    have h := hstrict.2.1 (lt_of_not_ge hh)
    change (translations C s).2 < 0+(translations C s).2 at h
    linarith only [h]
  · change z.1=0
    apply le_antisymm _ hzT.1
    by_contra hh
    have h := hstrict.1 (lt_of_not_ge hh)
    change (translations C s).1 < 0+(translations C s).1 at h
    linarith only [h]
  · change z.1+z.2=1
    apply le_antisymm hzT.2.2
    by_contra hh
    have h := hstrict.2.2 (lt_of_not_ge hh)
    change (t+(translations C s).1)+(C.deficit-t+(translations C s).2) <
      C.deficit+(translations C s).1+(translations C s).2 at h
    linarith only [h]

theorem translation_formula (C : Config) (s : Finset (Fin 3)) :
    translations C s =
      ((if 0 ∈ s then widths C 0 else 0)+(if 2 ∈ s then widths C 2 else 0),
        widths C 2+(if 1 ∈ s then widths C 1 else 0)-
          (if 2 ∈ s then widths C 2 else 0)) := by
  classical
  have he : shift (steps (widths C)) s =
      ∑ i : Fin 3, if i ∈ s then steps (widths C) i else 0 := by
    simp [shift,Finset.sum_ite_mem]
  rw [translations,base,he,Fin.sum_univ_three]
  by_cases h0 : (0 : Fin 3) ∈ s <;>
    by_cases h1 : (1 : Fin 3) ∈ s <;>
    by_cases h2 : (2 : Fin 3) ∈ s <;>
    simp [h0,h1,h2,steps]

def offset (C : Config) (b a c : ℝ) (s : Finset (Fin 3)) : Fin 3 → ℝ :=
  ![b*(if 1 ∈ s then widths C 1 else 0)+(1-b)*(if 2 ∈ s then widths C 2 else 0),
    a*(if 0 ∈ s then widths C 0 else 0)-(1-a)*(if 2 ∈ s then widths C 2 else 0),
    c*(if 0 ∈ s then widths C 0 else 0)-(1-c)*(if 1 ∈ s then widths C 1 else 0)]

theorem assignment_iff (C : Config) (b a c : ℝ)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1)) (z : ℝ × ℝ) (s : Finset (Fin 3)) :
    z+translations C s ∈ exteriorCells C s ↔ ∀ i,
      if i ∈ s then threshold C z i < offset C b a c s i
      else offset C b a c s i < threshold C z i := by
  classical
  have hn : ∀ i, (C.plank i).u= ![(1,b),(a,1),(c,c-1)] i := by
    intro i
    fin_cases i
    · exact hu0
    · exact hu1
    · exact hu2
  have hv (i : Fin 3) : dot (C.plank i).u (z+translations C s) =
      dot (C.plank i).u (z+base C)+offset C b a c s i+
        (if i ∈ s then widths C i else 0) := by
    rw [translation_formula,hn]
    fin_cases i <;>
      by_cases h0 : (0 : Fin 3) ∈ s <;>
      by_cases h1 : (1 : Fin 3) ∈ s <;>
      by_cases h2 : (2 : Fin 3) ∈ s <;>
      simp only [h0,h1,h2,↓reduceIte,offset,base] <;>
      dsimp [dot] <;> simp only [h0,h1,h2,↓reduceIte] <;> ring
  constructor <;> intro h i
  · have hi := h i
    by_cases his : i ∈ s <;> simp only [his,↓reduceIte] at hi ⊢
    all_goals rw [hv] at hi
    all_goals simp only [his,↓reduceIte] at hi
    all_goals dsimp [threshold,widths] at hi ⊢
    all_goals linarith only [hi]
  · have hi := h i
    by_cases his : i ∈ s <;> simp only [his,↓reduceIte] at hi ⊢
    all_goals rw [hv]
    all_goals simp only [his,↓reduceIte]
    all_goals dsimp [threshold,widths] at hi ⊢
    all_goals linarith only [hi]

theorem ab_patterns (C : Config) (b a c t : ℝ)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1)) (hr : ∀ i, 0 < widths C i)
    (s : Finset (Fin 3))
    (hs : seed C.deficit 0 t+translations C s ∈ exteriorCells C s)
    (hedge : onEdge 0 (seed C.deficit 0 t+translations C s)) :
    let z := seed C.deficit 0 t
    (((1-b)*widths C 2 < threshold C z 0 ∧
      -((1-a)*widths C 2) < threshold C z 1 ∧ threshold C z 2 < 0) ∨
     (threshold C z 0 < (1-b)*widths C 2 ∧
      a*widths C 0-((1-a)*widths C 2) < threshold C z 1 ∧
      threshold C z 2 < c*widths C 0)) := by
  classical
  change 0+(translations C s).2=0 at hedge
  rw [translation_formula] at hedge
  dsimp only at hedge
  have h1 : (1 : Fin 3) ∉ s := by
    intro h1
    by_cases h2 : (2 : Fin 3) ∈ s <;>
      simp only [h1,h2,↓reduceIte] at hedge <;> linarith only [hedge,hr 1,hr 2]
  have h2 : (2 : Fin 3) ∈ s := by
    by_contra h2
    simp only [h1,h2,↓reduceIte] at hedge
    linarith only [hedge,hr 2]
  have h := (assignment_iff C b a c hu0 hu1 hu2 _ s).mp hs
  have h0' := h 0
  have h1' := h 1
  have h2' := h 2
  by_cases h0 : (0 : Fin 3) ∈ s
  · right
    simpa [offset,h0,h1,h2] using And.intro h0' (And.intro h1' h2')
  · left
    simpa [offset,h0,h1,h2] using And.intro h0' (And.intro h1' h2')

theorem bc_patterns (C : Config) (b a c t : ℝ)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1)) (hr : ∀ i, 0 < widths C i)
    (hd : C.deficit=1-(widths C 0+widths C 1+widths C 2))
    (s : Finset (Fin 3))
    (hs : seed C.deficit 2 t+translations C s ∈ exteriorCells C s)
    (hedge : onEdge 2 (seed C.deficit 2 t+translations C s)) :
    let z := seed C.deficit 2 t
    ((threshold C z 0 < b*widths C 1 ∧ threshold C z 1 < a*widths C 0 ∧
      c*widths C 0-(1-c)*widths C 1 < threshold C z 2) ∨
     (threshold C z 0 < b*widths C 1+(1-b)*widths C 2 ∧
      threshold C z 1 < a*widths C 0-(1-a)*widths C 2 ∧
      threshold C z 2 < c*widths C 0-(1-c)*widths C 1)) := by
  classical
  change (t+(translations C s).1)+(C.deficit-t+(translations C s).2)=1 at hedge
  rw [translation_formula,hd] at hedge
  dsimp only at hedge
  have h0 : (0 : Fin 3) ∈ s := by
    by_contra h0
    by_cases h1 : (1 : Fin 3) ∈ s <;> by_cases h2 : (2 : Fin 3) ∈ s <;>
      simp only [h0,h1,h2,↓reduceIte] at hedge <;> linarith only [hedge,hr 0,hr 1]
  have h1 : (1 : Fin 3) ∈ s := by
    by_contra h1
    by_cases h2 : (2 : Fin 3) ∈ s <;>
      simp only [h0,h1,h2,↓reduceIte] at hedge <;> linarith only [hedge,hr 1]
  have h := (assignment_iff C b a c hu0 hu1 hu2 _ s).mp hs
  have h0' := h 0
  have h1' := h 1
  have h2' := h 2
  by_cases h2 : (2 : Fin 3) ∈ s
  · right
    simpa [offset,h0,h1,h2] using And.intro h0' (And.intro h1' h2')
  · left
    simpa [offset,h0,h1,h2] using And.intro h0' (And.intro h1' h2')

end Quant.TriangleCyclicCornerAssignments

/-- info: 'Quant.TriangleCyclicCornerAssignments.unique_at_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicCornerAssignments.unique_at_interior
/-- info: 'Quant.TriangleCyclicCornerAssignments.edge_seed_near_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicCornerAssignments.edge_seed_near_end
