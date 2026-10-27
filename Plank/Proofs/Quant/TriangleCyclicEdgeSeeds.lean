/- Every triangle edge contains an uncovered point at cyclic equality. -/
module
public import Plank.Proofs.Quant.TriangleCyclicStrictVertices
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicEdgeSeeds
open Set MeasureTheory Filter CommonVertex OrdinalArea CyclicArea
open CyclicTranslationEquality TriangleEqualityReductions TriangleCyclicVertices
open scoped Topology

theorem segment_in_open {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {z : ℝ × ℝ} (hz : z ∈ U) (w : ℝ × ℝ) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1-t) • z+t • w ∈ U := by
  let path := fun t : ℝ => (1-t) • z+t • w
  have hcont : Continuous path := by fun_prop
  have hzero : path 0=z := by simp [path]
  have ht : Tendsto path (𝓝 0) (𝓝 z) := by
    simpa only [hzero] using hcont.continuousAt.tendsto (x := 0)
  obtain ⟨ε,hε,hh⟩ := Metric.eventually_nhds_iff.mp (ht.eventually (hU.mem_nhds hz))
  let t := min ε 1/2
  have hm : 0 < min ε 1 := lt_min hε (by norm_num)
  have ht0 : 0 < t := div_pos hm (by norm_num)
  have htm : t < min ε 1 := by dsimp only [t]; linarith only [hm]
  refine ⟨t,ht0,htm.trans_le (min_le_right _ _),hh ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_pos ht0]
  exact htm.trans_le (min_le_left _ _)

/-- A strict gap cell cannot touch a new core support line in the interior
of the corresponding halfplane of the original triangle. -/
theorem strict_core (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1)) (hδ : 0 < C.deficit) (he : Equality C)
    (s : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ stdTriangle.set)
    (hs : z ∈ exteriorCells C s) :
    (0 < z.1 → (translations C s).1 < z.1) ∧
    (0 < z.2 → (translations C s).2 < z.2) ∧
    (z.1+z.2 < 1 → z.1+z.2 < C.deficit+(translations C s).1+(translations C s).2) := by
  have ho : IsOpen (exteriorCells C s) := TriangleTranslationBoundary.exterior_open C s
  obtain ⟨t,ht,ht1,htU⟩ := segment_in_open ho hs (vertex 0)
  have htT : (1-t) • z+t • vertex 0 ∈ stdTriangle.set :=
    Proofs.Transport.convex_triangle stdTriangle hz (vertex_mem 0)
      (sub_nonneg.mpr ht1.le) ht.le (by ring)
  have hA := cell_core C hb ha hc hu0 hu1 hu2 hδ he s htT htU
  change 0 ≤ ((1-t)*z.1+t*0)-(translations C s).1 ∧
    0 ≤ ((1-t)*z.2+t*0)-(translations C s).2 ∧ _ at hA
  obtain ⟨r,hr,hr1,hrU⟩ := segment_in_open ho hs (vertex 1)
  have hrT : (1-r) • z+r • vertex 1 ∈ stdTriangle.set :=
    Proofs.Transport.convex_triangle stdTriangle hz (vertex_mem 1)
      (sub_nonneg.mpr hr1.le) hr.le (by ring)
  have hB := (cell_core C hb ha hc hu0 hu1 hu2 hδ he s hrT hrU).2.2
  change (((1-r)*z.1+r*1)-(translations C s).1)+
    (((1-r)*z.2+r*0)-(translations C s).2) ≤ C.deficit at hB
  refine ⟨fun hx => ?_,fun hy => ?_,fun hsum => ?_⟩
  · nlinarith only [hA.1,mul_pos ht hx]
  · nlinarith only [hA.2.1,mul_pos ht hy]
  · nlinarith only [hB,mul_pos hr (sub_pos.mpr hsum)]

def seed (d : ℝ) (j : Fin 3) (t : ℝ) : ℝ × ℝ :=
  ![(t,0),(0,t),(t,d-t)] j

def slope (u : ℝ × ℝ) : Fin 3 → ℝ := ![u.1,u.2,u.1-u.2]

def onEdge (j : Fin 3) (z : ℝ × ℝ) : Prop :=
  ![z.2=0,z.1=0,z.1+z.2=1] j

theorem seed_mem (d t : ℝ) (ht : 0 ≤ t ∧ t ≤ d) (j : Fin 3) :
    seed d j t ∈ RowDeletion.triangle d := by
  fin_cases j
  · change 0 ≤ t ∧ 0 ≤ 0 ∧ t+0 ≤ d
    exact ⟨ht.1,le_rfl,by linarith only [ht.2]⟩
  · change 0 ≤ 0 ∧ 0 ≤ t ∧ 0+t ≤ d
    exact ⟨le_rfl,ht.1,by linarith only [ht.2]⟩
  · change 0 ≤ t ∧ 0 ≤ d-t ∧ t+(d-t) ≤ d
    exact ⟨ht.1,sub_nonneg.mpr ht.2,by linarith⟩

theorem seed_dot (u v : ℝ × ℝ) (d t : ℝ) (j : Fin 3) :
    dot u (seed d j t+v)=slope u j*t+dot u (seed d j 0+v) := by
  fin_cases j <;> dsimp [seed,slope,dot] <;> ring

theorem exists_strict_seed (C : Config) (j : Fin 3) (hδ : 0 < C.deficit)
    (hn : ∀ i, slope (C.plank i).u j ≠ 0)
    (hw : ∀ z ∈ RowDeletion.triangle C.deficit, ∃ s,
      z+translations C s ∈ Plank.LinearBands.weakCell
        (fun i => dot (C.plank i).u) (fun i => (C.plank i).lo)
        (fun i => (C.plank i).hi) s) :
    ∃ t : ℝ, 0 < t ∧ t < C.deficit ∧ ∃ s,
      seed C.deficit j t+translations C s ∈ exteriorCells C s := by
  classical
  let bad : Finset ℝ := Finset.univ.image
    (fun q : Finset (Fin 3) × Fin 3 =>
      ((if q.2 ∈ q.1 then (C.plank q.2).hi else (C.plank q.2).lo)-
        dot (C.plank q.2).u (seed C.deficit j 0+translations C q.1))/
        slope (C.plank q.2).u j)
  obtain ⟨t,ht,hnot⟩ := (Set.Ioo_infinite hδ).exists_notMem_finite bad.finite_toSet
  obtain ⟨s,hs⟩ := hw (seed C.deficit j t) (seed_mem _ _ ⟨ht.1.le,ht.2.le⟩ j)
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

theorem every_edge_has_gap (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1)) (hδ : 0 < C.deficit) (he : Equality C)
    (j : Fin 3) : ∃ z ∈ C.uncovered, onEdge j z := by
  have hnorm : ∀ i, (C.plank i).u= ![(1,b),(a,1),(c,c-1)] i := by
    intro i
    fin_cases i
    · exact hu0
    · exact hu1
    · exact hu2
  have hn : ∀ i, slope (C.plank i).u j ≠ 0 := by
    intro i
    rw [hnorm]
    fin_cases i <;> fin_cases j <;> dsimp [slope] <;>
      intro hh <;> linarith only [hh,hb.1,hb.2,ha.1,ha.2,hc.1,hc.2]
  have hno := ((equality_iff_partition C hb ha hc hu0 hu1 hu2 hδ).mp he).1
  obtain ⟨t,ht0,htδ,s,hs⟩ := exists_strict_seed C j hδ hn
    (weak_assignments_of_no_bad_seed C hb ha hc hu0 hu1 hu2 hno)
  let z := seed C.deficit j t+translations C s
  have hzT : z ∈ stdTriangle.set := by
    apply OrdinalArea.translated_mem_triangle (widths C)
      (fun i => sub_nonneg.mpr (C.plank i).lo_le_hi) s
    rw [← CyclicArea.deficit_eq C hb ha hc hu0 hu1 hu2]
    exact seed_mem _ _ ⟨ht0.le,htδ.le⟩ j
  refine ⟨z,⟨hzT,Plank.LinearBands.strictCell_subset_gap _ _ _ s hs⟩,?_⟩
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

end Quant.TriangleCyclicEdgeSeeds

/-- info: 'Quant.TriangleCyclicEdgeSeeds.every_edge_has_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicEdgeSeeds.every_edge_has_gap
