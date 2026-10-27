/- A cyclic equality band covers its middle vertex strictly. -/
module
public import Plank.Proofs.Quant.TriangleCyclicGapSupport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicStrictVertices
open Set MeasureTheory Filter TriangleEqualityReductions TriangleCyclicVertices
open TriangleCyclicGapSupport OrdinalArea
open scoped Topology

/-- A sole covering band near a vertex must contain every sufficiently
short segment from that vertex into the body. -/
theorem local_cover_segment (C : Config) (j : Fin 3) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) {v w : ℝ × ℝ} (hvU : v ∈ U)
    (hv : v ∈ stdTriangle.set) (hw : w ∈ stdTriangle.set)
    (hcover : stdTriangle.set ∩ U ⊆ ⋃ i, (C.plank i).set)
    (honly : ∀ i, i ≠ j → v ∉ (C.plank i).set) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ (1-t) • v+t • w ∈ (C.plank j).set := by
  let path := fun t : ℝ => (1-t) • v+t • w
  have hcont : Continuous path := by fun_prop
  have hz : path 0=v := by simp [path]
  have ht : Tendsto path (𝓝 0) (𝓝 v) := by
    simpa only [hz] using hcont.continuousAt.tendsto (x := 0)
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), path t ∈ U := ht.eventually (hU.mem_nhds hvU)
  have havoid : ∀ i, ∀ᶠ t in 𝓝 (0 : ℝ), i ≠ j → path t ∉ (C.plank i).set := by
    intro i
    by_cases hij : i=j
    · exact Eventually.of_forall (fun _ h => False.elim (h hij))
    · have hh := ht.eventually ((Proofs.Quant.isClosed_plank_set (C.plank i)).isOpen_compl.mem_nhds
        (honly i hij))
      exact hh.mono (fun _ h _ => h)
  obtain ⟨ε,hε,hh⟩ := Metric.eventually_nhds_iff.mp (hmem.and (eventually_all.mpr havoid))
  let t := min ε 1/2
  have hm : 0 < min ε 1 := lt_min hε (by norm_num)
  have ht0 : 0 < t := div_pos hm (by norm_num)
  have htm : t < min ε 1 := by dsimp only [t]; linarith only [hm]
  have ht1 : t < 1 := htm.trans_le (min_le_right _ _)
  have htε : dist t 0 < ε := by
    rw [Real.dist_eq,sub_zero,abs_of_pos ht0]
    exact htm.trans_le (min_le_left _ _)
  have hc := hh htε
  have hT : path t ∈ stdTriangle.set :=
    Proofs.Transport.convex_triangle stdTriangle hv hw
      (sub_nonneg.mpr ht1.le) ht0.le (by ring)
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover ⟨hT,hc.1⟩)
  have hij : i=j := by by_contra hn; exact hc.2 i hn hi
  exact ⟨t,ht0,ht1,hij ▸ hi⟩

/-- At a strict middle vertex, local coverage by a single band forces
strict containment between its two boundary lines. -/
theorem strict_of_local_cover (C : Config) (j : Fin 3) (U : Set (ℝ × ℝ))
    (hU : IsOpen U) {v wL wH : ℝ × ℝ} (hvU : v ∈ U)
    (hv : v ∈ stdTriangle.set) (hwL : wL ∈ stdTriangle.set) (hwH : wH ∈ stdTriangle.set)
    (hcover : stdTriangle.set ∩ U ⊆ ⋃ i, (C.plank i).set)
    (honly : ∀ i, i ≠ j → v ∉ (C.plank i).set)
    (hl : dot (C.plank j).u wL < dot (C.plank j).u v)
    (hh : dot (C.plank j).u v < dot (C.plank j).u wH) :
    (C.plank j).lo < dot (C.plank j).u v ∧ dot (C.plank j).u v < (C.plank j).hi := by
  obtain ⟨t,ht,_,hL⟩ := local_cover_segment C j U hU hvU hv hwL hcover honly
  obtain ⟨s,hs,_,hH⟩ := local_cover_segment C j U hU hvU hv hwH hcover honly
  have hdot (r : ℝ) (w : ℝ × ℝ) :
      dot (C.plank j).u ((1-r) • v+r • w) =
        (1-r)*dot (C.plank j).u v+r*dot (C.plank j).u w := by
    dsimp [dot]; ring
  have hL' := hL.1
  have hH' := hH.2
  rw [hdot] at hL' hH'
  constructor
  · nlinarith only [hL',mul_pos ht (sub_pos.mpr hl)]
  · nlinarith only [hH',mul_pos hs (sub_pos.mpr hh)]

/-- The middle vertices are in the interiors of their own equality bands;
all six middle-vertex endpoint contacts are excluded. -/
theorem abc_strict_middle (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    ((C.plank 0).lo < b ∧ b < (C.plank 0).hi) ∧
    ((C.plank 1).lo < a ∧ a < (C.plank 1).hi) ∧
    ((C.plank 2).lo < 0 ∧ 0 < (C.plank 2).hi) := by
  have hi := TriangleEndpointPositions.abc_internal C hb ha hc hu0 hu1 hu2 hp hδ he
  have hr : ∀ i, 0 < widths C i := by
    intro i
    simpa only [Config.relW,Plank.relWidth,
      BalancedArea.abc_width_one C hb ha hc hu0 hu1 hu2,div_one,widths] using hp i
  have hsole0 : ∀ i, i ≠ 0 → vertex 2 ∉ (C.plank i).set := by
    intro i hn hm
    fin_cases i
    · exact hn rfl
    · have hh : dot (C.plank 1).u (0,1) ≤ (C.plank 1).hi := hm.2
      rw [hu1] at hh
      norm_num [dot] at hh
      linarith only [hh,hi.2.1.2]
    · have hh : (C.plank 2).lo ≤ dot (C.plank 2).u (0,1) := hm.1
      rw [hu2] at hh
      norm_num [dot] at hh
      linarith only [hh,hi.2.2.1]
  have hsole1 : ∀ i, i ≠ 1 → vertex 1 ∉ (C.plank i).set := by
    intro i hn hm
    fin_cases i
    · have hh : dot (C.plank 0).u (1,0) ≤ (C.plank 0).hi := hm.2
      rw [hu0] at hh
      norm_num [dot] at hh
      linarith only [hh,hi.1.2]
    · exact hn rfl
    · have hh : dot (C.plank 2).u (1,0) ≤ (C.plank 2).hi := hm.2
      rw [hu2] at hh
      norm_num [dot] at hh
      linarith only [hh,hi.2.2.2]
  have hsole2 : ∀ i, i ≠ 2 → vertex 0 ∉ (C.plank i).set := by
    intro i hn hm
    fin_cases i
    · have hh : (C.plank 0).lo ≤ dot (C.plank 0).u (0,0) := hm.1
      norm_num [dot] at hh
      linarith only [hh,hi.1.1]
    · have hh : (C.plank 1).lo ≤ dot (C.plank 1).u (0,0) := hm.1
      norm_num [dot] at hh
      linarith only [hh,hi.2.1.1]
    · exact hn rfl
  have h0 := strict_of_local_cover C 0 (corner C 2) (corner_open C 2)
    (corner_contains_vertex C hr 2) (vertex_mem 2) (vertex_mem 0) (vertex_mem 1)
    (corner_covered C hb ha hc hu0 hu1 hu2 hδ he 2) hsole0
    (by simpa [vertex,hu0,dot] using hb.1)
    (by simpa [vertex,hu0,dot] using hb.2)
  have h1 := strict_of_local_cover C 1 (corner C 1) (corner_open C 1)
    (corner_contains_vertex C hr 1) (vertex_mem 1) (vertex_mem 0) (vertex_mem 2)
    (corner_covered C hb ha hc hu0 hu1 hu2 hδ he 1) hsole1
    (by simpa [vertex,hu1,dot] using ha.1)
    (by simpa [vertex,hu1,dot] using ha.2)
  have h2 := strict_of_local_cover C 2 (corner C 0) (corner_open C 0)
    (corner_contains_vertex C hr 0) (vertex_mem 0) (vertex_mem 2) (vertex_mem 1)
    (corner_covered C hb ha hc hu0 hu1 hu2 hδ he 0) hsole2
    (by simpa [vertex,hu2,dot] using sub_neg.mpr hc.2)
    (by simpa [vertex,hu2,dot] using hc.1)
  simpa [vertex,hu0,hu1,hu2,dot] using And.intro h0 (And.intro h1 h2)

end Quant.TriangleCyclicStrictVertices

/-- info: 'Quant.TriangleCyclicStrictVertices.strict_of_local_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicStrictVertices.strict_of_local_cover
/-- info: 'Quant.TriangleCyclicStrictVertices.abc_strict_middle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicStrictVertices.abc_strict_middle
