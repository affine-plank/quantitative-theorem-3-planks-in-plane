/- A convex body admitting no enlargement inside a covered region has a
boundary segment from each strictly covered boundary point to that region's
exterior. No polyhedral or smoothness assumption is used. -/
module
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Sequences
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ConvexBoundaryRuling

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K U : Set E}

theorem hull_insert_eq (hc : Convex ℝ K) (hne : K.Nonempty) (p : E) :
    convexHull ℝ (insert p K)=
      (fun q : ℝ × E => (1-q.1) • p+q.1 • q.2) '' (Icc (0 : ℝ) 1 ×ˢ K) := by
  rw [convexHull_insert hne,hc.convexHull_eq]
  ext z
  simp only [mem_convexJoin,mem_singleton_iff,exists_eq_left,
    segment_eq_image,mem_image,mem_prod]
  constructor
  · rintro ⟨y,hy,t,ht,rfl⟩
    exact ⟨(t,y),⟨ht,hy⟩,rfl⟩
  · rintro ⟨⟨t,y⟩,⟨ht,hy⟩,rfl⟩
    exact ⟨y,hy,t,ht,rfl⟩

theorem compact_insert (hK : IsCompact K) (hc : Convex ℝ K)
    (hne : K.Nonempty) (p : E) : IsCompact (convexHull ℝ (insert p K)) := by
  rw [hull_insert_eq hc hne]
  exact (isCompact_Icc.prod hK).image (by fun_prop)

/-- Every point between the adjoined point and a newly added point is
outside the old body. Strict separation avoids any boundary regularity. -/
theorem segment_outside (hK : IsClosed K) (hc : Convex ℝ K)
    {p z : E} (hz : z∈convexHull ℝ (insert p K)) (hzK : z∉K) :
    segment ℝ p z⊆Kᶜ := by
  obtain ⟨L,r,hL,hr⟩ := geometric_hahn_banach_closed_point hc hK hzK
  have hp : r<L p := by
    by_contra! hp
    have hh : convexHull ℝ (insert p K)⊆{y | L y≤r} :=
      convexHull_min (insert_subset hp (fun y hy => (hL y hy).le))
        ((convex_Iic r).linear_preimage L.toLinearMap)
    exact (not_le_of_gt hr) (hh hz)
  have hh : segment ℝ p z⊆{y | r<L y} :=
    ((convex_Ioi r).linear_preimage L.toLinearMap).segment_subset hp hr
  intro y hy hyK
  exact (not_lt_of_ge (hL y hyK).le) (hh hy)

/-- If every point enlargement adds something outside U, then each boundary
point in the interior of U is joined along the body's boundary to a point
outside the interior of U. The endpoint may lie on the boundary of U. -/
theorem exists_boundary_segment (hK : IsCompact K) (hc : Convex ℝ K)
    (hmax : ∀ p∉K,∃ z∈convexHull ℝ (insert p K),z∉K ∧ z∉U)
    {x : E} (hx : x∈frontier K) (hxU : x∈interior U) :
    ∃ z∈frontier K,z∉interior U ∧ x≠z ∧ segment ℝ x z⊆frontier K := by
  have hxK : x∈K := hK.isClosed.closure_eq ▸ hx.1
  have hne : K.Nonempty := ⟨x,hxK⟩
  have hxc : x∈closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  obtain ⟨p,hp,hpt⟩ := mem_closure_iff_seq_limit.mp hxc
  choose z hz hzK hzU using fun n => hmax (p n) (hp n)
  have hrep (n : ℕ) : ∃ q∈Icc (0 : ℝ) 1 ×ˢ K,
      (1-q.1) • p n+q.1 • q.2=z n := by
    have hh := hz n
    rw [hull_insert_eq hc hne] at hh
    exact hh
  choose q hq he using hrep
  obtain ⟨q₀,hq₀,φ,hφ,hqt⟩ := (isCompact_Icc.prod hK).tendsto_subseq hq
  let z₀ : E := (1-q₀.1) • x+q₀.1 • q₀.2
  have hz₀K : z₀∈K := hc hxK hq₀.2 (sub_nonneg.mpr hq₀.1.2) hq₀.1.1 (by ring)
  have hps : Tendsto (p ∘ φ) atTop (𝓝 x) := hpt.comp hφ.tendsto_atTop
  have hzs : Tendsto (z ∘ φ) atTop (𝓝 z₀) := by
    have ht₁ := (continuous_fst.tendsto q₀).comp hqt
    have ht₂ := (continuous_snd.tendsto q₀).comp hqt
    have ht := (((tendsto_const_nhds (x := (1 : ℝ))).sub ht₁).smul hps).add
      (ht₁.smul ht₂)
    simpa only [Function.comp_def,he] using ht
  have hz₀U : z₀∉interior U := isOpen_interior.isClosed_compl.mem_of_tendsto hzs
    (Eventually.of_forall fun n hn => hzU (φ n) (interior_subset hn))
  have hseg : segment ℝ x z₀⊆frontier K := by
    rintro w ⟨a,b,ha,hb,hab,rfl⟩
    rw [hK.isClosed.frontier_eq]
    refine ⟨hc hxK hz₀K ha hb hab,?_⟩
    have ht := (hps.const_smul a).add (hzs.const_smul b)
    exact isOpen_interior.isClosed_compl.mem_of_tendsto ht
      (Eventually.of_forall fun n hn =>
        segment_outside hK.isClosed hc (hz (φ n)) (hzK (φ n))
          ⟨a,b,ha,hb,hab,rfl⟩ (interior_subset hn))
  exact ⟨z₀,hseg (right_mem_segment _ _ _),hz₀U,
    (fun h => hz₀U (h ▸ hxU)),hseg⟩

end Plank.ConvexBoundaryRuling
