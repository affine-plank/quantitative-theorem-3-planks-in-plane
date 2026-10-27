/- Explicit finite-vertex families for the one-positive-plank equality case. -/
module

public import Plank.Proofs.Quant.PlanarOnePlankShape
public import Mathlib.Analysis.Convex.Join
public import Plank.Convex.CollinearSections

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarOnePlankVertices

open Set MeasureTheory Topology PlanarQuantitative PlanarOnePlankShape PlanarGapCells

theorem coordinate_injective_on_level (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) :
    ∃ i : Fin 2, ∀ x y : Point, f x = f y → x i = y i → x = y := by
  let A := f.linear ![1,0]
  let B := f.linear ![0,1]
  have hb0 : (fun j : Fin 2 => if (0 : Fin 2) = j then (1 : ℝ) else 0) = ![1,0] := by
    funext j; fin_cases j <;> norm_num
  have hb1 : (fun j : Fin 2 => if (1 : Fin 2) = j then (1 : ℝ) else 0) = ![0,1] := by
    funext j; fin_cases j <;> norm_num
  have hlin (x : Point) : f.linear x = x 0*A+x 1*B := by
    simpa only [Fin.sum_univ_two,hb0,hb1,smul_eq_mul] using f.linear.pi_apply_eq_sum_univ x
  have hform (x : Point) : f x = x 0*A+x 1*B+f 0 := by rw [affine_eval,hlin]
  by_cases hB : B = 0
  · have hA : A ≠ 0 := by
      intro hA
      apply hf
      apply LinearMap.ext
      intro x
      change f.linear x = 0
      rw [hlin,hA,hB,mul_zero,mul_zero,add_zero]
    refine ⟨1,fun x y hxy hi => ?_⟩
    have hp : (x 0-y 0)*A = 0 := by rw [hform x,hform y,hB] at hxy; nlinarith only [hxy]
    have hi0 := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hA)
    funext j
    fin_cases j
    · exact hi0
    · exact hi
  · refine ⟨0,fun x y hxy hi => ?_⟩
    have hp : (x 1-y 1)*B = 0 := by rw [hform x,hform y,hi] at hxy; nlinarith only [hxy]
    have hi1 := sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_right hB)
    funext j
    fin_cases j
    · exact hi
    · exact hi1

/-- Every nonempty compact convex level section in the plane is a segment.
This specializes the dimension-independent collinearity argument. -/
theorem levelSection_eq_segment {K : Set Point} (hK : IsCompact K) (hconv : Convex ℝ K)
    (f : Point →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (t : ℝ)
    (hne : (levelSection K f t).Nonempty) :
    ∃ c ∈ levelSection K f t, ∃ d ∈ levelSection K f t,
      levelSection K f t = segment ℝ c d := by
  exact CollinearSections.levelSection_eq_segment hK hconv (by simp [Point]) f hf t hne

theorem cone_segment_eq_triangle (b c d : Point) :
    cone b (segment ℝ c d) = convexHull ℝ {b,c,d} := by
  rw [cone,convexHull_insert (insert_nonempty c {d}),convexHull_pair,convexJoin_singleton_left]
  exact insert_eq_of_mem (mem_iUnion.mpr ⟨c,mem_iUnion.mpr
    ⟨left_mem_segment ℝ c d,left_mem_segment ℝ b c⟩⟩)

/-- Two closed triangles sharing their base. In an equality configuration
their union is the given convex body. -/
def fourPointBody (a b c d : Point) : Set Point :=
  convexHull ℝ {b,c,d} ∪ convexHull ℝ {a,c,d}

theorem fourPointBody_eq_hull (a b c d : Point)
    (hconv : Convex ℝ (fourPointBody a b c d)) :
    fourPointBody a b c d = convexHull ℝ {a,b,c,d} := by
  apply Subset.antisymm
  · apply union_subset
    · exact convexHull_mono (subset_insert a {b,c,d})
    · apply convexHull_mono
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)
  · apply convexHull_min _ hconv
    simp only [insert_subset_iff,singleton_subset_iff]
    refine ⟨Or.inr (subset_convexHull ℝ _ (by simp)),
      Or.inl (subset_convexHull ℝ _ (by simp)),
      Or.inl (subset_convexHull ℝ _ (by simp)),
      Or.inl (subset_convexHull ℝ _ (by simp))⟩

theorem doubleCone_segment (a b c d : Point) :
    doubleCone a b (segment ℝ c d) = fourPointBody a b c d := by
  rw [doubleCone,cone_segment_eq_triangle,cone_segment_eq_triangle]
  rfl

theorem cone_mono {S T : Set Point} (h : S ⊆ T) (b : Point) : cone b S ⊆ cone b T := by
  rintro x (hx | hx)
  · exact Or.inl hx
  · obtain ⟨z,hzx⟩ := mem_iUnion.mp hx
    obtain ⟨hzS,hxz⟩ := mem_iUnion.mp hzx
    exact mem_cone_of_segment (h hzS) hxz

/-- Complete parameterized one-plank family in normalized coordinates:
two support apices at levels 0 and 1 and two base endpoints at lo/(1-r).
Both necessity and actual-area sufficiency are proved. -/
theorem equality_iff_fourPointBody {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hV : 0 < (volume K).toReal)
    (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (ha : a ∈ K) (hb : b ∈ K)
    (hfa : f a = 1) (hfb : f b = 0) (hf : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (lo r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (volume (K \ {x | lo ≤ f x ∧ f x ≤ lo+r})).toReal = (1-r)^2*(volume K).toReal ↔
      0 ≤ lo ∧ lo+r ≤ 1 ∧ ∃ c ∈ K, ∃ d ∈ K,
        f c = lo/(1-r) ∧ f d = lo/(1-r) ∧ K = fourPointBody a b c d := by
  rw [equality_iff_doubleCone hK hconv hV f a b ha hb hfa hfb hf lo r hr hr1]
  constructor
  · rintro ⟨hlo,hhi,hshape⟩
    let t := lo/(1-r)
    have hq : 0 < 1-r := sub_pos.mpr hr1
    have ht : t ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hlo hq.le,(div_le_one hq).mpr (by linarith only [hhi])⟩
    have hne : (levelSection K f t).Nonempty := by
      refine ⟨b+t • (a-b),hconv.add_smul_sub_mem hb ha ht,?_⟩
      change f (b+t • (a-b)) = t
      rw [normalized_ray f hfb,hfa,mul_one]
    have hn : f.linear ≠ 0 := by
      intro hz
      obtain ⟨v,hv⟩ := f.linear_eq_zero_iff_exists_const.mp hz
      have he : f a = f b := by rw [hv]; rfl
      rw [hfa,hfb] at he
      norm_num at he
    obtain ⟨c,hc,d,hd,hs⟩ := levelSection_eq_segment hK hconv f hn t hne
    refine ⟨hlo,hhi,c,hc.1,d,hd.1,hc.2,hd.2,?_⟩
    rw [hshape,hs,doubleCone_segment]
  · rintro ⟨hlo,hhi,c,hc,d,hd,hfc,hfd,hshape⟩
    refine ⟨hlo,hhi,Subset.antisymm ?_ ?_⟩
    · have hbase : segment ℝ c d ⊆ levelSection K f (lo/(1-r)) := by
        apply (hconv.inter ((convex_singleton (lo/(1-r))).affine_preimage f)).segment_subset
        · exact ⟨hc,hfc⟩
        · exact ⟨hd,hfd⟩
      conv_lhs => rw [hshape,← doubleCone_segment]
      exact union_subset_union (cone_mono hbase b) (cone_mono hbase a)
    · exact union_subset (cone_subset hconv hb inter_subset_left) (cone_subset hconv ha inter_subset_left)

end Plank.PlanarOnePlankVertices

/-- info: 'Plank.PlanarOnePlankVertices.levelSection_eq_segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankVertices.levelSection_eq_segment
/-- info: 'Plank.PlanarOnePlankVertices.equality_iff_fourPointBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarOnePlankVertices.equality_iff_fourPointBody
