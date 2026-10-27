/- Boundary constraints on the seed partition at triangle equality. -/
module
public import Plank.Proofs.Quant.TriangleTranslationBoundary

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleSourceBoundary
open Set MeasureTheory Function CommonVertex TranslationEquality
open CommonVertexTranslationEquality TriangleTranslationBoundary CommonMiddleNecessity
open scoped BigOperators Topology

/-- An affine functional minimized on a relatively open neighborhood in a
convex set is minimized on the whole convex set. -/
theorem affine_minimum_open {K U : Set (ℝ × ℝ)} (hK : Convex ℝ K)
    (hU : IsOpen U) (f : (ℝ × ℝ) →ᵃ[ℝ] ℝ) {z : ℝ × ℝ}
    (hz : z ∈ K) (hzu : z ∈ U)
    (hb : ∀ x ∈ K, x ∈ U → f z ≤ f x) : ∀ x ∈ K, f z ≤ f x := by
  intro x hx
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), AffineMap.lineMap z x t ∈ U :=
    (AffineMap.lineMap_continuous.tendsto' _ _ (AffineMap.lineMap_apply_zero z x)).eventually_mem
      (hU.mem_nhds hzu)
  have hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), AffineMap.lineMap z x t ∈ U :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨t,htU,ht⟩ := (hright.and (Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))).exists
  have hh := hb _ (hK.lineMap_mem hz hx ⟨ht.1.le,ht.2⟩) htU
  rw [f.apply_lineMap,AffineMap.lineMap_apply_ring] at hh
  nlinarith only [hh,ht.1]

theorem core_convex (d : ℝ) : Convex ℝ (RowDeletion.triangle d) := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ a*x.1+b*y.1 ∧ 0 ≤ a*x.2+b*y.2 ∧
    (a*x.1+b*y.1)+(a*x.2+b*y.2) ≤ d
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1),?_⟩
  have hh := add_le_add (mul_le_mul_of_nonneg_left hx.2.2 ha)
    (mul_le_mul_of_nonneg_left hy.2.2 hb)
  rw [← add_mul,hab,one_mul] at hh
  nlinarith only [hh]

theorem core_interior_nonempty {d : ℝ} (hd : 0 < d) :
    (interior (RowDeletion.triangle d)).Nonempty := by
  let U : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ 0 < z.2 ∧ z.1+z.2 < d}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hsub : U ⊆ RowDeletion.triangle d := fun _ hz => ⟨hz.1.le,hz.2.1.le,hz.2.2.le⟩
  refine ⟨(d/4,d/4),interior_maximal hsub hU ?_⟩
  change 0 < d/4 ∧ 0 < d/4 ∧ d/4+d/4 < d
  exact ⟨by linarith,by linarith,by linarith⟩

/-- Strict source assignments are unique even on the boundary of the core.
An overlap at a boundary point would extend to positive area inside it. -/
theorem source_unique (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C)
    (s t : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ RowDeletion.triangle C.deficit)
    (hs : z+shift (steps C) s ∈ exteriorCells C s)
    (ht : z+shift (steps C) t ∈ exteriorCells C t) : s=t := by
  classical
  by_contra hne
  let U : Set (ℝ × ℝ) :=
    ((fun x => x+shift (steps C) s) ⁻¹' exteriorCells C s) ∩
    ((fun x => x+shift (steps C) t) ⁻¹' exteriorCells C t)
  have hU : IsOpen U := ((exterior_open C s).preimage (by fun_prop)).inter
    ((exterior_open C t).preimage (by fun_prop))
  have hnull : volume (RowDeletion.triangle C.deficit \ Uᶜ) = 0 := by
    have hd := ((equality_iff_partition C hu hδ).mp he).1 hne
    apply measure_mono_null _ hd
    intro x hx
    have hm : x ∈ U := not_not.mp hx.2
    exact ⟨⟨hx.1,hm.1⟩,⟨hx.1,hm.2⟩⟩
  have hcover := subset_of_null_sdiff (triangle_closed C.deficit) (core_convex C.deficit)
    (core_interior_nonempty hδ) hU.isClosed_compl hnull
  exact hcover hz ⟨hs,ht⟩

/-- A strict source cell on the left or bottom edge can use no escape step
transverse to that edge. On the far edge it must use the entire budget. -/
theorem source_faces (C : Config)
    (hu : ∀ i, 0 ≤ (C.plank i).u.1 ∧ 0 ≤ (C.plank i).u.2)
    (hδ : 0 < C.deficit) (he : TriangleEqualityReductions.Equality C)
    (s : Finset (Fin 3)) {z : ℝ × ℝ} (hz : z ∈ RowDeletion.triangle C.deficit)
    (hs : z+shift (steps C) s ∈ exteriorCells C s) :
    (z.1=0 → (shift (steps C) s).1=0) ∧
    (z.2=0 → (shift (steps C) s).2=0) ∧
    (z.1+z.2=C.deficit → (∑ i ∈ s, C.relW i)=C.sumRelW) := by
  have hT : z+shift (steps C) s ∈ stdTriangle.set := by
    apply shifted_mem_triangle (steps C) (steps_nonneg C) s
    simpa only [steps_cost,Config.deficit,Config.sumRelW] using hz
  have hshift : (shift (steps C) s).1+(shift (steps C) s).2 = ∑ i ∈ s, C.relW i := by
    rw [shift_fst,shift_snd,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => steps_cost C i)
  have hconv : Convex ℝ stdTriangle.set := by
    rw [Proofs.Quant.stdTriangle_set_eq]
    exact core_convex 1
  have hO : (0,0) ∈ stdTriangle.set := by rw [Proofs.Quant.stdTriangle_set_eq]; norm_num
  have hX : (1,0) ∈ stdTriangle.set := by rw [Proofs.Quant.stdTriangle_set_eq]; norm_num
  have hb (x : ℝ × ℝ) (hx : x ∈ stdTriangle.set) (hxcell : x ∈ exteriorCells C s) :=
    common_vertex_cell_inequalities C hu hδ he s hx hxcell
  refine ⟨?_,?_,?_⟩
  · intro hzx
    have hm := affine_minimum_open hconv (exterior_open C s)
      (LinearMap.fst ℝ ℝ ℝ).toAffineMap hT hs (fun x hx hxcell => by
        change z.1+(shift (steps C) s).1 ≤ x.1
        simpa only [hzx,zero_add] using (hb x hx hxcell).1) (0,0) hO
    have hp : 0 ≤ (shift (steps C) s).1 := by
      rw [shift_fst]; exact Finset.sum_nonneg (fun i _ => (steps_nonneg C i).1)
    change z.1+(shift (steps C) s).1 ≤ 0 at hm
    linarith only [hm,hp,hzx]
  · intro hzy
    have hm := affine_minimum_open hconv (exterior_open C s)
      (LinearMap.snd ℝ ℝ ℝ).toAffineMap hT hs (fun x hx hxcell => by
        change z.2+(shift (steps C) s).2 ≤ x.2
        simpa only [hzy,zero_add] using (hb x hx hxcell).2.1) (0,0) hO
    have hp : 0 ≤ (shift (steps C) s).2 := by
      rw [shift_snd]; exact Finset.sum_nonneg (fun i _ => (steps_nonneg C i).2)
    change z.2+(shift (steps C) s).2 ≤ 0 at hm
    linarith only [hm,hp,hzy]
  · intro hzs
    have hm := affine_minimum_open hconv (exterior_open C s)
      (-(LinearMap.fst ℝ ℝ ℝ+LinearMap.snd ℝ ℝ ℝ)).toAffineMap hT hs
      (fun x hx hxcell => by
        change -((z.1+(shift (steps C) s).1)+(z.2+(shift (steps C) s).2)) ≤ -(x.1+x.2)
        have hh := (hb x hx hxcell).2.2
        linarith only [hh,hshift,hzs]) (1,0) hX
    change -((z.1+(shift (steps C) s).1)+(z.2+(shift (steps C) s).2)) ≤ -(1+0) at hm
    have hsum : (∑ i ∈ s, C.relW i) ≤ C.sumRelW :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => relWidth_nonneg (C.plank i))
    dsimp only [Config.deficit] at hzs
    linarith only [hm,hshift,hzs,hsum]

end Quant.TriangleSourceBoundary

/-- info: 'Quant.TriangleSourceBoundary.source_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleSourceBoundary.source_unique
/-- info: 'Quant.TriangleSourceBoundary.source_faces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleSourceBoundary.source_faces
