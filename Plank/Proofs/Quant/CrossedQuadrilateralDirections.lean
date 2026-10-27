/- Direction rigidity for one-window equality on a genuine quadrilateral. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralAffine
public import Plank.Proofs.Quant.PlanarOnePlankClassification
public import Plank.Proofs.Quant.PlanarParallelTransport
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Data.Set.Card

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralDirections
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

private theorem extreme_of_unique_max {K : Set Point} (f : Point →ₗ[ℝ] ℝ)
    (v : Point) (hv : v ∈ K) (hmax : ∀ z ∈ K, f z ≤ f v)
    (hunique : ∀ z ∈ K, f z = f v → z = v) : v ∈ K.extremePoints ℝ := by
  refine ⟨hv,fun x hx y hy hseg => hunique x hx ?_⟩
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hh := congrArg f he
  simp only [map_add,map_smul,smul_eq_mul] at hh
  have hfx := hmax x hx
  have hfy := hmax y hy
  apply le_antisymm hfx
  apply le_of_not_gt
  intro hlt
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left hfy hb.le
  have h₃ := congrArg (fun t : ℝ => t*f v) hab
  nlinarith only [hh,h₁,h₂,h₃]

theorem x_ratio_le (S : Shape) (i : Bool) {z : Point} (hz : z ∈ S.body) :
    z.1/S.X i ≤ 1 := by
  by_cases hy : 0 ≤ z.2
  · have h := body_support S i true hz
    have hn := div_nonneg hy S.hb.le
    simp only [Shape.Y,if_true] at h
    linarith
  · have h := body_support S i false hz
    have hn := div_nonneg_of_nonpos (le_of_not_ge hy) (neg_nonpos.mpr S.hd.le)
    simp only [Shape.Y,Bool.false_eq_true,if_false] at h
    linarith

theorem y_ratio_le (S : Shape) (j : Bool) {z : Point} (hz : z ∈ S.body) :
    z.2/S.Y j ≤ 1 := by
  by_cases hx : 0 ≤ z.1
  · have h := body_support S true j hz
    have hn := div_nonneg hx S.ha.le
    simp only [Shape.X,if_true] at h
    linarith
  · have h := body_support S false j hz
    have hn := div_nonneg_of_nonpos (le_of_not_ge hx) (neg_nonpos.mpr S.hc.le)
    simp only [Shape.X,Bool.false_eq_true,if_false] at h
    linarith

theorem x_ratio_eq_one (S : Shape) (i : Bool) {z : Point} (hz : z ∈ S.body)
    (he : z.1/S.X i = 1) : z = (S.X i,0) := by
  have hu := body_support S i true hz
  have hl := body_support S i false hz
  simp only [he,Shape.Y,if_true,Bool.false_eq_true,if_false] at hu hl
  have hyu : z.2 ≤ 0 := by
    have hh : z.2/S.b ≤ 0 := by linarith
    simpa using (div_le_iff₀ S.hb).mp hh
  have hyl : 0 ≤ z.2 := by
    have hh : z.2/(-S.d) ≤ 0 := by linarith
    simpa using (div_le_iff_of_neg (neg_neg_of_pos S.hd)).mp hh
  exact Prod.ext (by simpa using (div_eq_iff (S.X_ne i)).mp he) (le_antisymm hyu hyl)

theorem y_ratio_eq_one (S : Shape) (j : Bool) {z : Point} (hz : z ∈ S.body)
    (he : z.2/S.Y j = 1) : z = (0,S.Y j) := by
  have hu := body_support S true j hz
  have hl := body_support S false j hz
  simp only [he,Shape.X,if_true,Bool.false_eq_true,if_false] at hu hl
  have hxu : z.1 ≤ 0 := by
    have hh : z.1/S.a ≤ 0 := by linarith
    simpa using (div_le_iff₀ S.ha).mp hh
  have hxl : 0 ≤ z.1 := by
    have hh : z.1/(-S.c) ≤ 0 := by linarith
    simpa using (div_le_iff_of_neg (neg_neg_of_pos S.hc)).mp hh
  exact Prod.ext (le_antisymm hxu hxl) (by simpa using (div_eq_iff (S.Y_ne j)).mp he)

theorem vertexX_extreme (S : Shape) (i : Bool) : (S.X i,0) ∈ S.body.extremePoints ℝ := by
  let f : Point →ₗ[ℝ] ℝ := (S.X i)⁻¹ • LinearMap.fst ℝ ℝ ℝ
  have hf (z : Point) : f z = z.1/S.X i := by simp [f,div_eq_mul_inv,mul_comm]
  apply extreme_of_unique_max f _ (vertexX_mem S i)
  · intro z hz
    simpa [hf,S.X_ne i] using x_ratio_le S i hz
  · intro z hz he
    apply x_ratio_eq_one S i hz
    simpa [hf,S.X_ne i] using he

theorem vertexY_extreme (S : Shape) (j : Bool) : (0,S.Y j) ∈ S.body.extremePoints ℝ := by
  let f : Point →ₗ[ℝ] ℝ := (S.Y j)⁻¹ • LinearMap.snd ℝ ℝ ℝ
  have hf (z : Point) : f z = z.2/S.Y j := by simp [f,div_eq_mul_inv,mul_comm]
  apply extreme_of_unique_max f _ (vertexY_mem S j)
  · intro z hz
    simpa [hf,S.Y_ne j] using y_ratio_le S j hz
  · intro z hz he
    apply y_ratio_eq_one S j hz
    simpa [hf,S.Y_ne j] using he

theorem vertices_extreme (S : Shape) : S.vertices ⊆ S.body.extremePoints ℝ := by
  rintro z (rfl | rfl | rfl | rfl)
  · exact vertexX_extreme S true
  · exact vertexY_extreme S true
  · exact vertexX_extreme S false
  · exact vertexY_extreme S false

theorem vertices_card (S : Shape) : S.vertices.ncard = 4 := by
  have ha : S.a ≠ 0 := S.ha.ne'
  have hb : S.b ≠ 0 := S.hb.ne'
  have hc : S.c ≠ 0 := S.hc.ne'
  have hd : S.d ≠ 0 := S.hd.ne'
  have hac : S.a ≠ -S.c := by linarith [S.ha,S.hc]
  have hbd : S.b ≠ -S.d := by linarith [S.hb,S.hd]
  simp [Shape.vertices,Prod.mk.injEq,ha,hb,hc,hd,hac,hbd]

/-- Four generators of this genuine quadrilateral must be its four vertices. -/
theorem vertices_eq_of_four_hull (S : Shape) (a b c d : Point)
    (he : S.body = convexHull ℝ {a,b,c,d}) : S.vertices = {a,b,c,d} := by
  have hs : S.vertices ⊆ ({a,b,c,d} : Set Point) := by
    intro z hz
    have hh := vertices_extreme S hz
    rw [he] at hh
    exact extremePoints_convexHull_subset hh
  apply Set.eq_of_subset_of_ncard_le hs
  rw [vertices_card]
  have h₁ := Set.ncard_insert_le a ({b,c,d} : Set Point)
  have h₂ := Set.ncard_insert_le b ({c,d} : Set Point)
  have h₃ := Set.ncard_insert_le c ({d} : Set Point)
  simp only [Set.ncard_singleton] at h₃
  omega


private theorem four_distinct (a b c d : Point) (h : ({a,b,c,d} : Set Point).ncard = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  classical
  simp only [Set.ncard_insert_eq_ite (s := ({b,c,d} : Set Point)) (by simp),
    Set.ncard_insert_eq_ite (s := ({c,d} : Set Point)) (by simp),
    Set.ncard_insert_eq_ite (s := ({d} : Set Point)) (by simp),Set.ncard_singleton] at h
  split_ifs at h <;> simp_all

/-- A double-cone base for this genuine quadrilateral lies on a diagonal:
its common affine level can have only one of the two diagonal normals. -/
theorem support_pair_direction (S : Shape) (u a b c d : Point)
    (he : S.vertices = {a,b,c,d})
    (hmax : ∀ z ∈ S.vertices, dot u z ≤ dot u a)
    (hmin : ∀ z ∈ S.vertices, dot u b ≤ dot u z)
    (hlevel : dot u c = dot u d) : u.1 = 0 ∨ u.2 = 0 := by
  have hncard : ({a,b,c,d} : Set Point).ncard = 4 := he ▸ vertices_card S
  have hdist := four_distinct a b c d hncard
  have ha : a ∈ S.vertices := by rw [he]; simp
  have hb : b ∈ S.vertices := by rw [he]; simp
  have hc : c ∈ S.vertices := by rw [he]; simp
  have hd : d ∈ S.vertices := by rw [he]; simp
  have hmax₀ := hmax (S.a,0) (by simp [Shape.vertices])
  have hmax₁ := hmax (0,S.b) (by simp [Shape.vertices])
  have hmax₂ := hmax (-S.c,0) (by simp [Shape.vertices])
  have hmax₃ := hmax (0,-S.d) (by simp [Shape.vertices])
  have hmin₀ := hmin (S.a,0) (by simp [Shape.vertices])
  have hmin₁ := hmin (0,S.b) (by simp [Shape.vertices])
  have hmin₂ := hmin (-S.c,0) (by simp [Shape.vertices])
  have hmin₃ := hmin (0,-S.d) (by simp [Shape.vertices])
  by_contra hn
  push Not at hn
  have hxs : (0 < u.1*S.a ∧ u.1*(-S.c) < 0) ∨
      (u.1*S.a < 0 ∧ 0 < u.1*(-S.c)) := by
    rcases lt_or_gt_of_ne hn.1 with h | h
    · exact Or.inr ⟨mul_neg_of_neg_of_pos h S.ha,mul_pos_of_neg_of_neg h (neg_neg_of_pos S.hc)⟩
    · exact Or.inl ⟨mul_pos h S.ha,mul_neg_of_pos_of_neg h (neg_neg_of_pos S.hc)⟩
  have hys : (0 < u.2*S.b ∧ u.2*(-S.d) < 0) ∨
      (u.2*S.b < 0 ∧ 0 < u.2*(-S.d)) := by
    rcases lt_or_gt_of_ne hn.2 with h | h
    · exact Or.inr ⟨mul_neg_of_neg_of_pos h S.hb,mul_pos_of_neg_of_neg h (neg_neg_of_pos S.hd)⟩
    · exact Or.inl ⟨mul_pos h S.hb,mul_neg_of_pos_of_neg h (neg_neg_of_pos S.hd)⟩
  rcases ha with rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl | rfl <;>
    rcases hd with rfl | rfl | rfl | rfl <;>
    simp only [ne_eq,not_true_eq_false,false_and,and_false] at hdist
  all_goals
    simp only [dot,mul_zero,zero_add,add_zero] at hlevel hmax₀ hmax₁ hmax₂ hmax₃ hmin₀ hmin₁ hmin₂ hmin₃
    rcases hxs with ⟨hx₁,hx₂⟩ | ⟨hx₁,hx₂⟩ <;>
      rcases hys with ⟨hy₁,hy₂⟩ | ⟨hy₁,hy₂⟩ <;>
      linarith only [hlevel,hmax₀,hmax₁,hmax₂,hmax₃,hmin₀,hmin₁,hmin₂,hmin₃,hx₁,hx₂,hy₁,hy₂]


theorem width_preimage (K : Set Point) (f : Point →ᵃ[ℝ] ℝ) :
    rangeWidth (ParallelProductPlane.coordinates ⁻¹' K) (ParallelProductPlane.pullForm f) =
      rangeWidth K f := by
  exact Plank.Body.width_affine_preimage
    ParallelProductPlane.coordinates.toLinearEquiv.toAffineEquiv K f


/-- The coordinate bridge for the common four-point support/base conclusion. -/
theorem direction_of_fourPoint_preimage (S : Shape) (u : Point) (a b c d : Fin 2 → ℝ)
    (hmax : ∀ z ∈ ParallelProductPlane.coordinates ⁻¹' S.body,
      ParallelProductPlane.pullForm (direction u) z ≤ ParallelProductPlane.pullForm (direction u) a)
    (hmin : ∀ z ∈ ParallelProductPlane.coordinates ⁻¹' S.body,
      ParallelProductPlane.pullForm (direction u) b ≤ ParallelProductPlane.pullForm (direction u) z)
    (hlevel : ParallelProductPlane.pullForm (direction u) c =
      ParallelProductPlane.pullForm (direction u) d)
    (hs : ParallelProductPlane.coordinates ⁻¹' S.body =
      Plank.PlanarOnePlankVertices.fourPointBody a b c d) : u.1 = 0 ∨ u.2 = 0 := by
  let C := ParallelProductPlane.coordinates
  let K := C ⁻¹' S.body
  let f := ParallelProductPlane.pullForm (direction u)
  have hc : Convex ℝ K := (convex_body S).linear_preimage C.toLinearMap
  have hh : K = convexHull ℝ {a,b,c,d} := hs.trans
    (Plank.PlanarOnePlankVertices.fourPointBody_eq_hull a b c d (by rwa [← hs]))
  have hshape : S.body = convexHull ℝ {C a,C b,C c,C d} := by
    calc
      S.body = C '' K := (Set.image_preimage_eq S.body C.surjective).symm
      _ = C '' convexHull ℝ {a,b,c,d} := congrArg (fun A => C '' A) hh
      _ = convexHull ℝ (C '' {a,b,c,d}) := C.toLinearMap.image_convexHull _
      _ = convexHull ℝ {C a,C b,C c,C d} := by simp [Set.image_insert_eq]
  apply support_pair_direction S u (C a) (C b) (C c) (C d)
    (vertices_eq_of_four_hull S _ _ _ _ hshape)
  · intro z hz
    have hh := hmax (C.symm z) (by simpa [K,C,Shape.body] using (subset_convexHull ℝ S.vertices hz))
    simpa [f,C,ParallelProductPlane.pullForm] using hh
  · intro z hz
    have hh := hmin (C.symm z) (by simpa [K,C,Shape.body] using (subset_convexHull ℝ S.vertices hz))
    simpa [f,C,ParallelProductPlane.pullForm] using hh
  · exact hlevel

/-- On this genuine quadrilateral, a single physical positive plank can
attain the square bound only in a diagonal direction. The premise uses its
actual relative width, with no direction or placement assumption. -/
theorem one_plank_direction (S : Shape) (p : Plank) (hp : p.lo < p.hi)
    (hR : relativeWidth S p < 1)
    (he : (volume (S.body \ p.set)).toReal =
      (1-relativeWidth S p)^2*(volume S.body).toReal) : p.u.1 = 0 ∨ p.u.2 = 0 := by
  let C := ParallelProductPlane.coordinates
  let K := C ⁻¹' S.body
  let f := ParallelProductPlane.pullForm (direction p.u)
  have hK : IsCompact K := ParallelProductPlane.compact_preimage (compact_body S)
  have hc : Convex ℝ K := (convex_body S).linear_preimage C.toLinearMap
  have hne : K.Nonempty := ⟨C.symm 0,by simpa [K] using zero_mem S⟩
  have hV : 0 < (volume K).toReal := by
    rw [ParallelProductPlane.volume_preimage]
    exact area_body_pos S
  have hW : rangeWidth K f = rangeWidth S.body (direction p.u) := width_preimage S.body _
  have hgap : volume (K \ {x | p.lo ≤ f x ∧ f x ≤ p.hi}) = volume (S.body \ p.set) := by
    rw [← ParallelProductPlane.volume_preimage (S.body \ p.set)]
    congr 1
  obtain ⟨a,ha,b,hb,hmax,hmin,_,_,c,hcm,d,hdm,hfc,hfd,hs⟩ :=
    (Plank.PlanarOnePlankClassification.equality_iff_exists_fourPointBody
      hK hc hne hV f p.lo p.hi hp (by rw [hW]; exact direction_width_pos S p.u_ne_zero)
      (by rwa [hW])).mp (by
        rw [hgap,ParallelProductPlane.volume_preimage,hW]
        exact he)
  exact direction_of_fourPoint_preimage S p.u a b c d hmax hmin (hfc.trans hfd.symm) hs


/-- An arbitrary finite parallel family at positive subcritical equality must
also use a diagonal direction. Endpoints may be anywhere and null bands are
allowed; the budget is the sum of their actual relative widths. -/
theorem parallel_direction {ι : Type*} [Fintype ι] (S : Shape) (u : Point) (hu : u ≠ 0)
    (lo hi : ι → ℝ) (ho : ∀ i, lo i ≤ hi i)
    (hR₀ : 0 < ∑ i, (hi i-lo i)/rangeWidth S.body (direction u))
    (hR₁ : (∑ i, (hi i-lo i)/rangeWidth S.body (direction u)) < 1)
    (he : (volume (S.body \ ⋃ i, {z | lo i ≤ dot u z ∧ dot u z ≤ hi i})).toReal =
      (1-∑ i, (hi i-lo i)/rangeWidth S.body (direction u))^2*(volume S.body).toReal) :
    u.1 = 0 ∨ u.2 = 0 := by
  let C := ParallelProductPlane.coordinates
  let K := C ⁻¹' S.body
  let f := ParallelProductPlane.pullForm (direction u)
  have hK : IsCompact K := ParallelProductPlane.compact_preimage (compact_body S)
  have hc : Convex ℝ K := (convex_body S).linear_preimage C.toLinearMap
  have hne : K.Nonempty := ⟨C.symm 0,by simpa [K] using zero_mem S⟩
  have hV : 0 < (volume K).toReal := by
    rw [ParallelProductPlane.volume_preimage]
    exact area_body_pos S
  have hW : rangeWidth K f = rangeWidth S.body (direction u) := width_preimage S.body _
  have hWp : 0 < rangeWidth K f := by rw [hW]; exact direction_width_pos S hu
  obtain ⟨a,ha,b,hb,hmax,hmin,ht⟩ :=
    (Plank.PlanarParallelClassification.equality_iff_exists_normalized_tiling
      hK hc hne hV lo hi ho f hWp (by rwa [hW]) (by rwa [hW])).mp (by
        rw [ParallelProductPlane.volume_gap_preimage,ParallelProductPlane.volume_preimage,hW,
          max_eq_right (sub_pos.mpr hR₁).le]
        exact he)
  obtain ⟨L,H,_,_,_,_,_,c,_,d,_,hfc,hfd,hs⟩ := ht
  have hlevel : f c = f d := by
    have hh : (f c-f b)/rangeWidth K f = (f d-f b)/rangeWidth K f := by
      simpa [Plank.PlanarParallelClassification.normalizedForm,div_eq_mul_inv,mul_comm]
        using hfc.trans hfd.symm
    have he := congrArg (fun t : ℝ => t*rangeWidth K f) hh
    simp only [div_mul_cancel₀ _ hWp.ne'] at he
    linarith only [he]
  exact direction_of_fourPoint_preimage S u a b c d hmax hmin hlevel hs

end Quant.CrossedQuadrilateralDirections

/-- info: 'Quant.CrossedQuadrilateralDirections.one_plank_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralDirections.one_plank_direction

/-- info: 'Quant.CrossedQuadrilateralDirections.parallel_direction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralDirections.parallel_direction
