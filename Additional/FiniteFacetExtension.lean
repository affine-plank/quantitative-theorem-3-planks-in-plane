/- Relaxing one actual facet of a finite halfspace intersection.
The bounded convex extension is constructed; no cap-placement hypothesis. -/
module
public import GlobalBodyCutVariation
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteFacetExtension

open Set Metric MeasureTheory
open scoped Topology

variable {E κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype κ]

omit [FiniteDimensional ℝ E] [Fintype κ] in
theorem convex_of_rep {K : Set (ℝ × E)}
    (g : κ → (ℝ × E) →ᵃ[ℝ] ℝ) (c : κ → ℝ) (b : ℝ)
    (hrep : K={x | x.1≤b ∧ ∀ j,g j x≤c j}) : Convex ℝ K := by
  rw [hrep,ofPred_and,ofPred_forall]
  exact ((convex_Iic b).affine_preimage (LinearMap.fst ℝ ℝ E).toAffineMap).inter
    (convex_iInter fun j => (convex_Iic (c j)).affine_preimage (g j))

/-- Strictness of the other rows makes the point interior to the actual
supporting section. No extension of the body is needed. -/
theorem interior_fiber_of_strict {K : Set (ℝ × E)}
    (g : κ → (ℝ × E) →ᵃ[ℝ] ℝ) (c : κ → ℝ) (b : ℝ)
    (hrep : K={x | x.1≤b ∧ ∀ j,g j x≤c j})
    (y : E) (hstrict : ∀ j,g j (b,y)<c j) : y∈interior (ConvexSections.fiber K b) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hn : ∀ᶠ z in 𝓝 y,∀ j,g j (b,z)<c j := Filter.eventually_all.mpr fun j =>
    ((g j).continuous_of_finiteDimensional.comp
      (continuous_const.prodMk continuous_id)).continuousAt.eventually (Iio_mem_nhds (hstrict j))
  filter_upwards [hn] with z hz
  change (b,z)∈K
  rw [hrep]
  exact ⟨le_rfl,fun j => (hz j).le⟩

/-- A strict point on the distinguished facet supplies a genuine compact
convex extension across it. The original body is exactly a fixed-lower-cut
window in that extension, so the supporting-cut calculus applies. -/
theorem exists_window_extension {K : Set (ℝ × E)} (hK : IsCompact K)
    (g : κ → (ℝ × E) →ᵃ[ℝ] ℝ) (c : κ → ℝ) (b : ℝ)
    (hrep : K={x | x.1≤b ∧ ∀ j,g j x≤c j})
    (y : E) (hstrict : ∀ j,g j (b,y)<c j) :
    ∃ (L : Set (ℝ × E)) (a : ℝ),
      IsCompact L ∧ Convex ℝ L ∧ (interior L).Nonempty ∧ a<b ∧
      b∈interior (Prod.fst '' L) ∧ MovingCutArea.window L a b=K := by
  classical
  have hz : (b,y)∈K := by rw [hrep]; exact ⟨le_rfl,fun j => (hstrict j).le⟩
  obtain ⟨M,hM,hbound⟩ := hK.isBounded.exists_pos_norm_le
  let R := M+1
  let L : Set (ℝ × E) := closedBall 0 R∩{x | ∀ j,g j x≤c j}
  let a := -M-2
  have hrows : IsClosed {x | ∀ j,g j x≤c j} := by
    rw [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le (g j).continuous_of_finiteDimensional continuous_const
  have hLc : IsCompact L := (isCompact_closedBall 0 R).inter_right hrows
  have hLv : Convex ℝ L := by
    apply (convex_closedBall (0 : ℝ × E) R).inter
    rw [ofPred_forall]
    exact convex_iInter fun j => (convex_Iic (c j)).affine_preimage (g j)
  have hn : ‖(b,y)‖<R := (hbound (b,y) hz).trans_lt (by dsimp [R]; linarith)
  have hnear : ∀ᶠ p : ℝ × E in 𝓝 (b,y),‖p‖<R ∧ ∀ j,g j p<c j :=
    Filter.Eventually.and ((isOpen_lt continuous_norm continuous_const).mem_nhds hn)
      (Filter.eventually_all.2 fun j =>
        (isOpen_lt (g j).continuous_of_finiteDimensional continuous_const).mem_nhds (hstrict j))
  have hzint : (b,y)∈interior L := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hnear] with p hp
    exact ⟨by simpa only [mem_closedBall,dist_zero_right] using hp.1.le,
      fun j => (hp.2 j).le⟩
  have hcut : b∈interior (Prod.fst '' L) :=
    isOpenMap_fst.image_interior_subset L ⟨(b,y),hzint,rfl⟩
  have hfirst (x : ℝ × E) : |x.1|≤‖x‖ := by
    simpa only [Real.norm_eq_abs] using norm_fst_le x
  have hzb : -M≤b := (abs_le.mp ((hfirst (b,y)).trans (hbound (b,y) hz))).1
  refine ⟨L,a,hLc,hLv,⟨(b,y),hzint⟩,by dsimp [a]; linarith,hcut,?_⟩
  ext x
  constructor
  · rintro ⟨hxL,hxrange,_⟩
    rw [hrep]
    exact ⟨hxrange.2,hxL.2⟩
  · intro hx
    have hxp := hx
    rw [hrep] at hxp
    have hxnorm := hbound x hx
    have hxlo : -M≤x.1 := (abs_le.mp ((hfirst x).trans hxnorm)).1
    refine ⟨⟨?_,hxp.2⟩,⟨?_,hxp.1⟩,mem_univ _⟩
    · simpa only [mem_closedBall,dist_zero_right] using hxnorm.trans (by dsimp [R]; linarith)
    · dsimp [a]; linarith only [hxlo]

variable {ι : Type*} [Fintype ι] [MeasurableSpace E] [BorelSpace E]

/-- Every noncoincident facet of a positive-gap global minimum has an
uncovered point. This follows directly from the actual supporting-section
inequality and positive face area, without constructing an extension. -/
theorem not_fully_covered_facet (ν : MeasureTheory.Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K)
    (g : κ → (ℝ × E) →ᵃ[ℝ] ℝ) (c : κ → ℝ) (b : ℝ)
    (hrep : K={x | x.1≤b ∧ ∀ j,g j x≤c j})
    (y : E) (hstrict : ∀ j,g j (b,y)<c j)
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i,lo i≤hi i)
    (hsep : ∀ j, (¬∀ z,f j (b,z)=lo j) ∧ (¬∀ z,f j (b,z)=hi j))
    (hV : 0<(MeasureTheory.volume.prod ν).real K)
    (hW : ∀ i,0<Plank.Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : PrunedPlankCounterexample.budget K f lo hi≤B)
    (hglobal : GlobalPlankBodyMinimum.IsGlobalMinimum (MeasureTheory.volume.prod ν)
      K f lo hi d B)
    (hgap : 0<(MeasureTheory.volume.prod ν).real (K\PrunedPlankCounterexample.covered f lo hi)) :
    ¬∀ z,(b,z)∈K → (b,z)∈PrunedPlankCounterexample.covered f lo hi := by
  have hh := GlobalSupportingFaceBalance.section_ge ν hK (convex_of_rep g c b hrep)
    b (fun p hp => (hrep ▸ hp).1) f lo hi horder hV hW hsep d hbudget hglobal
  intro hcover
  have hz : ConvexSections.fiber (K\PrunedPlankCounterexample.covered f lo hi) b=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.2 (hcover z hz.1)
  rw [hz,measureReal_empty] at hh
  have harea : 0<ν.real (ConvexSections.fiber K b) :=
    ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior ν
      ⟨y,interior_fiber_of_strict g c b hrep y hstrict⟩).ne'
      (ConvexSections.compact_fiber hK b).measure_ne_top
  exact (not_le_of_gt (mul_pos (div_pos hgap hV) harea)) hh

end Plank.FiniteFacetExtension
