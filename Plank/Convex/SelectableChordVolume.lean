/- One contained-chord volume proof for every stable finite side-assignment
criterion. The algebra supplies the selector; convexity supplies the seed. -/
module

public import Plank.Algebra.SideAssignments
public import Plank.Measure.ChordSeed
public import Plank.Measure.LinearBands
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SelectableChordVolume

open Set MeasureTheory
open scoped BigOperators Pointwise

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Fintype ι]

/-- A side assignment for the actual steps is enough for the measure bound.
The diagonal steps may exceed the band widths; neither convexity nor a
uniform condition over other column scalings is needed here. -/
theorem measure_core_le_closed_gap (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : ι → E →L[ℝ] ℝ) (hfne : ∀i,f i≠0)
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i)
    (v : ι → E) (hselect : SideAssignments.Admits (fun i j => f i (v j)))
    (hdiag : ∀i,hi i-lo i≤f i (v i))
    (K core : Set E) (hm : MeasurableSet core)
    (hinside : ∀s : Finset ι,∀t∈core,t+s.sum v∈K) :
    μ core≤μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  classical
  apply LinearBands.measure_le_closed_gap_of_translations μ (fun i => f i)
    (fun i => (f i).continuous.measurable) lo hi ho
    (fun i => LinearBands.measure_level_zero μ (f i) (hfne i) (lo i))
    (fun i => LinearBands.measure_level_zero μ (f i) (hfne i) (hi i))
    core hm (fun s => s.sum v) ?_ K hinside
  intro t _
  obtain ⟨s,hh,hl⟩ := hselect (fun i => f i t-lo i)
  refine ⟨s,?_⟩
  intro i
  change if i∈s then hi i≤f i (t+s.sum v) else f i (t+s.sum v)≤lo i
  simp only [map_add,map_sum]
  by_cases his : i∈s
  · simp only [his,↓reduceIte]
    have h := hh i his
    change f i (v i)≤f i t-lo i+s.sum (fun j => f i (v j)) at h
    linarith [hdiag i]
  · simp only [his,↓reduceIte]
    have h := hl i his
    change f i t-lo i+s.sum (fun j => f i (v j))≤0 at h
    linarith

/-- Zero-width steps are included in the algebraic selector hypothesis. -/
theorem measure_gap_ge_of_chords_le_one_of_assignment (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →L[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i-y i))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i)
    (hselect : SideAssignments.Admits
      (fun i j => ((hi j-lo j)/f j (x j-y j))*f i (x j-y j)))
    (hsum : ∑i,(hi i-lo i)/f i (x i-y i)≤1) :
    (ENNReal.ofReal (1-∑i,(hi i-lo i)/f i (x i-y i)))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  let ρ (i : ι) := (hi i-lo i)/f i (x i-y i)
  let v (i : ι) := ρ i • (x i-y i)
  have hρ (i : ι) : 0≤ρ i := div_nonneg (sub_nonneg.mpr (ho i)) (hspan i).le
  have hfne (i : ι) : f i≠0 := by
    intro hz
    have hp := hspan i
    simp [hz] at hp
  have hself (i : ι) : ρ i*f i (x i-y i)=hi i-lo i :=
    div_mul_cancel₀ _ (hspan i).ne'
  have hv (i j : ι) : f i (v j)=ρ j*f i (x j-y j) := map_smul (f i) _ _
  have hb := measure_core_le_closed_gap μ f hfne lo hi ho v
    (by simpa only [hv] using hselect)
    (fun i => by rw [hv,hself]) K
    (Plank.Convex.chordSeed K ρ y) (BangVolume.measurableSet_chordSeed hm ρ y) (by
      intro s t ht
      exact Plank.Convex.chordSeed_shift_mem hc x y hx hy ρ hρ hsum s ht)
  rw [BangVolume.measure_chordSeed μ K ρ y hsum] at hb
  exact hb

/-- Assignment for the actual width-scaled steps gives the truncated bound. -/
theorem measure_gap_ge_of_chords_of_assignment (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →L[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i-y i))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i)
    (hselect : SideAssignments.Admits
      (fun i j => ((hi j-lo j)/f j (x j-y j))*f i (x j-y j))) :
    (ENNReal.ofReal (max 0 (1-∑i,(hi i-lo i)/f i (x i-y i))))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  by_cases hsum : ∑i,(hi i-lo i)/f i (x i-y i)≤1
  · simpa only [max_eq_right (sub_nonneg.mpr hsum)] using
      measure_gap_ge_of_chords_le_one_of_assignment μ K hc hm f x y hx hy hspan lo hi ho hselect hsum
  · have hdim : Module.finrank ℝ E≠0 := by
      intro hd
      have : Subsingleton E := Module.finrank_zero_iff.mp hd
      have : IsEmpty ι := ⟨fun i => by
        have hp := hspan i
        rw [Subsingleton.elim (x i) (y i),sub_self,map_zero] at hp
        exact (lt_irrefl 0) hp⟩
      simp at hsum
    have hz : max 0 (1-∑i,(hi i-lo i)/f i (x i-y i))=0 :=
      max_eq_left (sub_nonpos.mpr (le_of_not_ge hsum))
    simp only [hz,ENNReal.ofReal_zero,zero_pow hdim,zero_mul,zero_le]

/-- Affine constants shift the windows and preserve every chord evaluation. -/
theorem measure_gap_ge_of_affine_chords_of_assignment (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i)-f i (y i))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i)
    (hselect : SideAssignments.Admits
      (fun i j => ((hi j-lo j)/(f j (x j)-f j (y j)))*(f i (x j)-f i (y j)))) :
    (ENNReal.ofReal (max 0 (1-∑i,(hi i-lo i)/(f i (x i)-f i (y i)))))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  let g (i : ι) := (f i).linear.toContinuousLinearMap
  have hlin (i j : ι) : g i (x j-y j)=f i (x j)-f i (y j) := by
    simpa only [g,LinearMap.coe_toContinuousLinearMap',vsub_eq_sub] using
      (f i).linearMap_vsub (x j) (y j)
  have hf (i : ι) (z : E) : f i z=g i z+f i 0 := by
    simpa only [g,LinearMap.coe_toContinuousLinearMap',vadd_eq_add,add_zero] using
      (f i).map_vadd (0 : E) z
  have hband (i : ι) : LinearBands.closedBand (g i) (lo i-f i 0) (hi i-f i 0)=
      LinearBands.closedBand (f i) (lo i) (hi i) := by
    ext z
    change (lo i-f i 0≤g i z ∧ g i z≤hi i-f i 0) ↔ (lo i≤f i z ∧ f i z≤hi i)
    rw [hf i z]
    simp only [sub_le_iff_le_add,le_sub_iff_add_le]
  have hb := measure_gap_ge_of_chords_of_assignment μ K hc hm g x y hx hy
    (by simpa only [hlin] using hspan)
    (fun i => lo i-f i 0) (fun i => hi i-f i 0) (fun i => sub_le_sub_right (ho i) _)
    (by simpa only [hlin,sub_sub_sub_cancel_right] using hselect)
  simpa only [hlin,sub_sub_sub_cancel_right,hband] using hb

/-- Stability supplies the actual assignment for every ordered window. -/
theorem measure_gap_ge_of_chords_le_one (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →L[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i-y i))
    (hselect : SideAssignments.Stable (fun i j => f i (x j-y j)))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i)
    (hsum : ∑i,(hi i-lo i)/f i (x i-y i)≤1) :
    (ENNReal.ofReal (1-∑i,(hi i-lo i)/f i (x i-y i)))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) :=
  measure_gap_ge_of_chords_le_one_of_assignment μ K hc hm f x y hx hy hspan lo hi ho
    (hselect (fun i => (hi i-lo i)/f i (x i-y i))
      (fun i => div_nonneg (sub_nonneg.mpr (ho i)) (hspan i).le)) hsum

theorem measure_gap_ge_of_chords (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →L[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i-y i))
    (hselect : SideAssignments.Stable (fun i j => f i (x j-y j)))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) :
    (ENNReal.ofReal (max 0 (1-∑i,(hi i-lo i)/f i (x i-y i))))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) :=
  measure_gap_ge_of_chords_of_assignment μ K hc hm f x y hx hy hspan lo hi ho
    (hselect (fun i => (hi i-lo i)/f i (x i-y i))
      (fun i => div_nonneg (sub_nonneg.mpr (ho i)) (hspan i).le))

theorem measure_gap_ge_of_affine_chords (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : Set E) (hc : Convex ℝ K) (hm : MeasurableSet K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K) (hspan : ∀i,0<f i (x i)-f i (y i))
    (hselect : SideAssignments.Stable (fun i j => f i (x j)-f i (y j)))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) :
    (ENNReal.ofReal (max 0 (1-∑i,(hi i-lo i)/(f i (x i)-f i (y i)))))^Module.finrank ℝ E*μ K≤
      μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) :=
  measure_gap_ge_of_affine_chords_of_assignment μ K hc hm f x y hx hy hspan lo hi ho
    (hselect (fun i => (hi i-lo i)/(f i (x i)-f i (y i)))
      (fun i => div_nonneg (sub_nonneg.mpr (ho i)) (hspan i).le))

end Plank.SelectableChordVolume
