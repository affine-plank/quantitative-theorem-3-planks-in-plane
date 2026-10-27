/- Actual original-width bounds from stable finite side assignments. -/
module

public import Plank.Convex.SelectableChordVolume
public import Plank.Proofs.AffineWidth

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.SelectableSupportChords

open Set MeasureTheory

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem uncovered_volume_lower_bound_of_assignment (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K)
    (hspan : ∀i,f i (x i)-f i (y i)=Body.width K (f i))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) (hW : ∀i,0<Body.width K (f i))
    (hselect : SideAssignments.Admits
      (fun i j => ((hi j-lo j)/Body.width K (f j))*(f i (x j)-f i (y j)))) :
    (max 0 (1-∑i,(hi i-lo i)/Body.width K (f i)))^Module.finrank ℝ E*μ.real K≤
      μ.real (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) := by
  have h := SelectableChordVolume.measure_gap_ge_of_affine_chords_of_assignment μ K hc
    hK.measurableSet f x y hx hy (by simpa only [hspan] using hW) lo hi ho
    (by simpa only [hspan] using hselect)
  simp only [hspan] at h
  have hf : μ (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i))≠⊤ :=
    measure_ne_top_of_subset sdiff_subset hK.measure_ne_top
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (le_max_left _ _),Measure.real] using ENNReal.toReal_mono hf h

theorem cover_relative_width_sum_ge_one_of_assignment (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K)
    (hspan : ∀i,f i (x i)-f i (y i)=Body.width K (f i))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) (hW : ∀i,0<Body.width K (f i))
    (hselect : SideAssignments.Admits
      (fun i j => ((hi j-lo j)/Body.width K (f j))*(f i (x j)-f i (y j))))
    (hcover : K⊆⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) :
    1≤∑i,(hi i-lo i)/Body.width K (f i) := by
  by_contra hn
  have hR : (∑i,(hi i-lo i)/Body.width K (f i))<1 := lt_of_not_ge hn
  have h := uncovered_volume_lower_bound_of_assignment μ hK hc f x y hx hy hspan lo hi ho hW hselect
  simp only [sdiff_eq_empty.mpr hcover,Measure.real,measure_empty,ENNReal.toReal_zero] at h
  have hp : 0<max 0 (1-∑i,(hi i-lo i)/Body.width K (f i)) :=
    lt_max_of_lt_right (sub_pos.mpr hR)
  exact (not_le_of_gt (mul_pos (pow_pos hp _) hV)) h

theorem uncovered_volume_lower_bound (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K)
    (hspan : ∀i,f i (x i)-f i (y i)=Body.width K (f i))
    (hselect : SideAssignments.Stable (fun i j => f i (x j)-f i (y j)))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) (hW : ∀i,0<Body.width K (f i)) :
    (max 0 (1-∑i,(hi i-lo i)/Body.width K (f i)))^Module.finrank ℝ E*μ.real K≤
      μ.real (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) :=
  uncovered_volume_lower_bound_of_assignment μ hK hc f x y hx hy hspan lo hi ho hW
    (hselect (fun i => (hi i-lo i)/Body.width K (f i))
      (fun i => div_nonneg (sub_nonneg.mpr (ho i)) (hW i).le))

theorem cover_relative_width_sum_ge_one (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (x y : ι → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K)
    (hspan : ∀i,f i (x i)-f i (y i)=Body.width K (f i))
    (hselect : SideAssignments.Stable (fun i j => f i (x j)-f i (y j)))
    (lo hi : ι → ℝ) (ho : ∀i,lo i≤hi i) (hW : ∀i,0<Body.width K (f i))
    (hcover : K⊆⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) :
    1≤∑i,(hi i-lo i)/Body.width K (f i) :=
  cover_relative_width_sum_ge_one_of_assignment μ hK hc hV f x y hx hy hspan lo hi ho hW
    (hselect (fun i => (hi i-lo i)/Body.width K (f i))
      (fun i => div_nonneg (sub_nonneg.mpr (ho i)) (hW i).le)) hcover

variable {κ : Type*} [Fintype κ]

/-- Two selectable blocks suffice. Chords in the first block leave every
second-block form unchanged; the reverse interactions are unrestricted. -/
theorem uncovered_volume_lower_bound_of_blocks (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (f : (ι ⊕ κ) → E →ᵃ[ℝ] ℝ) (x y : (ι ⊕ κ) → E)
    (hx : ∀i,x i∈K) (hy : ∀i,y i∈K)
    (hspan : ∀i,f i (x i)-f i (y i)=Body.width K (f i))
    (hleft : SideAssignments.Stable
      (fun i j => f (.inl i) (x (.inl j))-f (.inl i) (y (.inl j))))
    (hright : SideAssignments.Stable
      (fun i j => f (.inr i) (x (.inr j))-f (.inr i) (y (.inr j))))
    (hzero : ∀i j,f (.inr j) (x (.inl i))-f (.inr j) (y (.inl i))=0)
    (lo hi : (ι ⊕ κ) → ℝ) (ho : ∀i,lo i≤hi i) (hW : ∀i,0<Body.width K (f i)) :
    (max 0 (1-∑i,(hi i-lo i)/Body.width K (f i)))^Module.finrank ℝ E*μ.real K≤
      μ.real (K\⋃i,LinearBands.closedBand (f i) (lo i) (hi i)) :=
  uncovered_volume_lower_bound μ hK hc f x y hx hy hspan
    (SideAssignments.stable_sum _ hleft hright hzero) lo hi ho hW

end Plank.SelectableSupportChords
