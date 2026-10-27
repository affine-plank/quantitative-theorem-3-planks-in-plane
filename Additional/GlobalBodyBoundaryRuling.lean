/- Covered boundary points of a positive-gap global quantitative minimum
lie on boundary segments reaching the exterior of the covered interior. -/
module
public import ConvexBoundaryRuling
public import GlobalPlankBodyEnlargement

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalBodyBoundaryRuling

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

/-- A proper point enlargement of a positive-gap minimum must add an
uncovered point. No support-width constraint is imposed on the enlargement. -/
theorem point_enlargement (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (ho : ∀ i,lo i≤hi i) (hW : ∀ i,0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi))
    (p : E) (hp : p∉K) :
    ∃ z∈convexHull ℝ (insert p K),z∉K ∧ z∉covered f lo hi := by
  have hne : K.Nonempty := by
    by_contra hn
    simp [not_nonempty_iff_eq_empty.mp hn,Measure.real] at hV
  let C := convexHull ℝ (insert p K)
  have hC : IsCompact C := ConvexBoundaryRuling.compact_insert hK hc hne p
  have hKC : K⊆C := (subset_insert p K).trans (subset_convexHull ℝ _)
  by_contra! hn
  have hg : C\covered f lo hi⊆K\covered f lo hi := by
    rintro z ⟨hz,hzu⟩
    exact ⟨by by_contra hzk; exact hzu (hn z hz hzk),hzu⟩
  have he := GlobalPlankBodyEnlargement.eq_of_gap_volume_le μ hK hV hC
    (convex_convexHull ℝ _) hKC f lo hi ho hW d hbudget hglobal hgap
    (measureReal_mono hg (measure_ne_top_of_subset sdiff_subset hK.measure_ne_top))
  exact hp (he ▸ (subset_convexHull ℝ (insert p K) (mem_insert p K)))

/-- Exact boundary structure, in every dimension and for any finite plank
family. The endpoint can lie on a plank boundary; it need not be uncovered. -/
theorem boundary_segment (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (ho : ∀ i,lo i≤hi i) (hW : ∀ i,0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi))
    {x : E} (hx : x∈frontier K) (hxu : x∈interior (covered f lo hi)) :
    ∃ z∈frontier K,z∉interior (covered f lo hi) ∧ x≠z ∧
      segment ℝ x z⊆frontier K :=
  ConvexBoundaryRuling.exists_boundary_segment hK hc
    (point_enlargement μ hK hc hV f lo hi ho hW d hbudget hglobal hgap) hx hxu

/-- For each plank strictly containing a boundary point, one such segment
can be stopped at that very plank's lower or upper boundary hyperplane. -/
theorem plank_boundary_segment (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (ho : ∀ i,lo i≤hi i) (hW : ∀ i,0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi))
    {x : E} (hx : x∈frontier K) (i : ι) (hxi : f i x∈Ioo (lo i) (hi i)) :
    ∃ y∈frontier K,(f i y=lo i ∨ f i y=hi i) ∧ x≠y ∧
      segment ℝ x y⊆frontier K := by
  have hiU : (f i) ⁻¹' Ioo (lo i) (hi i)⊆interior (covered f lo hi) :=
    interior_maximal (fun y hy => mem_iUnion.mpr ⟨i,hy.1.le,hy.2.le⟩)
      (isOpen_Ioo.preimage (f i).continuous_of_finiteDimensional)
  obtain ⟨z,_,hzu,_,hseg⟩ := boundary_segment μ hK hc hV f lo hi ho hW d hbudget
    hglobal hgap hx (hiU hxi)
  have hz : ¬f i z∈Ioo (lo i) (hi i) := fun hz => hzu (hiU hz)
  have hex : ∃ a,(a=lo i ∨ a=hi i) ∧ a∈segment ℝ (f i x) (f i z) := by
    rw [segment_eq_uIcc]
    by_cases hl : f i z≤lo i
    · exact ⟨lo i,Or.inl rfl,mem_uIcc.mpr (Or.inr ⟨hl,hxi.1.le⟩)⟩
    · have hh : hi i≤f i z := le_of_not_gt fun hh => hz ⟨lt_of_not_ge hl,hh⟩
      exact ⟨hi i,Or.inr rfl,mem_uIcc.mpr (Or.inl ⟨hxi.2.le,hh⟩)⟩
  obtain ⟨a,ha,has⟩ := hex
  rw [←image_segment ℝ (f i) x z] at has
  obtain ⟨y,hy,he⟩ := has
  have hey : f i y=lo i ∨ f i y=hi i := ha.imp (he.trans ·) (he.trans ·)
  refine ⟨y,hseg hy,hey,?_,?_⟩
  · intro h
    subst y
    rcases hey with h | h
    · exact (ne_of_gt hxi.1) h
    · exact (ne_of_lt hxi.2) h
  · exact ((convex_segment x z).segment_subset (left_mem_segment _ _ _) hy).trans hseg

end Plank.GlobalBodyBoundaryRuling
