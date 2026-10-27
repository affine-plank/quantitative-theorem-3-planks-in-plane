/- Actual global quantitative minima exist in every finite dimension.
The affine normalization and compact comparison are constructions, not premises. -/
module

public import FiniteDimensionalBodyNormalization
public import FinitePlankNormalization
public import FinitePlankAffineTransport
public import GlobalPlankBoundaryMinimum
public import GlobalPlankMergeMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalGlobalMinimum

open Set Metric MeasureTheory
open FiniteDimensionalBodyNormalization (Point innerRadius innerRadius_pos)
open FinitePlankAffineTransport (pull)
open PrunedPlankCounterexample GlobalPlankBodyMinimum

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Every physical competitor has a member of one fixed compact parameter
family with no larger quantitative margin, at the SAME budget and exponent. -/
theorem exists_normalized_le (μ : Measure (Point n)) [μ.IsAddHaarMeasure]
    {K : Set (Point n)} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → Point n →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (hW : ∀ i,0<Plank.Body.width K (f i)) (horder : ∀ i,a i≤b i)
    (d : ℕ) {B : ℝ} (hbudget : budget K f a b≤B) :
    ∃ q : NormalizedPlankBodyMinimum.Data (E := Point n) (ι := ι) (innerRadius n) 2,
      q∈NormalizedPlankBodyMinimum.domain B ∧
      NormalizedPlankBodyMinimum.margin μ d B q≤GlobalPlankBodyMinimum.margin μ K f a b d B := by
  obtain ⟨F,hin,hout⟩ :=
    FiniteDimensionalBodyNormalization.exists_ball_sandwich_of_volume_pos μ hK hconv hV
  have hc : IsCompact (F ⁻¹' K) := by
    rw [show F ⁻¹' K=F.symm '' K by ext x; simp]
    exact hK.image F.symm.toAffineMap.continuous_of_finiteDimensional
  let C : NormalizedPlankBodyMinimum.Body (E := Point n) (innerRadius n) 2 :=
    ⟨⟨⟨F ⁻¹' K,hc⟩,⟨0,hin (by simpa using (innerRadius_pos n).le)⟩⟩,
      hconv.affine_preimage F.toAffineMap,hin,hout⟩
  have hw (i) : Plank.Body.width (C.1 : Set (Point n)) (pull F (f i))=Plank.Body.width K (f i) :=
    FinitePlankAffineTransport.width_pull F K (f i)
  have hb : budget (C.1 : Set (Point n)) (fun i => pull F (f i)) a b=budget K f a b :=
    FinitePlankAffineTransport.budget_pull F K f a b
  obtain ⟨q,hq,hle⟩ := FinitePlankNormalization.exists_data_le (B := B) μ (innerRadius_pos n) C
    (fun i => pull F (f i)) a b horder (fun i => by rw [hw i]; exact hW i) d
    (by rw [hb]; exact hbudget)
  exact ⟨q,hq,hle.trans_eq (FinitePlankAffineTransport.margin_pull μ F K f a b d B)⟩

/-- Any negative competitor gives an actual negative global minimum over
all compact positive-volume convex bodies and all finite indexed plank
configurations in R^n. No qualitative plank theorem, polytope restriction,
or prescribed bound on the number of faces is used. -/
theorem exists_negative_global_minimum (μ : Measure (Point n)) [μ.IsAddHaarMeasure]
    {K : Set (Point n)} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → Point n →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (hW : ∀ i,0<Plank.Body.width K (f i)) (horder : ∀ i,a i≤b i)
    (d : ℕ) {B : ℝ} (hbudget : budget K f a b≤B)
    (hbad : GlobalPlankBodyMinimum.margin μ K f a b d B<0) :
    ∃ (C : Set (Point n)) (g : ι → Point n →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ),
      IsCompact C ∧ Convex ℝ C ∧ 0<μ.real C ∧
      (∀ i,0<Plank.Body.width C (g i)) ∧ (∀ i,lo i≤hi i) ∧
      budget C g lo hi≤B ∧ GlobalPlankBodyMinimum.margin μ C g lo hi d B<0 ∧
      IsGlobalMinimum μ C g lo hi d B := by
  obtain ⟨q₀,hq₀,hq₀le⟩ := exists_normalized_le μ hK hconv hV f a b hW horder d hbudget
  obtain ⟨q,hq,hneg,hmin⟩ := NormalizedPlankBodyMinimum.exists_negative_minimum μ
    (innerRadius_pos n) d B hq₀ (hq₀le.trans_lt hbad)
  let C : Set (Point n) := NormalizedPlankBodyMinimum.body q
  let g := NormalizedPlankBodyMinimum.form q
  let lo := NormalizedPlankBodyMinimum.lo q
  let hi := NormalizedPlankBodyMinimum.hi q
  have he : NormalizedPlankBodyMinimum.margin μ d B q=GlobalPlankBodyMinimum.margin μ C g lo hi d B :=
    NormalizedPlankBodyMinimum.margin_eq_physical μ (innerRadius_pos n) q d B
  have hw (i) : 0<Plank.Body.width C (g i) :=
    NormalizedPlankBodyMinimum.span_pos μ (innerRadius_pos n) q i
  have hsum : budget C g lo hi=NormalizedPlankBodyMinimum.total q.2.2 :=
    NormalizedPlankBodyMinimum.budget_eq_total μ (innerRadius_pos n) q
  refine ⟨C,g,lo,hi,(NormalizedPlankBodyMinimum.body q).isCompact,q.1.2.1,
    NormalizedPlankBodyMinimum.volume_pos μ (innerRadius_pos n) q,hw,?_,?_,?_,?_⟩
  · intro i
    change NormalizedPlankBodyMinimum.lower q i+q.2.2.1 i*NormalizedPlankBodyMinimum.span q i≤
      NormalizedPlankBodyMinimum.lower q i+q.2.2.2 i*NormalizedPlankBodyMinimum.span q i
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hq.2.2.1 i).2.1 (hw i).le)
  · rw [hsum]; exact hq.2.2.2
  · rwa [he] at hneg
  · intro D h aa bb hD hDc hDV hDW horder hbudget
    obtain ⟨p,hp,hle⟩ := exists_normalized_le μ hD hDc hDV h aa bb hDW horder d hbudget
    rw [← he]
    exact (hmin hp).trans hle

/-- In positive dimension, any strict physical failure has an actual global
minimum whose every positive-width window lies strictly inside its body's
range. No smaller-plank theorem or polygonal/chart selection is required. -/
theorem exists_negative_minimum_with_interior_windows (μ : Measure (Point n))
    [μ.IsAddHaarMeasure] (hn : 0<n)
    {K : Set (Point n)} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → Point n →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (hW : ∀ i,0<Plank.Body.width K (f i)) (horder : ∀ i,a i≤b i)
    {B : ℝ} (hB : B≤1) (hbudget : budget K f a b≤B)
    (hbad : GlobalPlankBodyMinimum.margin μ K f a b n B<0) :
    ∃ (C : Set (Point n)) (g : ι → Point n →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ),
      IsCompact C ∧ Convex ℝ C ∧ 0<μ.real C ∧
      (∀ i,0<Plank.Body.width C (g i)) ∧ (∀ i,lo i≤hi i) ∧
      budget C g lo hi≤B ∧ GlobalPlankBodyMinimum.margin μ C g lo hi n B<0 ∧
      IsGlobalMinimum μ C g lo hi n B ∧
      (∀ i, lo i<hi i → (∃ x∈C, g i x<lo i) ∧ (∃ y∈C, hi i<g i y)) := by
  classical
  obtain ⟨C,g,lo,hi,hC,hCc,hCV,hCW,ho,hbud,hneg,hmin⟩ :=
    exists_negative_global_minimum μ hK hconv hV f a b hW horder n hbudget hbad
  refine ⟨C,g,lo,hi,hC,hCc,hCV,hCW,ho,hbud,hneg,hmin,?_⟩
  have he : Module.finrank ℝ (Point n)=n := Module.finrank_fin_fun ℝ
  intro i hipos
  exact GlobalPlankBoundaryMinimum.active_window_interior μ (he.symm ▸ hn)
    hC hCc hCV g lo hi ho hCW hB hbud (he.symm ▸ hneg) (he.symm ▸ hmin) i hipos

/-- A strict failure has a support-normalized negative global minimum with
the fewest active endpoint windows. Its active cuts are interior, and no
two distinct active planks have a coincident boundary hyperplane. The result
works in every positive dimension and for every finite index type. -/
theorem exists_negative_minimum_with_separated_active_windows (μ : Measure (Point n))
    [μ.IsAddHaarMeasure] (hn : 0<n)
    {K : Set (Point n)} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → Point n →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (hW : ∀ i,0<Plank.Body.width K (f i)) (horder : ∀ i,a i≤b i)
    {B : ℝ} (hB : B≤1) (hbudget : budget K f a b≤B)
    (hbad : GlobalPlankBodyMinimum.margin μ K f a b n B<0) :
    ∃ (C : Set (Point n)) (g : ι → Point n →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ),
      IsCompact C ∧ Convex ℝ C ∧ 0<μ.real C ∧
      (∀ i,Plank.Body.width C (g i)=1) ∧ (∀ i x,x∈C → 0≤g i x ∧ g i x≤1) ∧
      (∀ i,lo i≤hi i) ∧ budget C g lo hi≤B ∧
      GlobalPlankBodyMinimum.margin μ C g lo hi n B<0 ∧
      IsGlobalMinimum μ C g lo hi n B ∧ GlobalPlankMergeMinimum.LeastActive μ C g lo hi n B ∧
      (∀ i,lo i<hi i → (∃ x∈C,g i x<lo i) ∧ (∃ y∈C,hi i<g i y)) ∧
      (∀ i j,i≠j → lo i<hi i → lo j<hi j → ∀ u v,
        u=lo i ∨ u=hi i → v=lo j ∨ v=hi j → ¬∀ x,g i x=u → g j x=v) := by
  obtain ⟨C,h,c,e,hC,hCc,hCV,hCW,ho,hbud,hneg,hmin⟩ :=
    exists_negative_global_minimum μ hK hconv hV f a b hW horder n hbudget hbad
  have hne : C.Nonempty := by
    by_contra hh
    simp [not_nonempty_iff_eq_empty.mp hh,Measure.real] at hCV
  obtain ⟨g,a₀,b₀,hunit,hnorm,ho₀,hbud₀,hm₀,hmin₀⟩ :=
    GlobalPlankMergeMinimum.exists_unit_minimum μ hC hne h c e hCW ho n B hmin
  have hGW (i) : 0<Plank.Body.width C (g i) := by rw [hunit]; norm_num
  obtain ⟨lo,hi,horder,hbudget,hmargin,hglobal,hactive⟩ :=
    GlobalPlankMergeMinimum.exists_least_active μ hC hCc hCV g a₀ b₀ hGW ho₀ n
      (hbud₀ ▸ hbud) hmin₀
  have hnegative : margin μ C g lo hi n B<0 := by rw [hmargin,hm₀]; exact hneg
  refine ⟨C,g,lo,hi,hC,hCc,hCV,hunit,hnorm,horder,hbudget,hnegative,hglobal,hactive,?_,?_⟩
  · have he : Module.finrank ℝ (Point n)=n := Module.finrank_fin_fun ℝ
    intro i hipos
    exact GlobalPlankBoundaryMinimum.active_window_interior μ (he.symm ▸ hn)
      hC hCc hCV g lo hi horder hGW hB hbudget (he.symm ▸ hnegative)
      (he.symm ▸ hglobal) i hipos
  · intro i j hij hipos hjpos u v hu hv
    exact GlobalPlankMergeMinimum.not_level_subset μ hC hne g hunit hnorm lo hi
      horder n hbudget hactive i j hij hipos hjpos u v hu hv

end Plank.FiniteDimensionalGlobalMinimum
