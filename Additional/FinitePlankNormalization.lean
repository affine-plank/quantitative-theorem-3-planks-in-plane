/- Physical finite plank families enter the compact parameter domain in
every finite dimension. Clipping changes only null support levels. -/
module

public import PhysicalPlankNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FinitePlankNormalization

open Set Metric MeasureTheory NormalizedPlankBodyMinimum
open PrunedPlankCounterexample (covered)
open PlanarNormalization (clip clip_bounds monotone_clip clip_sub_le mem_clipped_iff)
open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]

omit [Fintype ι] in
theorem exists_unit_form {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) (hW : 0<Body.width K f) :
    ∃ (g : E →ᵃ[ℝ] ℝ) (c : ℝ),
      (∀ x,g x=(f x-c)/Body.width K f) ∧
      (∀ x∈K,0≤g x ∧ g x≤1) ∧ Body.width K g=1 ∧ g.linear≠0 := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne f.continuous_of_finiteDimensional
  have hspan := Body.width_eq_of_realisers ha hb hmax hmin
  let g : E →ᵃ[ℝ] ℝ := (Body.width K f)⁻¹ • (f-AffineMap.const ℝ E (f b))
  have happly (x) : g x=(f x-f b)/Body.width K f := by simp [g,div_eq_mul_inv,mul_comm]
  have hbounds : ∀ x∈K,0≤g x ∧ g x≤1 := by
    intro x hx
    rw [happly]
    refine ⟨div_nonneg (sub_nonneg.mpr (hmin x hx)) hW.le,?_⟩
    apply (div_le_one hW).mpr
    rw [hspan]
    linarith only [hmax x hx]
  have hga : g a=1 := by rw [happly,← hspan,div_self hW.ne']
  have hgb : g b=0 := by rw [happly,sub_self,zero_div]
  refine ⟨g,f b,happly,hbounds,?_,?_⟩
  · rw [Body.width_eq_of_realisers ha hb
      (fun x hx => by rw [hga]; exact (hbounds x hx).2)
      (fun x hx => by rw [hgb]; exact (hbounds x hx).1),hga,hgb,sub_zero]
  · intro hz
    have he := g.linearMap_vsub a b
    rw [hz,LinearMap.zero_apply,hga,hgb] at he
    norm_num at he

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem gap_clip (K : Set E) (g : ι → E →ᵃ[ℝ] ℝ)
    (hg : ∀ i,(g i).linear≠0) (hnorm : ∀ i x,x∈K → 0≤g i x ∧ g i x≤1)
    (p : Endpoints (ι := ι)) :
    μ.real (K\covered g (fun i => clip (p.1 i)) (fun i => clip (p.2 i)))=
      μ.real (K\covered g p.1 p.2) := by
  classical
  let bad : Set E := ⋃ i,{x | g i x=0}∪{x | g i x=1}
  have hbad : μ bad=0 := measure_iUnion_null fun i => measure_union_null
    (ConvexExposedSections.measure_affine_level_eq_zero μ (g i) (hg i) 0)
    (ConvexExposedSections.measure_affine_level_eq_zero μ (g i) (hg i) 1)
  have hequiv (x : E) (hx : x∈K) (hb : x∉bad) (i : ι) :
      (clip (p.1 i)≤g i x ∧ g i x≤clip (p.2 i)) ↔ (p.1 i≤g i x ∧ g i x≤p.2 i) := by
    have hz : g i x≠0 := fun h => hb (mem_iUnion.mpr ⟨i,Or.inl h⟩)
    have ho : g i x≠1 := fun h => hb (mem_iUnion.mpr ⟨i,Or.inr h⟩)
    exact mem_clipped_iff (lt_of_le_of_ne (hnorm i x hx).1 hz.symm)
      (lt_of_le_of_ne (hnorm i x hx).2 ho)
  have he : (K\covered g (fun i => clip (p.1 i)) (fun i => clip (p.2 i)))\bad=
      (K\covered g p.1 p.2)\bad := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨hx.1.1,?_⟩,hx.2⟩
      intro hh
      obtain ⟨i,hi⟩ := mem_iUnion.mp hh
      exact hx.1.2 (mem_iUnion.mpr ⟨i,(hequiv x hx.1.1 hx.2 i).mpr hi⟩)
    · intro hx
      refine ⟨⟨hx.1.1,?_⟩,hx.2⟩
      intro hh
      obtain ⟨i,hi⟩ := mem_iUnion.mp hh
      exact hx.1.2 (mem_iUnion.mpr ⟨i,(hequiv x hx.1.1 hx.2 i).mp hi⟩)
  apply congrArg ENNReal.toReal
  exact (measure_sdiff_null hbad).symm.trans ((congrArg μ he).trans (measure_sdiff_null hbad))

omit [Fintype ι] in
theorem encode_unit_data {r R : ℝ} (hr : 0<r)
    (K : Body (E := E) r R) (g : ι → E →ᵃ[ℝ] ℝ)
    (hW : ∀ i,Plank.Body.width (K.1 : Set E) (g i)=1)
    (hbounds : ∀ i x,x∈(K.1 : Set E) → 0≤g i x ∧ g i x≤1)
    (p : Endpoints (ι := ι)) :
    ∃ q : Data (E := E) (ι := ι) r R,
      q.1=K ∧ q.2.2=p ∧ gap μ q=μ.real ((K.1 : Set E)\covered g p.1 p.2) := by
  choose u hu using fun i => PhysicalPlankNormalization.exists_direction
    K.1.isCompact K.1.nonempty (g i) (hW i) (hbounds i)
  let q : Data (E := E) (ι := ι) r R := (K,u,p)
  have he (i : ι) (x : E) : g i x=(form q i x-lower q i)/span q i := hu i x
  have hband (i : ι) (x : E) :
      (lo q i≤form q i x ∧ form q i x≤hi q i) ↔ (p.1 i≤g i x ∧ g i x≤p.2 i) := by
    rw [he]
    have hw := span_pos μ hr q i
    rw [le_div_iff₀ hw,div_le_iff₀ hw]
    change (lower q i+p.1 i*span q i≤form q i x ∧
      form q i x≤lower q i+p.2 i*span q i) ↔ _
    constructor <;> rintro ⟨hl,hh⟩ <;> constructor <;> linarith only [hl,hh]
  have hset : covered (form q) (lo q) (hi q)=covered g p.1 p.2 := by
    ext x
    simp only [covered,mem_iUnion,mem_ofPred_eq]
    exact exists_congr (fun i => hband i x)
  refine ⟨q,rfl,rfl,?_⟩
  change μ.real ((K.1 : Set E)\covered (form q) (lo q) (hi q))=_
  rw [hset]

/-- Actual compact parameters have no larger margin at the same budget and
exponent. The construction preserves the original body and gap measure. -/
theorem exists_data_le {r R : ℝ} (hr : 0<r)
    (K : Body (E := E) r R) (f : ι → E →ᵃ[ℝ] ℝ) (a b : ι → ℝ)
    (horder : ∀ i,a i≤b i) (hW : ∀ i,0<Plank.Body.width (K.1 : Set E) (f i))
    (d : ℕ) {B : ℝ} (hbudget : PrunedPlankCounterexample.budget (K.1 : Set E) f a b≤B) :
    ∃ q : Data (E := E) (ι := ι) r R, q∈domain B ∧
      margin μ d B q≤GlobalPlankBodyMinimum.margin μ (K.1 : Set E) f a b d B := by
  choose g c happly hnorm hunit hg using fun i => exists_unit_form
    K.1.isCompact K.1.nonempty (f i) (hW i)
  let p : Endpoints (ι := ι) :=
    (fun i => (a i-c i)/Plank.Body.width (K.1 : Set E) (f i),
     fun i => (b i-c i)/Plank.Body.width (K.1 : Set E) (f i))
  have ho (i) : p.1 i≤p.2 i :=
    (div_le_div_iff_of_pos_right (hW i)).mpr (sub_le_sub_right (horder i) _)
  have hcost : total p=PrunedPlankCounterexample.budget (K.1 : Set E) f a b := by
    unfold total PrunedPlankCounterexample.budget
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [p]
    ring
  have hset : covered g p.1 p.2=covered f a b := by
    ext x
    simp only [covered,mem_iUnion,mem_ofPred_eq]
    apply exists_congr
    intro i
    rw [happly]
    dsimp only [p]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  let pc : Endpoints (ι := ι) := (fun i => clip (p.1 i),fun i => clip (p.2 i))
  obtain ⟨q,hqK,hqp,hgap⟩ := encode_unit_data μ hr K g hunit hnorm pc
  have hle : total q.2.2≤PrunedPlankCounterexample.budget (K.1 : Set E) f a b := by
    rw [hqp,← hcost]
    exact Finset.sum_le_sum (fun i _ => clip_sub_le (ho i))
  have hgapeq : gap μ q=μ.real ((K.1 : Set E)\covered f a b) := by
    rw [hgap,gap_clip μ (K.1 : Set E) g hg hnorm p,hset]
  refine ⟨q,⟨mem_univ _,mem_univ _,?_,hle.trans hbudget⟩,?_⟩
  · rw [hqp]
    intro i
    exact ⟨(clip_bounds (p.1 i)).1,monotone_clip (ho i),(clip_bounds (p.2 i)).2⟩
  · have hp := pow_le_pow_left₀ (sub_nonneg.mpr hbudget) (sub_le_sub_left hle B) d
    unfold margin GlobalPlankBodyMinimum.margin
    rw [hgapeq]
    have he : (body q : Set E)=(K.1 : Set E) := by unfold body; rw [hqK]
    rw [he]
    exact sub_le_sub_left hp _

end Plank.FinitePlankNormalization
