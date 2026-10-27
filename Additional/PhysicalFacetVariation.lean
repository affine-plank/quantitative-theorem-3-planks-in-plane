/- Actual facet variation in arbitrary physical coordinates and dimension. -/
module
public import FiniteFacetExtension
public import FiniteDimensionalCutCoordinates
public import GlobalMinimumCoordinateTransport
public import AffineLevelCoincidence

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PhysicalFacetVariation

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum
open GlobalMinimumCoordinateTransport FiniteDimensionalCutCoordinates

variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype κ]

/-- At a positive-gap global minimum, a noncoincident actual facet cannot
be fully covered. Both the physical Haar transport and the convex extension
across the facet are constructed inside the proof. No cap estimate is assumed. -/
theorem not_fully_covered_facet (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K)
    (g : E →ᵃ[ℝ] ℝ) (hg : g.linear≠0)
    (H : κ → E →ᵃ[ℝ] ℝ) (c : κ → ℝ) (b : ℝ)
    (hrep : K={x | g x≤b ∧ ∀ j,H j x≤c j})
    (p : E) (hp : g p=b) (hstrict : ∀ j,H j p<c j)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hsep : ∀ i,(¬{x | g x=b}⊆{x | f i x=lo i}) ∧
      (¬{x | g x=b}⊆{x | f i x=hi i}))
    (hV : 0<μ.real K) (hW : ∀ i,0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi)) :
    ¬∀ x∈K,g x=b → x∈covered f lo hi := by
  classical
  obtain ⟨v,hv⟩ := exists_unit_vector g.linear hg
  let A := (split g.linear v hv).toAffineEquiv
  let ν : Measure g.linear.ker := Measure.addHaar
  let C := A ⁻¹' K
  let b' := b-g 0
  let f' (i : ι) := pull A (f i)
  let H' (j : κ) := pull A (H j)
  obtain ⟨s,hs,hscale⟩ := exists_volume_factor μ g.linear v hv
  have hA (z : ℝ × g.linear.ker) : g (A z)=z.1+g 0 := affine_split g v hv z
  have hfirst (x : E) : (A.symm x).1=g x-g 0 := by
    have he := hA (A.symm x)
    rw [A.apply_symm_apply] at he
    linarith only [he]
  have hcutpoint (x : E) (hx : g x=b) : A (b',(A.symm x).2)=x := by
    have he : (b',(A.symm x).2)=A.symm x := by
      apply Prod.ext
      · rw [hfirst,hx]
      · rfl
    rw [he,A.apply_symm_apply]
  have hC : IsCompact C := by
    have he : C=A.symm '' K := by
      ext x
      constructor
      · intro hx; exact ⟨A x,hx,A.symm_apply_apply x⟩
      · rintro ⟨x,hx,rfl⟩; simpa [C] using hx
    rw [he]
    exact hK.image A.symm.toAffineMap.continuous_of_finiteDimensional
  have hrepC : C={z | z.1≤b' ∧ ∀ j,H' j z≤c j} := by
    ext z
    simp only [C,mem_preimage,hrep,mem_ofPred_eq,H',pull,AffineMap.comp_apply,
      AffineEquiv.coe_toAffineMap,hA,b',le_sub_iff_add_le]
  have hstrictC (j : κ) : H' j (b',(A.symm p).2)<c j := by
    change H j (A (b',(A.symm p).2))<c j
    rw [hcutpoint p hp]
    exact hstrict j
  have hsepC (i : ι) : (¬∀ y,f' i (b',y)=lo i) ∧ (¬∀ y,f' i (b',y)=hi i) := by
    have hlevel (u : ℝ) (hn : ¬{x | g x=b}⊆{x | f i x=u}) :
        ¬∀ y,f' i (b',y)=u := by
      intro hh
      apply hn
      intro x hx
      have he := hh (A.symm x).2
      change f i (A (b',(A.symm x).2))=u at he
      rw [hcutpoint x hx] at he
      exact he
    exact ⟨hlevel _ (hsep i).1,hlevel _ (hsep i).2⟩
  have hCV : 0<(volume.prod ν).real C := by
    have he := hscale K hK.measurableSet
    exact (mul_pos_iff_of_pos_left hs).mp (he ▸ hV)
  have hCW (i) : 0<Body.width C (f' i) := by
    rw [show Body.width C (f' i)=Body.width K (f i) from width_pull A K (f i)]
    exact hW i
  have hbudgetC : budget C f' lo hi≤B := by
    rw [show budget C f' lo hi=budget K f lo hi from budget_pull A K f lo hi]
    exact hbudget
  have hglobalC : IsGlobalMinimum (volume.prod ν) C f' lo hi d B :=
    global_minimum_pull μ (volume.prod ν) A s hs hscale hK.measurableSet f lo hi d B hglobal
  have hgapC : 0<(volume.prod ν).real (C\covered f' lo hi) := by
    rw [show C\covered f' lo hi=A ⁻¹' (K\covered f lo hi) from gap_preimage A K f lo hi]
    have hcov : MeasurableSet (covered f lo hi) := MeasurableSet.iUnion fun i =>
      measurableSet_Icc.preimage (f i).continuous_of_finiteDimensional.measurable
    have he := hscale _ (hK.measurableSet.diff hcov)
    exact (mul_pos_iff_of_pos_left hs).mp (he ▸ hgap)
  intro hcover
  apply FiniteFacetExtension.not_fully_covered_facet ν hC H' c b' hrepC
    (A.symm p).2 hstrictC f' lo hi horder hsepC hCV hCW d hbudgetC hglobalC hgapC
  intro y hy
  have he : g (A (b',y))=b := by rw [hA]; dsimp [b']; ring
  have hh := hcover (A (b',y)) hy he
  simpa only [covered,f',pull,AffineMap.comp_apply,AffineEquiv.coe_toAffineMap,
    mem_iUnion,mem_ofPred_eq] using hh

/-- Full coverage forces an actual plank boundary to contain the facet
hyperplane. Parallelism alone is not enough. -/
theorem exists_coincident_boundary (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K)
    (g : E →ᵃ[ℝ] ℝ) (hg : g.linear≠0)
    (H : κ → E →ᵃ[ℝ] ℝ) (c : κ → ℝ) (b : ℝ)
    (hrep : K={x | g x≤b ∧ ∀ j,H j x≤c j})
    (p : E) (hp : g p=b) (hstrict : ∀ j,H j p<c j)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hV : 0<μ.real K) (hW : ∀ i,0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi))
    (hcover : ∀ x∈K,g x=b → x∈covered f lo hi) :
    ∃ i,({x | g x=b}⊆{x | f i x=lo i}) ∨ ({x | g x=b}⊆{x | f i x=hi i}) := by
  by_contra! hn
  exact not_fully_covered_facet μ hK g hg H c b hrep p hp hstrict f lo hi horder
    hn hV hW d hbudget hglobal hgap hcover

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A coincident nonconstant affine level on a supporting hyperplane is the
same hyperplane and supplies a support direction, with either sign. -/
theorem support_of_level {K : Set E} (g f : E →ᵃ[ℝ] ℝ)
    (hg : g.linear≠0) (hf : f.linear≠0) (b u : ℝ)
    (hlevel : ∀ x,g x=b → f x=u) (p : E) (hp : g p=b)
    (hside : ∀ x∈K,g x≤b) :
    (IsMaxOn f K p ∨ IsMinOn f K p) ∧ ∀ x,g x=b ↔ f x=f p := by
  obtain ⟨q,c,hrel⟩ := AffineLevelCoincidence.affine_relation g f hg b u hlevel
  have hq : q≠0 := by
    intro hz
    apply hf
    ext x
    change f.linear x=0
    have he := f.linearMap_vsub x 0
    change f.linear (x-0)=f x-f 0 at he
    simpa only [sub_zero,hrel,hz,zero_mul,zero_add,sub_self] using he
  constructor
  · by_cases hpos : 0≤q
    · left
      intro x hx
      change f x≤f p
      rw [hrel,hrel,hp]
      exact add_le_add (mul_le_mul_of_nonneg_left (hside x hx) hpos) le_rfl
    · right
      intro x hx
      change f p≤f x
      rw [hrel,hrel,hp]
      exact add_le_add (mul_le_mul_of_nonpos_left (hside x hx) (le_of_not_ge hpos)) le_rfl
  · intro x
    rw [hrel,hrel,hp]
    constructor
    · intro hx; rw [hx]
    · intro he
      exact mul_left_cancel₀ hq (add_right_cancel he)

/-- Every fully covered specified facet at a positive-gap global minimum
is exactly an indexed upper or lower support face of a plank direction.
This is an all-dimensional replacement for the planar thin-cap estimate. -/
theorem covered_facet_is_support (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K)
    (g : E →ᵃ[ℝ] ℝ) (hg : g.linear≠0)
    (H : κ → E →ᵃ[ℝ] ℝ) (c : κ → ℝ) (b : ℝ)
    (hrep : K={x | g x≤b ∧ ∀ j,H j x≤c j})
    (p : E) (hp : g p=b) (hstrict : ∀ j,H j p<c j)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hV : 0<μ.real K) (hW : ∀ i,0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi))
    (hcover : ∀ x∈K,g x=b → x∈covered f lo hi) :
    ∃ i,(IsMaxOn (f i) K p ∨ IsMinOn (f i) K p) ∧
      K∩{x | g x=b}=K∩{x | f i x=f i p} := by
  have hpK : p∈K := by rw [hrep]; exact ⟨hp.le,fun j => (hstrict j).le⟩
  have hside (x : E) (hx : x∈K) : g x≤b := by rw [hrep] at hx; exact hx.1
  obtain ⟨i,hboundary⟩ := exists_coincident_boundary μ hK g hg H c b hrep p hp hstrict
    f lo hi horder hV hW d hbudget hglobal hgap hcover
  have hfi := AffineLevelCoincidence.linear_ne_zero_of_width_pos hK ⟨p,hpK⟩ (f i) (hW i)
  have hs : (IsMaxOn (f i) K p ∨ IsMinOn (f i) K p) ∧ ∀ x,g x=b ↔ f i x=f i p := by
    rcases hboundary with hlo | hhi
    · exact support_of_level g (f i) hg hfi b (lo i) hlo p hp hside
    · exact support_of_level g (f i) hg hfi b (hi i) hhi p hp hside
  refine ⟨i,hs.1,?_⟩
  ext x
  exact and_congr_right (fun _ => hs.2 x)

end Plank.PhysicalFacetVariation
