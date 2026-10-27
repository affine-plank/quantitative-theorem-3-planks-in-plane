/- Transfer actual global minima between different finite-dimensional
coordinate spaces using a verified positive volume factor. -/
module
public import GlobalPlankBodyMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalMinimumCoordinateTransport

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def pull (A : E ≃ᵃ[ℝ] F) (f : F →ᵃ[ℝ] ℝ) : E →ᵃ[ℝ] ℝ := f.comp A.toAffineMap

theorem width_pull (A : E ≃ᵃ[ℝ] F) (K : Set F) (f : F →ᵃ[ℝ] ℝ) :
    Body.width (A ⁻¹' K) (pull A f)=Body.width K f := by
  have he : pull A f '' (A ⁻¹' K)=f '' K := by
    change (f ∘ A) '' (A ⁻¹' K)=_
    rw [image_comp,image_preimage_eq _ A.surjective]
  change sSup (pull A f '' (A ⁻¹' K))-sInf (pull A f '' (A ⁻¹' K))=_
  rw [he]
  rfl

theorem gap_preimage (A : E ≃ᵃ[ℝ] F) (K : Set F)
    (f : ι → F →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    (A ⁻¹' K)\covered (fun i => pull A (f i)) lo hi=A ⁻¹' (K\covered f lo hi) := by
  ext x
  simp only [covered,pull,AffineMap.comp_apply,AffineEquiv.coe_toAffineMap,
    mem_sdiff,mem_preimage,mem_iUnion,mem_ofPred_eq]

variable [Fintype ι]

theorem budget_pull (A : E ≃ᵃ[ℝ] F) (K : Set F)
    (f : ι → F →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) :
    budget (A ⁻¹' K) (fun i => pull A (f i)) lo hi=budget K f lo hi := by
  simp only [budget,width_pull]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem margin_pull (μ : Measure F) (ν : Measure E)
    (A : E ≃ᵃ[ℝ] F) (c : ℝ) (hc : 0<c)
    (hscale : ∀ S,MeasurableSet S → μ.real S=c*ν.real (A ⁻¹' S))
    {K : Set F} (hK : MeasurableSet K) (f : ι → F →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (d : ℕ) (B : ℝ) :
    margin ν (A ⁻¹' K) (fun i => pull A (f i)) lo hi d B=margin μ K f lo hi d B := by
  have hcov : MeasurableSet (covered f lo hi) := MeasurableSet.iUnion fun i =>
    measurableSet_Icc.preimage (f i).continuous_of_finiteDimensional.measurable
  rw [margin,margin,gap_preimage,budget_pull,hscale K hK,hscale _ (hK.diff hcov),
    mul_div_mul_left _ _ hc.ne']

omit [BorelSpace E] in
/-- The global comparison includes every actual competitor in the new
space. Both body and plank data are transported, with the same budget and
exponent; the positive Jacobian factor cancels. -/
theorem global_minimum_pull (μ : Measure F) (ν : Measure E)
    (A : E ≃ᵃ[ℝ] F) (c : ℝ) (hc : 0<c)
    (hscale : ∀ S,MeasurableSet S → μ.real S=c*ν.real (A ⁻¹' S))
    {K : Set F} (hK : MeasurableSet K) (f : ι → F →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (d : ℕ) (B : ℝ)
    (hglobal : IsGlobalMinimum μ K f lo hi d B) :
    IsGlobalMinimum ν (A ⁻¹' K) (fun i => pull A (f i)) lo hi d B := by
  intro C g a b hC hCc hCV hCW hab hbudget
  let D := A '' C
  let h (i : ι) := pull A.symm (g i)
  have he : A ⁻¹' D=C := preimage_image_eq _ A.injective
  have hf : (fun i => pull A (h i))=g := by
    funext i
    ext x
    simp only [pull,h,AffineMap.comp_apply,AffineEquiv.coe_toAffineMap,A.symm_apply_apply]
  have hD : IsCompact D := hC.image A.toAffineMap.continuous_of_finiteDimensional
  have hDc : Convex ℝ D := hCc.affine_image A.toAffineMap
  have hDV : 0<μ.real D := by
    rw [hscale D hD.measurableSet,he]
    exact mul_pos hc hCV
  have hw (i) : Body.width D (h i)=Body.width C (g i) := by
    have hh := width_pull A D (h i)
    rw [he,show pull A (h i)=g i from congrFun hf i] at hh
    exact hh.symm
  have hb : budget D h a b=budget C g a b := by simp only [budget,hw]
  have hm := hglobal D h a b hD hDc hDV (fun i => by rw [hw i]; exact hCW i)
    hab (hb.symm ▸ hbudget)
  have hmargin := margin_pull μ ν A c hc hscale hD.measurableSet h a b d B
  rw [he,hf] at hmargin
  rw [margin_pull μ ν A c hc hscale hK f lo hi d B,hmargin]
  exact hm

end Plank.GlobalMinimumCoordinateTransport
