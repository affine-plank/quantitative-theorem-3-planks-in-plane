/- Supporting-section balance at arbitrary global quantitative minima.
No convex extension or polyhedral representation is assumed. -/
module
public import SupportingFaceResidual
public import GlobalPlankBodyEnlargement
public import GlobalSupportingCut

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalSupportingFaceBalance

open Set MeasureTheory Filter ConvexSections PrunedPlankCounterexample GlobalPlankBodyMinimum
open SupportingFaceEnlargement SupportingFaceResidual
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

/-- Outward convex-hull competitors force the reverse density comparison
on every supporting section whose plane is not a plank boundary. Widths
may increase; selected-extremum witnesses are not needed for this direction. -/
theorem section_ge (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    (b : ℝ) (htop : ∀ p∈K,p.1≤b)
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hV : 0<(volume.prod ν).real K) (hW : ∀ i,0<Body.width K (f i))
    (hsep : ∀ i,(¬∀ y,f i (b,y)=lo i) ∧ (¬∀ y,f i (b,y)=hi i))
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum (volume.prod ν) K f lo hi d B) :
    (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K*ν.real (fiber K b)≤
      ν.real (fiber (K\covered f lo hi) b) := by
  classical
  let μ : Measure (ℝ × E) := volume.prod ν
  have hfull : (interior K).Nonempty := by
    by_contra hn
    have hs : K⊆frontier K := by
      rw [frontier,not_nonempty_iff_eq_empty.mp hn,sdiff_empty]
      exact subset_closure
    have hz := measure_mono_null hs (hc.addHaar_frontier μ)
    change (volume.prod ν) K=0 at hz
    simp [Measure.real,hz] at hV
  have hU : MeasurableSet (covered f lo hi) := by
    apply MeasurableSet.iUnion
    intro i
    exact ((isClosed_le continuous_const (f i).continuous_of_finiteDimensional).inter
      (isClosed_le (f i).continuous_of_finiteDimensional continuous_const)).measurableSet
  have htrace : ∀ᵐ y ∂ν,∀ᶠ t in 𝓝 b,(t,y)∈covered f lo hi ↔ (b,y)∈covered f lo hi := by
    simpa [covered] using ae_eventually_plank_mem_iff ν b Finset.univ f lo hi (fun i _ => hsep i)
  apply le_of_forall_inner_caps ν (compact_fiber hK b) (convex_fiber hc b)
  intro A hA hAc hAi
  apply le_section_of_added_lower ν hK hc hfull htop hA hAc hAi hU htrace
  intro ε hε
  have hv := (added_volume_bounds ν hK hc htop hA hAc (hAi.trans interior_subset) hε.le).1
  have hq : 0≤μ.real (K\covered f lo hi)/μ.real K := div_nonneg measureReal_nonneg hV.le
  have hg := GlobalPlankBodyEnlargement.added_gap_ge μ hK hV
    (compact_enlargement hK hc b hA hAc ε) (convex_enlargement K b A ε)
    (subset_enlargement K b A ε) f lo hi horder hW d hbudget hglobal
  calc (μ.real (K\covered f lo hi)/μ.real K*ν.real A)*ε =
        (μ.real (K\covered f lo hi)/μ.real K)*(ε*ν.real A) := by ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left hv hq).trans hg

/-- A supporting section has the body's exact uncovered fraction when all
selected extrema have witnesses strictly below the supporting plane. -/
theorem section_eq (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    (b : ℝ) (htop : ∀ p∈K,p.1≤b) (y : E) (hyK : (b,y)∈K)
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hV : 0<(volume.prod ν).real K) (hW : ∀ i,0<Body.width K (f i))
    (P Q : ι → ℝ × E) (hP : ∀ i,P i∈K) (hQ : ∀ i,Q i∈K)
    (hmax : ∀ i,∀ x∈K,f i x≤f i (P i)) (hmin : ∀ i,∀ x∈K,f i (Q i)≤f i x)
    (hPb : ∀ i,(P i).1<b) (hQb : ∀ i,(Q i).1<b)
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum (volume.prod ν) K f lo hi d B) :
    ν.real (fiber (K\covered f lo hi) b)=
      (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K*ν.real (fiber K b) := by
  have hle := GlobalSupportingCut.convex_moment_le ν hK hc b htop y hyK
    f lo hi horder hV hW P Q hP hQ hmax hmin hPb hQb d hbudget hglobal
    (fun _ => 1) continuous_const (fun _ _ => zero_le_one) (convexOn_const 1 convex_univ)
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one] at hle
  apply le_antisymm hle
  apply section_ge ν hK hc b htop f lo hi horder hV hW _ d hbudget hglobal
  intro j
  exact ⟨GlobalBodyCutEquilibrium.nonconstant_on_cut (f j) hyK (hW j)
      (hP j) (hQ j) (hmax j) (hmin j) (hPb j) (hQb j) _,
    GlobalBodyCutEquilibrium.nonconstant_on_cut (f j) hyK (hW j)
      (hP j) (hQ j) (hmax j) (hmin j) (hPb j) (hQb j) _⟩

/-- The convex section-moment comparison holds for signed continuous convex
observables. Exact area balance cancels the constant used in the inward cut. -/
theorem convex_moment_le (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    (b : ℝ) (htop : ∀ p∈K,p.1≤b) (y : E) (hyK : (b,y)∈K)
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hV : 0<(volume.prod ν).real K) (hW : ∀ i,0<Body.width K (f i))
    (P Q : ι → ℝ × E) (hP : ∀ i,P i∈K) (hQ : ∀ i,Q i∈K)
    (hmax : ∀ i,∀ x∈K,f i x≤f i (P i)) (hmin : ∀ i,∀ x∈K,f i (Q i)≤f i x)
    (hPb : ∀ i,(P i).1<b) (hQb : ∀ i,(Q i).1<b)
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum (volume.prod ν) K f lo hi d B)
    (h : E → ℝ) (hh : Continuous h) (hconv : ConvexOn ℝ univ h) :
    (∫ y in fiber (K\covered f lo hi) b,h y ∂ν)≤
      (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K*
        ∫ y in fiber K b,h y ∂ν := by
  let F := fiber K b
  let R := fiber (K\covered f lo hi) b
  have hF : IsCompact F := compact_fiber hK b
  have hRF : R⊆F := preimage_mono sdiff_subset
  have hFR : ν R≠⊤ := measure_ne_top_of_subset hRF hF.measure_ne_top
  obtain ⟨z,hz,hminh⟩ := hF.exists_isMinOn ⟨y,hyK⟩ hh.continuousOn
  have hhF : IntegrableOn h F ν := hh.continuousOn.integrableOn_compact hF
  have hhR : IntegrableOn h R ν := hhF.mono_set hRF
  have hs := GlobalSupportingCut.convex_moment_le ν hK hc b htop y hyK
    f lo hi horder hV hW P Q hP hQ hmax hmin hPb hQb d hbudget hglobal
    (fun w => h w+(-h z)) (hh.add continuous_const)
    (fun w hw => by have hm : h z≤h w := hminh hw; linarith)
    (hconv.add (convexOn_const (-h z) convex_univ))
  have he := section_eq ν hK hc b htop y hyK f lo hi horder hV hW
    P Q hP hQ hmax hmin hPb hQb d hbudget hglobal
  change (∫ w in R,h w+(-h z) ∂ν)≤
    (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K*
      ∫ w in F,h w+(-h z) ∂ν at hs
  rw [integral_add hhR (integrableOn_const hFR),
    integral_add hhF (integrableOn_const hF.measure_ne_top)] at hs
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hs
  change ν.real R=_ at he
  change (∫ w in R,h w ∂ν)+ν.real R*(-h z)≤
    (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K*
      ((∫ w in F,h w ∂ν)+ν.real F*(-h z)) at hs
  rw [he,mul_add,mul_assoc] at hs
  exact (add_le_add_iff_right _).mp hs

/-- Every affine section moment balances exactly without assuming that
the body admits a convex extension across the supporting plane. -/
theorem affine_moment_eq (ν : Measure E) [ν.IsAddHaarMeasure]
    {K : Set (ℝ × E)} (hK : IsCompact K) (hc : Convex ℝ K)
    (b : ℝ) (htop : ∀ p∈K,p.1≤b) (y : E) (hyK : (b,y)∈K)
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (horder : ∀ i,lo i≤hi i)
    (hV : 0<(volume.prod ν).real K) (hW : ∀ i,0<Body.width K (f i))
    (P Q : ι → ℝ × E) (hP : ∀ i,P i∈K) (hQ : ∀ i,Q i∈K)
    (hmax : ∀ i,∀ x∈K,f i x≤f i (P i)) (hmin : ∀ i,∀ x∈K,f i (Q i)≤f i x)
    (hPb : ∀ i,(P i).1<b) (hQb : ∀ i,(Q i).1<b)
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum (volume.prod ν) K f lo hi d B)
    (h : E →ᵃ[ℝ] ℝ) :
    (∫ y in fiber (K\covered f lo hi) b,h y ∂ν)=
      (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K*
        ∫ y in fiber K b,h y ∂ν := by
  have hcv (g : E →ᵃ[ℝ] ℝ) : ConvexOn ℝ univ g := by
    simpa only [preimage_univ,Function.comp_def,id_eq] using
      (convexOn_id (𝕜 := ℝ) (s := (univ : Set ℝ)) convex_univ).comp_affineMap g
  have hp := convex_moment_le ν hK hc b htop y hyK f lo hi horder hV hW
    P Q hP hQ hmax hmin hPb hQb d hbudget hglobal h h.continuous_of_finiteDimensional (hcv h)
  have hn := convex_moment_le ν hK hc b htop y hyK f lo hi horder hV hW
    P Q hP hQ hmax hmin hPb hQb d hbudget hglobal (-h) (-h).continuous_of_finiteDimensional (hcv (-h))
  change (∫ y in fiber (K\covered f lo hi) b,-(h y) ∂ν)≤
    (volume.prod ν).real (K\covered f lo hi)/(volume.prod ν).real K*
      ∫ y in fiber K b,-(h y) ∂ν at hn
  simp only [integral_neg,mul_neg,neg_le_neg_iff] at hn
  exact le_antisymm hp hn

end Plank.GlobalSupportingFaceBalance
