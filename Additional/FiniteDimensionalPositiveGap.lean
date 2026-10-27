/- Positive uncovered volume at an actual regular negative minimum in
any finite dimension and for any finite plank family. -/
module
public import ActivePlankRestriction
public import FiniteDimensionalGlobalMinimum
public import FiniteDimensionalEndpointDerivative

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalPositiveGap

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum
open FiniteDimensionalEndpointDerivative
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Moving one upper endpoint changes its normalized cost linearly. -/
theorem budget_update_upper [DecidableEq ι] (K : Set E)
    (f : ι → E →ᵃ[ℝ] ℝ) (hunit : ∀ j,Body.width K (f j)=1)
    (lo hi : ι → ℝ) (i : ι) (t : ℝ) :
    budget K f lo (Function.update hi i t)=budget K f lo hi+t-hi i := by
  have he : (fun j => Function.update hi i t j-lo j)=
      Function.update (fun j => hi j-lo j) i (t-lo i) := by
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj]
  simp only [budget,hunit,div_one]
  rw [he,Finset.sum_update_of_mem (Finset.mem_univ i),Finset.sdiff_singleton_eq_erase]
  have hh := Finset.sum_erase_add Finset.univ (fun j => hi j-lo j) (Finset.mem_univ i)
  linarith only [hh]

/-- Remove inactive null windows, retaining the distinguished moving plank. -/
theorem gap_update_restrict (μ : Measure E) [μ.IsAddHaarMeasure] [DecidableEq ι]
    (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ) (hf : ∀ j,(f j).linear≠0)
    (lo hi : ι → ℝ) (i : ι) (hipos : lo i<hi i) (t : ℝ) :
    μ.real (K\covered f lo (Function.update hi i t))=
      μ.real (gap K (f i) (fun j : {j // lo j<hi j ∧ j≠i} => f j)
        (fun j => lo j) (fun j => hi j) (lo i) t) := by
  classical
  have hzero (j : ι) (hj : ¬lo j<hi j) : Function.update hi i t j≤lo j := by
    have hji : j≠i := fun h => hj (h ▸ hipos)
    simpa [hji] using le_of_not_gt hj
  rw [←ActivePlankRestriction.gap_restrict_to μ (fun j => lo j<hi j)
    K f lo (Function.update hi i t) hf hzero]
  congr 1
  ext x
  simp only [covered,gap,mem_sdiff,mem_iUnion,mem_ofPred_eq,not_exists]
  constructor
  · rintro ⟨hx,hn⟩
    refine ⟨⟨hx,fun j hj => hn ⟨j,j.property.1⟩ ?_⟩,?_⟩
    · simpa [j.property.2] using hj
    · simpa using hn ⟨i,hipos⟩
  · rintro ⟨⟨hx,hn⟩,hi⟩
    refine ⟨hx,?_⟩
    intro j hj
    by_cases he : j.val=i
    · subst i
      exact hi (by simpa using hj)
    · exact hn ⟨j,⟨j.property,he⟩⟩ (by simpa [he] using hj)

/-- No zero gap is possible at an actual negative minimum with separated,
interior active windows. Only one endpoint derivative is needed. -/
theorem positive_gap_of_regular (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (hunit : ∀ j,Body.width K (f j)=1)
    (lo hi : ι → ℝ) (ho : ∀ j,lo j≤hi j) (n : ℕ) (hn : 0<n) {B : ℝ}
    (hbudget : budget K f lo hi≤B) (hneg : margin μ K f lo hi n B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi n B)
    (hint : ∀ i,lo i<hi i → (∃ x∈K,f i x<lo i) ∧ (∃ y∈K,hi i<f i y))
    (hsep : ∀ i j,i≠j → lo i<hi i → lo j<hi j → ∀ u v,
      u=lo i ∨ u=hi i → v=lo j ∨ v=hi j → ¬∀ x,f i x=u → f j x=v) :
    0<μ.real (K\covered f lo hi) := by
  classical
  have hne : K.Nonempty := by
    by_contra h
    simp [not_nonempty_iff_eq_empty.mp h,Measure.real] at hV
  have hW (j) : 0<Body.width K (f j) := by rw [hunit]; norm_num
  have hf (j) : (f j).linear≠0 :=
    AffineLevelCoincidence.linear_ne_zero_of_width_pos hK hne (f j) (hW j)
  have hRB : budget K f lo hi<B := by
    by_contra! h
    have he : B-budget K f lo hi=0 := sub_eq_zero.mpr (le_antisymm h hbudget)
    have hh : μ.real (K\covered f lo hi)/μ.real K<0 := by
      simpa only [margin,he,zero_pow (Nat.ne_of_gt hn),sub_zero] using hneg
    exact (not_lt_of_ge (div_nonneg measureReal_nonneg hV.le)) hh
  by_contra! hz
  have hzero : μ.real (K\covered f lo hi)=0 := le_antisymm hz measureReal_nonneg
  obtain ⟨i,hipos⟩ : ∃ i,lo i<hi i := by
    by_contra! h
    have hh := ActivePlankRestriction.gap_restrict_to μ (fun _ : ι => False)
      K f lo hi hf (fun j _ => h j)
    have hcov : covered (fun j : {j : ι // False} => f j)
        (fun j => lo j) (fun j => hi j)=∅ := by
      ext x; simp [covered]
    rw [hcov,sdiff_empty,hzero] at hh
    exact hV.ne' hh
  let J := {j // lo j<hi j ∧ j≠i}
  let G (t : ℝ) := μ.real (K\covered f lo (Function.update hi i t))
  have hdiff : DifferentiableAt ℝ G (hi i) := by
    obtain ⟨⟨x,hx,hxl⟩,hright⟩ := hint i hipos
    have hD := differentiableAt_upper μ hK hc hV (f i) (hf i)
      (fun j : J => f j) (fun j => lo j) (fun j => hi j) hipos
      ⟨x,hx,hxl.trans hipos⟩ hright (fun j =>
        ⟨hsep i j (Ne.symm j.property.2) hipos j.property.1 _ _
          (Or.inr rfl) (Or.inl rfl),
         hsep i j (Ne.symm j.property.2) hipos j.property.1 _ _
          (Or.inr rfl) (Or.inr rfl)⟩)
    exact hD.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (gap_update_restrict μ K f hf lo hi i hipos))
  have hGi : G (hi i)=0 := by simpa [G] using hzero
  have hGmin : IsLocalMin G (hi i) := Filter.Eventually.of_forall fun t => by
    rw [hGi]; exact measureReal_nonneg
  have hD := hdiff.hasDerivAt
  rw [hGmin.hasDerivAt_eq_zero hD] at hD
  let R := budget K f lo hi
  let M (t : ℝ) := G t/μ.real K-(B-(R+t-hi i))^n
  have hM : HasDerivAt M ((n : ℝ)*(B-R)^(n-1)) (hi i) := by
    have hh := (hD.div_const (μ.real K)).sub
      (((hasDerivAt_const (hi i) B).sub
        (((hasDerivAt_const (hi i) R).add (hasDerivAt_id (hi i))).sub_const (hi i))).pow n)
    convert hh using 1 <;> first | rfl | simp
  have hMmin : IsLocalMin M (hi i) := by
    have hcont : Continuous (fun t : ℝ => R+t-hi i) := by fun_prop
    filter_upwards [eventually_gt_nhds hipos,
      (isOpen_lt hcont continuous_const).mem_nhds (by simpa using hRB)] with t ht hbt
    have horder (j) : lo j≤Function.update hi i t j := by
      by_cases hj : j=i
      · subst j; simpa using ht.le
      · simpa [hj] using ho j
    have hbud : budget K f lo (Function.update hi i t)≤B := by
      rw [budget_update_upper K f hunit]; exact hbt.le
    have hh := hglobal K f lo (Function.update hi i t) hK hc hV hW horder hbud
    change M (hi i)≤M t
    simpa only [margin,budget_update_upper K f hunit,Function.update_eq_self,
      M,G,R,add_sub_cancel_right] using hh
  have hz := hMmin.hasDerivAt_eq_zero hM
  exact (ne_of_gt (mul_pos (Nat.cast_pos.mpr hn) (pow_pos (sub_pos.mpr hRB) _))) hz

/-- Least-active global minimization supplies all regularity hypotheses.
The exponent is the positive ambient dimension. -/
theorem positive_gap (μ : Measure E) [μ.IsAddHaarMeasure]
    (hn : 0<Module.finrank ℝ E) {K : Set E} (hK : IsCompact K)
    (hc : Convex ℝ K) (hV : 0<μ.real K) (f : ι → E →ᵃ[ℝ] ℝ)
    (hunit : ∀ j,Body.width K (f j)=1)
    (hnorm : ∀ j x,x∈K → 0≤f j x ∧ f j x≤1)
    (lo hi : ι → ℝ) (ho : ∀ j,lo j≤hi j) {B : ℝ} (hB : B≤1)
    (hbudget : budget K f lo hi≤B)
    (hneg : margin μ K f lo hi (Module.finrank ℝ E) B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi (Module.finrank ℝ E) B)
    (hactive : GlobalPlankMergeMinimum.LeastActive μ K f lo hi (Module.finrank ℝ E) B) :
    0<μ.real (K\covered f lo hi) := by
  have hne : K.Nonempty := by
    by_contra h
    simp [not_nonempty_iff_eq_empty.mp h,Measure.real] at hV
  have hW (i) : 0<Body.width K (f i) := by rw [hunit]; norm_num
  apply positive_gap_of_regular μ hK hc hV f hunit lo hi ho
    (Module.finrank ℝ E) hn hbudget hneg hglobal
  · exact GlobalPlankBoundaryMinimum.active_window_interior μ hn
      hK hc hV f lo hi ho hW hB hbudget hneg hglobal
  · intro i j hij hipos hjpos u v hu hv
    exact GlobalPlankMergeMinimum.not_level_subset μ hK hne f hunit hnorm lo hi ho
      (Module.finrank ℝ E) hbudget hactive i j hij hipos hjpos u v hu hv

/-- Any strict failure yields a negative global minimum with positive
uncovered volume, uniformly in dimension and plank count. -/
theorem exists_negative_minimum_positive_gap {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [μ.IsAddHaarMeasure] (hn : 0<n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → (Fin n → ℝ) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hW : ∀ i,0<Body.width K (f i)) (ho : ∀ i,lo i≤hi i) {B : ℝ}
    (hB : B≤1) (hbudget : budget K f lo hi≤B) (hneg : margin μ K f lo hi n B<0) :
    ∃ (C : Set (Fin n → ℝ)) (g : ι → (Fin n → ℝ) →ᵃ[ℝ] ℝ) (a b : ι → ℝ),
      IsCompact C ∧ Convex ℝ C ∧ 0<μ.real C ∧
      (∀ i,Body.width C (g i)=1) ∧ (∀ i x,x∈C → 0≤g i x ∧ g i x≤1) ∧
      (∀ i,a i≤b i) ∧ budget C g a b≤B ∧ margin μ C g a b n B<0 ∧
      IsGlobalMinimum μ C g a b n B ∧
      GlobalPlankMergeMinimum.LeastActive μ C g a b n B ∧
      0<μ.real (C\covered g a b) := by
  obtain ⟨C,g,a,b,hC,hCc,hCV,hunit,hnorm,hab,hbud,hnegative,hglobal,hactive,hint,hsep⟩ :=
    FiniteDimensionalGlobalMinimum.exists_negative_minimum_with_separated_active_windows
      μ hn hK hc hV f lo hi hW ho hB hbudget hneg
  exact ⟨C,g,a,b,hC,hCc,hCV,hunit,hnorm,hab,hbud,hnegative,hglobal,hactive,
    positive_gap_of_regular μ hC hCc hCV g hunit a b hab n hn hbud hnegative hglobal hint hsep⟩

end Plank.FiniteDimensionalPositiveGap
