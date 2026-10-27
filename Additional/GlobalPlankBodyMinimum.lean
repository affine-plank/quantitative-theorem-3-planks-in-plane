/- Body minimization retains the actual body under support-preserving pruning.
The existence of a global minimum is not assumed implicitly or proved here. -/
module

public import PrunedPlankCounterexample

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalPlankBodyMinimum

open Set MeasureTheory PrunedPlankCounterexample

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

/-- The normalized quantitative margin on the domain whose budget is at most B. -/
def margin (μ : Measure E) (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (d : ℕ) (B : ℝ) : ℝ :=
  μ.real (K\covered f lo hi)/μ.real K-(B-budget K f lo hi)^d

/-- Comparison with all actual bodies and all physical plank configurations.
This is an explicit hypothesis; no compactness or existence claim is bundled in it. -/
def IsGlobalMinimum (μ : Measure E) (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (d : ℕ) (B : ℝ) : Prop :=
  ∀ (C : Set E) (g : ι → E →ᵃ[ℝ] ℝ) (a b : ι → ℝ),
    IsCompact C → Convex ℝ C → 0<μ.real C →
    (∀ i, 0<Body.width C (g i)) → (∀ i, a i≤b i) → budget C g a b≤B →
    margin μ K f lo hi d B≤margin μ C g a b d B

/-- Equal covered parts and a nonimproving gap ratio force equality of the
actual compact bodies. The removed set is not merely null in the conclusion. -/
theorem eq_of_pruned_ratio (μ : Measure E) [μ.IsAddHaarMeasure]
    {K C U : Set E} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hV : 0<μ.real K) (hC : IsCompact C) (hCV : 0<μ.real C) (hCK : C⊆K)
    (hU : MeasurableSet U) (hcover : C∩U=K∩U)
    (hcovered : μ.real (K\U)<μ.real K)
    (hmin : μ.real (K\U)/μ.real K≤μ.real (C\U)/μ.real C) : C=K := by
  have hcross := (div_le_div_iff₀ hV hCV).mp hmin
  have hdiff := CoveredSetPruning.gap_difference μ hK.measure_ne_top hCK hU hcover
  have hvol := measureReal_mono (μ := μ) hCK hK.measure_ne_top
  have heq : μ.real C=μ.real K := by
    by_contra hn
    have hd : 0<μ.real K-μ.real C := sub_pos.mpr (lt_of_le_of_ne hvol hn)
    have hc : 0<(μ.real K-μ.real (K\U))*(μ.real K-μ.real C) :=
      mul_pos (sub_pos.mpr hcovered) hd
    have hg : μ.real (C\U)=μ.real (K\U)-μ.real K+μ.real C := by
      linarith only [hdiff]
    rw [hg] at hcross
    nlinarith only [hcross,hc]
  exact ConvexMeasureRigidity.eq_of_full_measure μ hconv hC.isClosed hCK
    (ENNReal.toReal_pos_iff.mp hV).1 hK.measure_ne_top
    ((ENNReal.toReal_eq_toReal_iff' hC.measure_ne_top hK.measure_ne_top).mp heq)

/-- Every choice of actual support witnesses leaves a negative global minimum
unchanged under pruning. In particular, nonunique support faces may be used. -/
theorem prune_eq_self (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i, lo i≤hi i) (hW : ∀ i, 0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hB : B≤1) (hbudget : budget K f lo hi≤B)
    (hneg : margin μ K f lo hi d B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (P Q : ι → E) (hP : ∀ i, P i∈K) (hQ : ∀ i, Q i∈K)
    (hmax : ∀ i, IsMaxOn (f i) K (P i)) (hmin : ∀ i, IsMinOn (f i) K (Q i)) :
    SupportPruningGeometry.prune K (covered f lo hi) P Q=K := by
  let C := SupportPruningGeometry.prune K (covered f lo hi) P Q
  have hC : IsCompact C := SupportPruningGeometry.isCompact_prune hK hconv hP hQ
  have hCc : Convex ℝ C := SupportPruningGeometry.convex_prune _ _ _ _
  have hCK : C⊆K := SupportPruningGeometry.prune_subset hK.isClosed hconv hP hQ
  have hcover : C∩covered f lo hi=K∩covered f lo hi :=
    SupportPruningGeometry.prune_inter hK.isClosed hconv hP hQ
  have hw (i) : Body.width C (f i)=Body.width K (f i) :=
    SupportPruningGeometry.width_prune hK.isClosed hconv hP hQ f
      (fun i _ hx => hmax i hx) (fun i _ hx => hmin i hx) i
  have hb : budget C f lo hi=budget K f lo hi := by simp only [budget,hw]
  have hU : MeasurableSet (covered f lo hi) := by
    apply MeasurableSet.iUnion
    intro i
    exact ((isClosed_le continuous_const (f i).continuous_of_finiteDimensional).inter
      (isClosed_le (f i).continuous_of_finiteDimensional continuous_const)).measurableSet
  have hR : 0≤budget K f lo hi :=
    Finset.sum_nonneg (fun i _ => div_nonneg (sub_nonneg.mpr (horder i)) (hW i).le)
  have hcoef : (B-budget K f lo hi)^d≤1 :=
    pow_le_one₀ (sub_nonneg.mpr hbudget) (by linarith only [hB,hR])
  have hbad : μ.real (K\covered f lo hi)<(B-budget K f lo hi)^d*μ.real K :=
    (div_lt_iff₀ hV).mp (sub_neg.mp hneg)
  have hbadC := CoveredSetPruning.bad_transfer μ hK.measure_ne_top hCK hU hcover hcoef hbad
  have hCV : 0<μ.real C := by
    by_contra! hn
    have hz : μ.real C=0 := le_antisymm hn measureReal_nonneg
    rw [hz,mul_zero] at hbadC
    exact (not_lt_of_ge measureReal_nonneg) hbadC
  have hm := hglobal C f lo hi hC hCc hCV (fun i => by rw [hw i]; exact hW i)
    horder (hb ▸ hbudget)
  have hratio : μ.real (K\covered f lo hi)/μ.real K≤
      μ.real (C\covered f lo hi)/μ.real C := by
    unfold margin at hm
    rw [hb] at hm
    linarith only [hm]
  exact eq_of_pruned_ratio μ hK hconv hV hC hCV hCK hU hcover
    (hbad.trans_le (by nlinarith only [hcoef,hV])) hratio

omit [MeasurableSpace E] [BorelSpace E] in
private theorem exists_max_ne {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) (v : E)
    (hn : ¬(IsMaxOn f K v ∧ ∀ x∈K, f x=f v → x=v)) :
    ∃ p∈K, p≠v ∧ IsMaxOn f K p := by
  obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn hne f.continuous_of_finiteDimensional.continuousOn
  by_cases he : p=v
  · subst p
    have hother : ∃ x∈K, f x=f v ∧ x≠v := by
      by_contra h
      apply hn
      refine ⟨hmax,?_⟩
      intro x hx hval
      by_contra hxv
      exact h ⟨x,hx,hval,hxv⟩
    obtain ⟨x,hx,hval,hxv⟩ := hother
    exact ⟨x,hx,hxv,fun y hy => (hmax hy).trans_eq hval.symm⟩
  · exact ⟨p,hp,he,hmax⟩

omit [MeasurableSpace E] [BorelSpace E] in
private theorem exists_min_ne {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) (v : E)
    (hn : ¬(IsMinOn f K v ∧ ∀ x∈K, f x=f v → x=v)) :
    ∃ p∈K, p≠v ∧ IsMinOn f K p := by
  obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne f.continuous_of_finiteDimensional.continuousOn
  by_cases he : p=v
  · subst p
    have hother : ∃ x∈K, f x=f v ∧ x≠v := by
      by_contra h
      apply hn
      refine ⟨hmin,?_⟩
      intro x hx hval
      by_contra hxv
      exact h ⟨x,hx,hval,hxv⟩
    obtain ⟨x,hx,hval,hxv⟩ := hother
    exact ⟨x,hx,hxv,fun y hy => hval.trans_le (hmin hy)⟩
  · exact ⟨p,hp,he,hmin⟩

/-- An uncovered extreme point is a singleton support face for at least one
indexed direction. This does not assume all support faces are singletons,
positive gap, positive plank widths, or minimality in the plank count. -/
theorem uncovered_extreme_unique_support (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0<μ.real K) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i, lo i≤hi i) (hW : ∀ i, 0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hB : B≤1) (hbudget : budget K f lo hi≤B)
    (hneg : margin μ K f lo hi d B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    {v : E} (hv : v∈K.extremePoints ℝ\covered f lo hi) :
    ∃ i, (IsMaxOn (f i) K v ∧ ∀ x∈K, f i x=f i v → x=v) ∨
      (IsMinOn (f i) K v ∧ ∀ x∈K, f i x=f i v → x=v) := by
  classical
  by_contra hn
  have hnot (i) :
      ¬(IsMaxOn (f i) K v ∧ ∀ x∈K, f i x=f i v → x=v) ∧
      ¬(IsMinOn (f i) K v ∧ ∀ x∈K, f i x=f i v → x=v) :=
    ⟨fun h => hn ⟨i,Or.inl h⟩,fun h => hn ⟨i,Or.inr h⟩⟩
  choose P hP hPv hmax using fun i => exists_max_ne hK hne (f i) v (hnot i).1
  choose Q hQ hQv hmin using fun i => exists_min_ne hK hne (f i) v (hnot i).2
  have heq := prune_eq_self μ hK hconv hV f lo hi horder hW d hB hbudget hneg hglobal
    P Q hP hQ hmax hmin
  let S (i) : Set E := {x | lo i≤f i x ∧ f i x≤hi i}
  have hS (i) : IsClosed (S i) :=
    (isClosed_le continuous_const (f i).continuous_of_finiteDimensional).inter
      (isClosed_le (f i).continuous_of_finiteDimensional continuous_const)
  have hSc (i) : Convex ℝ (S i) := (convex_Icc (lo i) (hi i)).affine_preimage (f i)
  have hext := PrunedPlankExtremes.uncovered_extremes_subset hK hconv S hS hSc P Q
  change (SupportPruningGeometry.prune K (covered f lo hi) P Q).extremePoints ℝ\
    covered f lo hi⊆range P∪range Q at hext
  rw [heq] at hext
  rcases hext hv with ⟨i,hi⟩ | ⟨i,hi⟩
  · exact hPv i hi
  · exact hQv i hi

/-- A singleton upper or lower support face, with its actual point. -/
def UniqueSupport (K : Set E) (f : E →ᵃ[ℝ] ℝ) (upper : Bool) (v : E) : Prop :=
  v∈K ∧ (if upper then IsMaxOn f K v else IsMinOn f K v) ∧
    ∀ x∈K, f x=f v → x=v

/-- The indexed singleton faces. Repeated directions remain separately indexed. -/
def singletonFaces (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ) : Set (ι × Bool) :=
  {j | ∃ v, UniqueSupport K (f j.1) j.2 v}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem uniqueSupport_eq {K : Set E} {f : E →ᵃ[ℝ] ℝ} {upper : Bool} {v w : E}
    (hv : UniqueSupport K f upper v) (hw : UniqueSupport K f upper w) : v=w := by
  apply hw.2.2 v hv.1
  cases upper
  · exact le_antisymm (hv.2.1 hw.1) (hw.2.1 hv.1)
  · exact le_antisymm (hw.2.1 hv.1) (hv.2.1 hw.1)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A purely finite count: assigning each point to a singleton indexed support
face is injective, even if a point supports several of the directions. -/
theorem finite_ncard_le_singletonFaces {A K : Set E} (f : ι → E →ᵃ[ℝ] ℝ)
    (hA : ∀ v∈A, ∃ j : ι × Bool, UniqueSupport K (f j.1) j.2 v) :
    A.Finite ∧ A.ncard≤(singletonFaces K f).ncard := by
  classical
  have hs (v : A) : ∃ j : singletonFaces K f,
      UniqueSupport K (f j.val.1) j.val.2 v.val := by
    obtain ⟨j,hj⟩ := hA v.val v.property
    exact ⟨⟨j,⟨v.val,hj⟩⟩,hj⟩
  choose g hg using hs
  have hinj : Function.Injective g := by
    intro v w heq
    apply Subtype.ext
    have hw := hg w
    rw [←heq] at hw
    exact uniqueSupport_eq (hg v) hw
  let : Finite A := Finite.of_injective g hinj
  exact ⟨Set.toFinite A,Nat.card_le_card_of_injective g hinj⟩

/-- The uncovered-vertex bound uses only the singleton indexed faces: if t
of the 2m faces are singletons, there are at most t uncovered extreme points. -/
theorem uncovered_ncard_le_singletonFaces (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hV : 0<μ.real K) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i, lo i≤hi i) (hW : ∀ i, 0<Body.width K (f i))
    (d : ℕ) {B : ℝ} (hB : B≤1) (hbudget : budget K f lo hi≤B)
    (hneg : margin μ K f lo hi d B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi d B) :
    (K.extremePoints ℝ\covered f lo hi).Finite ∧
      (K.extremePoints ℝ\covered f lo hi).ncard≤(singletonFaces K f).ncard := by
  apply finite_ncard_le_singletonFaces f
  intro v hv
  obtain ⟨i,hi⟩ := uncovered_extreme_unique_support μ hK hconv hne hV f lo hi
    horder hW d hB hbudget hneg hglobal hv
  rcases hi with hmax | hmin
  · exact ⟨(i,true),extremePoints_subset hv.1,hmax⟩
  · exact ⟨(i,false),extremePoints_subset hv.1,hmin⟩

end Plank.GlobalPlankBodyMinimum

#print axioms Plank.GlobalPlankBodyMinimum.eq_of_pruned_ratio
#print axioms Plank.GlobalPlankBodyMinimum.prune_eq_self
#print axioms Plank.GlobalPlankBodyMinimum.uncovered_extreme_unique_support
#print axioms Plank.GlobalPlankBodyMinimum.uncovered_ncard_le_singletonFaces
