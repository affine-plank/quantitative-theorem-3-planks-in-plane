/- Positive-gap negative global minima are finite convex hulls directly from
boundary ruling and the uncovered-support count, before any halfspace envelope. -/
module
public import PlanarBoundaryStrip
public import GlobalBodyBoundaryRuling
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarRuledMinimum

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum
open PlanarStripVertices (Plane)

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A nonconstant affine form in a two-dimensional space is the first
coordinate of a linear chart, up to its value at the origin. -/
theorem exists_plank_chart (hdim : Module.finrank ℝ E=2)
    (f : E →ᵃ[ℝ] ℝ) (hf : f.linear≠0) :
    ∃ A : Plane ≃ₗ[ℝ] E, ∀ x,f (A x)=x.1+f 0 := by
  obtain ⟨v,hv⟩ : ∃ v,f.linear v=1 := by
    obtain ⟨x,hx⟩ : ∃ x,f.linear x≠0 := by
      by_contra! hn
      exact hf (LinearMap.ext hn)
    exact ⟨(f.linear x)⁻¹ • x,by simp [hx]⟩
  have hdker := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hd : Module.finrank ℝ ℝ=Module.finrank ℝ f.linear.ker := by
    rw [Module.finrank_self,hdim] at *
    omega
  let V : ℝ ≃ₗ[ℝ] f.linear.ker := LinearEquiv.ofFinrankEq ℝ f.linear.ker hd
  let S : (ℝ × f.linear.ker) ≃ₗ[ℝ] E :=
    { toFun := fun p => p.1 • v+p.2
      invFun := fun x => (f.linear x,⟨x-f.linear x • v,by simp [hv]⟩)
      map_add' := by intro p q; simp [add_smul]; abel
      map_smul' := by intro r p; simp [smul_add,smul_smul]
      left_inv := by intro p; ext <;> simp [hv]
      right_inv := by intro x; simp }
  let A := (LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ) V).trans S
  refine ⟨A,?_⟩
  intro x
  have he := congrFun f.decomp (A x)
  change f (A x)=f.linear (x.1 • v+V x.2)+f 0 at he
  simpa [hv] using he

/-- Transfer the six-point strip count through the physical affine chart. -/
theorem closed_strip_extremes_of_chart (A : Plane ≃ₗ[ℝ] E)
    (g : E →ᵃ[ℝ] ℝ) (k : ℝ) (hA : ∀ x,g (A x)=x.1+k)
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (hint : (interior K).Nonempty) (a b : ℝ)
    (hrule : ∀ p∈frontier K,g p∈Ioo a b →
      ∃ z∈frontier K,g z∉Ioo a b ∧ segment ℝ p z⊆frontier K) :
    (K.extremePoints ℝ∩{x | g x∈Icc a b}).Finite ∧
      (K.extremePoints ℝ∩{x | g x∈Icc a b}).ncard≤6 := by
  let C := A.symm '' K
  have hmem (x : Plane) : x∈C ↔ A x∈K := by
    constructor
    · rintro ⟨y,hy,rfl⟩; simpa using hy
    · intro hx; exact ⟨A x,hx,A.symm_apply_apply x⟩
  have hC : IsCompact C := hK.image A.symm.continuous_of_finiteDimensional
  have hcC : Convex ℝ C := hc.linear_image A.symm.toLinearMap
  have hintC : (interior C).Nonempty := by
    have he : A.symm '' interior K=interior C :=
      A.symm.toContinuousLinearEquiv.toHomeomorph.image_interior K
    exact he ▸ hint.image A.symm
  have hfront : A.symm '' frontier K=frontier C :=
    A.symm.toContinuousLinearEquiv.toHomeomorph.image_frontier K
  have hfm (x : Plane) : x∈frontier C ↔ A x∈frontier K := by
    rw [←hfront]
    constructor
    · rintro ⟨y,hy,rfl⟩; simpa using hy
    · intro hx; exact ⟨A x,hx,A.symm_apply_apply x⟩
  have hrC : PlanarBoundaryStrip.ReachesBoundary C (a-k) (b-k) := by
    intro p hp hpab
    have hab : g (A p)∈Ioo a b := by
      rw [hA]
      constructor <;> linarith [hpab.1,hpab.2]
    obtain ⟨z,hz,hzab,hseg⟩ := hrule (A p) ((hfm p).mp hp) hab
    refine ⟨A.symm z,?_,?_,?_⟩
    · exact (hfm _).mpr (by simpa using hz)
    · intro hza
      apply hzab
      have hg := hA (A.symm z)
      rw [A.apply_symm_apply] at hg
      constructor <;> linarith [hza.1,hza.2]
    · have he : segment ℝ p (A.symm z)=A.symm '' segment ℝ (A p) z := by
        simpa using (image_segment ℝ A.symm.toAffineEquiv.toAffineMap (A p) z).symm
      rw [he,←hfront]
      exact image_mono hseg
  obtain ⟨hfin,hcard⟩ := PlanarBoundaryStrip.closed_strip_extremes hC hcC hintC
    (a-k) (b-k) hrC
  have he : K.extremePoints ℝ∩{x | g x∈Icc a b}=
      A '' (C.extremePoints ℝ∩{x | x.1∈Icc (a-k) (b-k)}) := by
    ext x
    constructor
    · intro hx
      refine ⟨A.symm x,⟨?_,?_⟩,A.apply_symm_apply x⟩
      · rw [←image_extremePoints A.symm K]
        exact ⟨x,hx.1,rfl⟩
      · have hg := hA (A.symm x)
        rw [A.apply_symm_apply] at hg
        constructor <;> linarith [hx.2.1,hx.2.2]
    · rintro ⟨y,hy,rfl⟩
      refine ⟨?_,?_⟩
      · have hh : A y∈(A '' C).extremePoints ℝ := by
          rw [←image_extremePoints A C]
          exact ⟨y,hy.1,rfl⟩
        have hAC : A '' C=K := by
          ext z
          constructor
          · rintro ⟨w,hw,rfl⟩; exact (hmem w).mp hw
          · intro hz; exact ⟨A.symm z,⟨z,hz,rfl⟩,A.apply_symm_apply z⟩
        rwa [hAC] at hh
      · change a≤g (A y) ∧ g (A y)≤b
        rw [hA]
        constructor <;> linarith [hy.2.1,hy.2.2]
  rw [he,ncard_image_of_injective _ A.injective]
  exact ⟨hfin.image A,hcard⟩

variable [Fintype ι] [MeasurableSpace E] [BorelSpace E]

/-- A positive-gap negative global minimum in dimension two has at most
8m extreme points, before polygonality, normalization, or endpoint variations.
This coarse count is a route to polygonality, not a replacement for 4m. -/
theorem extremes_finite_ncard_le_eight_mul
    (hdim : Module.finrank ℝ E=2) (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (ho : ∀ i,lo i≤hi i)
    (hW : ∀ i,0<Body.width K (f i)) (d : ℕ) {B : ℝ} (hB : B≤1)
    (hbudget : budget K f lo hi≤B) (hneg : margin μ K f lo hi d B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi)) :
    (K.extremePoints ℝ).Finite ∧ (K.extremePoints ℝ).ncard≤8*Fintype.card ι := by
  have hint : (interior K).Nonempty := by
    by_contra hn
    have he : interior K=∅ := not_nonempty_iff_eq_empty.mp hn
    have hs : K⊆frontier K := by rw [frontier,he,sdiff_empty]; exact subset_closure
    have hz := measure_mono_null hs (hc.addHaar_frontier μ)
    simp [Measure.real,hz] at hV
  have hne : K.Nonempty := hint.mono interior_subset
  have hf (i : ι) : (f i).linear≠0 := by
    intro hz
    obtain ⟨P,hP,Q,hQ,hmax,hmin⟩ := Body.exists_realisers hK hne
      (f i).continuous_of_finiteDimensional
    have he := (f i).linearMap_vsub P Q
    rw [hz,LinearMap.zero_apply] at he
    have hw := hW i
    rw [Body.width_eq_of_realisers hP hQ hmax hmin] at hw
    change 0=f i P-f i Q at he
    linarith only [he,hw]
  let A (i) := K.extremePoints ℝ∩{x | f i x∈Icc (lo i) (hi i)}
  have hA (i) : (A i).Finite ∧ (A i).ncard≤6 := by
    obtain ⟨L,hL⟩ := exists_plank_chart hdim (f i) (hf i)
    apply closed_strip_extremes_of_chart L (f i) (f i 0) hL hK hc hint (lo i) (hi i)
    intro p hp hpi
    obtain ⟨z,hz,hzw,_,hseg⟩ := GlobalBodyBoundaryRuling.plank_boundary_segment
      μ hK hc hV f lo hi ho hW d hbudget hglobal hgap hp i hpi
    refine ⟨z,hz,?_,hseg⟩
    intro hzi
    rcases hzw with h | h
    · exact (ne_of_gt hzi.1) h
    · exact (ne_of_lt hzi.2) h
  have hcovered : (K.extremePoints ℝ∩covered f lo hi).Finite ∧
      (K.extremePoints ℝ∩covered f lo hi).ncard≤6*Fintype.card ι := by
    have he : K.extremePoints ℝ∩covered f lo hi=⋃ i,A i := inter_iUnion _ _
    rw [he]
    refine ⟨finite_iUnion fun i => (hA i).1,?_⟩
    calc
      (⋃ i,A i).ncard≤∑ i,(A i).ncard := ncard_iUnion_le_of_fintype A
      _ ≤∑ _i : ι,6 := Finset.sum_le_sum fun i _ => (hA i).2
      _ =6*Fintype.card ι := by simp [Nat.mul_comm]
  obtain ⟨hfin,hcount⟩ := uncovered_ncard_le_singletonFaces μ hK hc hne hV
    f lo hi ho hW d hB hbudget hneg hglobal
  have hsingle : (singletonFaces K f).ncard≤2*Fintype.card ι := by
    simpa [Nat.card_prod,Nat.card_eq_fintype_card,Nat.mul_comm]
      using (singletonFaces K f).ncard_le_card
  have he : (K.extremePoints ℝ\covered f lo hi)∪
      (K.extremePoints ℝ∩covered f lo hi)=K.extremePoints ℝ := sdiff_union_inter _ _
  refine ⟨he ▸ hfin.union hcovered.1,?_⟩
  calc
    (K.extremePoints ℝ).ncard=((K.extremePoints ℝ\covered f lo hi)∪
        (K.extremePoints ℝ∩covered f lo hi)).ncard := congrArg Set.ncard he.symm
    _ ≤(K.extremePoints ℝ\covered f lo hi).ncard+
        (K.extremePoints ℝ∩covered f lo hi).ncard := ncard_union_le _ _
    _ ≤8*Fintype.card ι := by have := hcovered.2; omega

/-- The original minimum itself is a finite convex hull. There is no
auxiliary polygonal enlargement and no finite-halfspace hypothesis. -/
theorem eq_convexHull_at_most_eight_mul
    (hdim : Module.finrank ℝ E=2) (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (ho : ∀ i,lo i≤hi i)
    (hW : ∀ i,0<Body.width K (f i)) (d : ℕ) {B : ℝ} (hB : B≤1)
    (hbudget : budget K f lo hi≤B) (hneg : margin μ K f lo hi d B<0)
    (hglobal : IsGlobalMinimum μ K f lo hi d B)
    (hgap : 0<μ.real (K\covered f lo hi)) :
    ∃ V : Finset E,V.card≤8*Fintype.card ι ∧ K=convexHull ℝ (V : Set E) := by
  classical
  obtain ⟨hfin,hcard⟩ := extremes_finite_ncard_le_eight_mul hdim μ hK hc hV
    f lo hi ho hW d hB hbudget hneg hglobal hgap
  have he := closure_convexHull_extremePoints hK hc
  rw [(hfin.isClosed_convexHull ℝ).closure_eq] at he
  refine ⟨hfin.toFinset,?_,?_⟩
  · rw [←ncard_eq_toFinset_card _ hfin]
    exact hcard
  · simpa using he.symm

end Plank.PlanarRuledMinimum
