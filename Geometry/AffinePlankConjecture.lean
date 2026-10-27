module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

open scoped RealInnerProductSpace Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Width of `K` along direction `u`: `sup_{y ∈ K} ⟪y, u⟫ − inf_{y ∈ K} ⟪y, u⟫`. -/
noncomputable def widthAlong (K : Set E) (u : E) : ℝ :=
  sSup ((fun x => ⟪x, u⟫) '' K) - sInf ((fun x => ⟪x, u⟫) '' K)

/-- Minimal width of `K`: `inf_{u ≠ 0} widthAlong K u / ‖u‖`. Scale-invariant in `u`. -/
noncomputable def minWidth (K : Set E) : ℝ :=
  sInf ((fun u => widthAlong K u / ‖u‖) '' {u : E | u ≠ 0})

/-! ### Properties of `widthAlong` -/

/-- Width is monotone: larger sets have larger width along any direction. -/
theorem widthAlong_mono {S K : Set E} (hSK : S ⊆ K) (hS : S.Nonempty)
    (hK : IsCompact K) (u : E) :
    widthAlong S u ≤ widthAlong K u := by
  unfold widthAlong
  have himg : (fun x => ⟪x, u⟫) '' S ⊆ (fun x => ⟪x, u⟫) '' K := Set.image_mono hSK
  have hSne : ((fun x => ⟪x, u⟫) '' S).Nonempty := hS.image _
  have hcont : ContinuousOn (fun x => ⟪x, u⟫) K :=
    ((innerSLFlip ℝ) u).continuous.continuousOn
  linarith [csSup_le_csSup (hK.bddAbove_image hcont) hSne himg,
            csInf_le_csInf (hK.bddBelow_image hcont) hSne himg]

/-- For a compact nonempty set, the width along `u` is attained by two points. -/
theorem widthAlong_attained (K : Set E) (hK : IsCompact K) (hne : K.Nonempty) (u : E) :
    ∃ x ∈ K, ∃ y ∈ K, widthAlong K u = ⟪x, u⟫ - ⟪y, u⟫ := by
  have hcont : ContinuousOn (fun x => ⟪x, u⟫) K :=
    ((innerSLFlip ℝ) u).continuous.continuousOn
  obtain ⟨x, hx, hxeq⟩ := hK.exists_sSup_image_eq hne hcont
  obtain ⟨y, hy, hyeq⟩ := hK.exists_sInf_image_eq hne hcont
  exact ⟨x, hx, y, hy, by unfold widthAlong; rw [hxeq, hyeq]⟩

/-- The image of a bounded set under `⟪·, u⟫` is bounded above. -/
private theorem bddAbove_inner_image {K : Set E} (hbdd : Bornology.IsBounded K) (u : E) :
    BddAbove ((fun x => ⟪x, u⟫) '' K) := by
  obtain ⟨R, hR⟩ := hbdd.subset_ball 0
  exact ⟨R * ‖u‖, fun y ⟨x, hx, hxy⟩ => by
    subst hxy; have := hR hx; rw [Metric.mem_ball, dist_zero_right] at this
    exact (le_abs_self _).trans ((abs_real_inner_le_norm x u).trans
      (mul_le_mul_of_nonneg_right this.le (norm_nonneg u)))⟩

/-- The image of a bounded set under `⟪·, u⟫` is bounded below. -/
private theorem bddBelow_inner_image {K : Set E} (hbdd : Bornology.IsBounded K) (u : E) :
    BddBelow ((fun x => ⟪x, u⟫) '' K) := by
  obtain ⟨R, hR⟩ := hbdd.subset_ball 0
  exact ⟨-(R * ‖u‖), fun y ⟨x, hx, hxy⟩ => by
    subst hxy; have hx' := hR hx; rw [Metric.mem_ball, dist_zero_right] at hx'
    nlinarith [abs_real_inner_le_norm x u, neg_abs_le ⟪x, u⟫, norm_nonneg u]⟩

/-- If `K` has nonempty interior and is bounded, then `widthAlong K u > 0` for `u ≠ 0`. -/
private theorem widthAlong_pos_of_interior [FiniteDimensional ℝ E]
    {K : Set E} (hne_int : (interior K).Nonempty) (hbdd : Bornology.IsBounded K)
    {u : E} (hu : u ≠ 0) :
    0 < widthAlong K u := by
  unfold widthAlong
  obtain ⟨z, hz⟩ := hne_int
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have h_in_ball : z + (ε / (2 * ‖u‖)) • u ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖z + (ε / (2 * ‖u‖)) • u - z‖ = ε / (2 * ‖u‖) * ‖u‖ := by
      rw [show z + (ε / (2 * ‖u‖)) • u - z = (ε / (2 * ‖u‖)) • u from by abel]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hε (mul_pos two_pos hu_pos))]
    rw [h1]; have : ε / (2 * ‖u‖) * ‖u‖ = ε / 2 := by field_simp
    linarith
  have hz1 : z + (ε / (2 * ‖u‖)) • u ∈ K := interior_subset (hball h_in_ball)
  have h_val : ⟪z + (ε / (2 * ‖u‖)) • u, u⟫ =
      ⟪z, u⟫ + (ε / (2 * ‖u‖)) * ‖u‖ ^ 2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith [csInf_le (bddBelow_inner_image hbdd u)
      (Set.mem_image_of_mem _ (interior_subset hz)),
    le_csSup (bddAbove_inner_image hbdd u) (Set.mem_image_of_mem _ hz1),
    mul_pos (div_pos hε (mul_pos two_pos hu_pos)) (sq_pos_of_pos hu_pos)]

/-- `sSup (convexHull ℝ S) = sSup S` for bounded nonempty sets in `ℝ`. -/
private theorem csSup_convexHull_eq {S : Set ℝ} (hne : S.Nonempty) (hbddA : BddAbove S)
    (hbddB : BddBelow S) :
    sSup (convexHull ℝ S) = sSup S := by
  have hIcc : convexHull ℝ S ⊆ Set.Icc (sInf S) (sSup S) :=
    convexHull_min (fun y hy => ⟨csInf_le hbddB hy, le_csSup hbddA hy⟩) (convex_Icc _ _)
  apply le_antisymm
  · exact csSup_le (convexHull_nonempty_iff.mpr hne) (fun x hx => (hIcc hx).2)
  · exact csSup_le_csSup ⟨sSup S, fun x hx => (hIcc hx).2⟩ hne (subset_convexHull ℝ S)

/-- `sInf (convexHull ℝ S) = sInf S` for bounded nonempty sets in `ℝ`. -/
private theorem csInf_convexHull_eq {S : Set ℝ} (hne : S.Nonempty) (hbddA : BddAbove S)
    (hbddB : BddBelow S) :
    sInf (convexHull ℝ S) = sInf S := by
  have hIcc : convexHull ℝ S ⊆ Set.Icc (sInf S) (sSup S) :=
    convexHull_min (fun y hy => ⟨csInf_le hbddB hy, le_csSup hbddA hy⟩) (convex_Icc _ _)
  apply le_antisymm
  · exact csInf_le_csInf ⟨sInf S, fun x hx => (hIcc hx).1⟩ hne (subset_convexHull ℝ S)
  · exact le_csInf (convexHull_nonempty_iff.mpr hne) (fun x hx => (hIcc hx).1)

/-- `widthAlong (convexHull ℝ K) u = widthAlong K u` for bounded nonempty `K`. -/
private theorem widthAlong_convexHull {K : Set E} (hne : K.Nonempty)
    (hbdd : Bornology.IsBounded K) (u : E) :
    widthAlong (convexHull ℝ K) u = widthAlong K u := by
  unfold widthAlong
  set f : E → ℝ := fun x => ⟪x, u⟫
  have hlin : IsLinearMap ℝ f :=
    ⟨fun _ _ => inner_add_left _ _ _, fun _ _ => real_inner_smul_left _ _ _⟩
  rw [hlin.image_convexHull,
    csSup_convexHull_eq (hne.image f) (bddAbove_inner_image hbdd u)
      (bddBelow_inner_image hbdd u),
    csInf_convexHull_eq (hne.image f) (bddAbove_inner_image hbdd u)
      (bddBelow_inner_image hbdd u)]

/-! ## Bang's Affine Plank Conjecture (1951)

If a convex body is covered by planks, the sum of relative widths is ≥ 1.
Open in full generality; see specializations below. -/

/-- Bang's affine plank conjecture for a specific inner product space `E`.
If a convex body `K ⊆ E` with nonempty interior is covered by `n` planks, then
the sum of their relative widths is at least 1. -/
def AffinePlankConjecture (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (K : ConvexBody E), (interior (K : Set E)).Nonempty →
    ∀ (n : ℕ) (u : Fin n → E) (lo hi : Fin n → ℝ),
      (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
      ↑K ⊆ ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
      1 ≤ ∑ i : Fin n, (hi i - lo i) / widthAlong (↑K) (u i)

/-! ## Specialization 1: The Planar Case (d = 2)

Open in full generality. Bang (1953) proved the conjecture for n = 2 planks
(in any dimension, not specific to the plane). Best known lower bound for d = 2:
2/(1 + √2) ≈ 0.83 (Bakaev–Yehudayoff 2025). -/

/-- Bang's conjecture restricted to the plane (`dim E = 2`). -/
def AffinePlankConjecturePlane (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  Module.finrank ℝ E = 2 → AffinePlankConjecture E

/-! ## Specialization 2: The Simplex Case

Equivalent to the full conjecture: Ambrus (2010) showed proving Bang's conjecture
for simplices implies it in general. -/

/-- Bang's conjecture restricted to simplices (convex hull of affinely independent points). -/
def AffinePlankConjectureSimplex (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (d : ℕ) (s : Affine.Simplex ℝ E d),
    (interior (convexHull ℝ (Set.range s.points))).Nonempty →
    ∀ (n : ℕ) (u : Fin n → E) (lo hi : Fin n → ℝ),
      (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
      convexHull ℝ (Set.range s.points) ⊆
        ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
      1 ≤ ∑ i : Fin n, (hi i - lo i) /
        widthAlong (convexHull ℝ (Set.range s.points)) (u i)

/-- The general conjecture trivially implies the simplex case: the convex hull of a
simplex in a finite-dimensional inner product space is a `ConvexBody` (compact, convex,
nonempty), so the general statement applies directly. -/
theorem AffinePlankConjecture.simplex [FiniteDimensional ℝ E]
    (h : AffinePlankConjecture E) : AffinePlankConjectureSimplex E :=
  fun _d s hs _n u lo hi hu hle hcover =>
    h ⟨_, convex_convexHull ℝ _,
      (Set.finite_range s.points).isCompact_convexHull (𝕜 := ℝ),
      (Set.range_nonempty s.points).convexHull (𝕜 := ℝ)⟩ hs _ u lo hi hu hle hcover

/-! ### Helper lemmas for the Ambrus lifting argument -/

/-- The family `{0, e₀, e₁, …, e_{d-1}}` in `EuclideanSpace ℝ (Fin d)` is affinely
independent. Follows from orthonormality of the standard basis. -/
private lemma affineIndependent_origin_stdBasis (d : ℕ) :
    AffineIndependent ℝ (Fin.cons (0 : EuclideanSpace ℝ (Fin d))
      (fun j => EuclideanSpace.single j (1 : ℝ))) := by
  set p : Fin (d + 1) → EuclideanSpace ℝ (Fin d) :=
    Fin.cons 0 (fun j => EuclideanSpace.single j (1 : ℝ)) with hp
  show AffineIndependent ℝ p
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin (d + 1))]
  have hp0 : p 0 = 0 := Fin.cons_zero _ _
  simp only [hp0, vsub_eq_sub, sub_zero]
  have hps : ∀ k : Fin d, p (Fin.succ k) = EuclideanSpace.single k (1 : ℝ) :=
    fun k => Fin.cons_succ _ _ k
  have hpeq : ∀ (i : { x : Fin (d + 1) // x ≠ 0 }),
      p i.1 = EuclideanSpace.single (Fin.pred i.1 i.2) (1 : ℝ) := by
    intro ⟨i, hi⟩
    rw [show p i = p (Fin.succ (Fin.pred i hi)) from by rw [Fin.succ_pred]]
    exact hps _
  simp_rw [hpeq]
  exact (EuclideanSpace.orthonormal_single (𝕜 := ℝ)).linearIndependent.comp _
    (fun a b h => Subtype.ext (by
      have := congr_arg Fin.succ h
      rwa [Fin.succ_pred, Fin.succ_pred] at this))

/-- The convex hull of `{0, e₀, …, e_{d-1}}` has nonempty interior in
`EuclideanSpace ℝ (Fin d)`, because the affine span is the full space. -/
private lemma interior_convexHull_origin_stdBasis (d : ℕ) :
    (interior (convexHull ℝ (Set.range (Fin.cons (0 : EuclideanSpace ℝ (Fin d))
      (fun j => EuclideanSpace.single j (1 : ℝ)))))).Nonempty := by
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
  set p : Fin (d + 1) → EuclideanSpace ℝ (Fin d) :=
    Fin.cons 0 (fun j => EuclideanSpace.single j (1 : ℝ)) with hp
  change affineSpan ℝ (Set.range p) = ⊤
  have hindep : AffineIndependent ℝ p := affineIndependent_origin_stdBasis d
  rw [hindep.affineSpan_eq_top_iff_card_eq_finrank_add_one]
  simp [EuclideanSpace, PiLp]

/-! ## Bezdek's Annulus Conjecture (2003)

Removing a sufficiently small homothetic copy of a convex body from its interior
does not reduce the total plank width needed to cover it. Unlike Bang's conjecture,
this uses absolute widths and concerns a non-convex region. The absolute width of
plank `{x | lo ≤ ⟪x, u⟫ ≤ hi}` is `(hi − lo) / ‖u‖`. -/

/-- Bezdek's annulus conjecture for a specific inner product space `E`.
For a convex body `K` containing the origin in its interior, there exists `ε₀ > 0`
such that for all `0 < ε < ε₀`, covering `K \ εK` by planks requires total
absolute width at least `minWidth K`. -/
def BezdekAnnulusConjecture (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (K : ConvexBody E), (0 : E) ∈ interior (K : Set E) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (n : ℕ) (u : Fin n → E) (lo hi : Fin n → ℝ),
        (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
        ((↑K : Set E) \ (ε • (↑K : Set E))) ⊆
          ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
        minWidth (K : Set E) ≤ ∑ i : Fin n, (hi i - lo i) / ‖u i‖

/-- Bezdek's annulus conjecture (translated version, standard formulation).
The inner copy `εK` may be translated by any `y` such that `εK + {y} ⊆ interior K`.
**False** for spiky bodies: Ambrus–Huddell–Lai–Quirk–Williams (2025) showed that
for the equilateral triangle, the annulus can always be covered with strictly less
total width (arXiv:2504.02656). -/
def BezdekAnnulusConjectureTranslated (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : Prop :=
  ∀ (K : ConvexBody E), (0 : E) ∈ interior (K : Set E) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ (y : E), (ε • (↑K : Set E) + ({y} : Set E)) ⊆ interior (↑K : Set E) →
        ∀ (n : ℕ) (u : Fin n → E) (lo hi : Fin n → ℝ),
          (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
          ((↑K : Set E) \ (ε • (↑K : Set E) + ({y} : Set E))) ⊆
            ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
          minWidth (K : Set E) ≤ ∑ i : Fin n, (hi i - lo i) / ‖u i‖

/-! ## Sharp Ambrus reduction: dimension-specific simplex hypothesis

The original `AffinePlankConjectureSimplex.general` has a hypothesis that quantifies over
**all** finite-dimensional inner product spaces and **all** simplex dimensions. This is much
stronger than what the Ambrus lifting argument actually uses.

The proof constructs, for `n` planks on a convex body `K ⊆ E`, a `(2n−1)`-simplex in
`ℝ^{2n−1}` (specifically `EuclideanSpace ℝ (Fin (2n−1))`). The simplex hypothesis is
applied exactly once, in that specific space, for that specific simplex dimension, with
exactly `n` planks. Therefore, the weakest sufficient hypothesis is:

  "The plank conjecture holds for `n` planks on any `(2n−1)`-simplex in `ℝ^{2n−1}`."

The definitions below make this precise and the theorem
`AffinePlankConjectureSimplex.general_sharp` formalizes the sharp reduction. -/

/-- Bang's affine plank conjecture for a **fixed number** of planks `n` in space `E`.
This is the conjecture restricted to coverings by exactly `n` planks. -/
def AffinePlankConjectureFor (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) : Prop :=
  ∀ (K : ConvexBody E), (interior (K : Set E)).Nonempty →
    ∀ (u : Fin n → E) (lo hi : Fin n → ℝ),
      (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
      ↑K ⊆ ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
      1 ≤ ∑ i : Fin n, (hi i - lo i) / widthAlong (↑K) (u i)

/-- Bang's conjecture restricted to simplices of a **fixed dimension** `d` with a **fixed
number** of planks `n`. This is the simplex conjecture with both parameters specialized. -/
def AffinePlankConjectureSimplexFor (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (d n : ℕ) : Prop :=
  ∀ (s : Affine.Simplex ℝ E d),
    (interior (convexHull ℝ (Set.range s.points))).Nonempty →
    ∀ (u : Fin n → E) (lo hi : Fin n → ℝ),
      (∀ i, u i ≠ 0) → (∀ i, lo i ≤ hi i) →
      convexHull ℝ (Set.range s.points) ⊆
        ⋃ i, {x | lo i ≤ ⟪x, u i⟫ ∧ ⟪x, u i⟫ ≤ hi i} →
      1 ≤ ∑ i : Fin n, (hi i - lo i) /
        widthAlong (convexHull ℝ (Set.range s.points)) (u i)

/-- The full conjecture is equivalent to covering with any fixed number of planks.
(Forward: specialize. Backward: combine all fixed-n instances.) -/
theorem affinePlankConjecture_iff_for [FiniteDimensional ℝ E] :
    AffinePlankConjecture E ↔ ∀ n, AffinePlankConjectureFor E n := by
  simp only [AffinePlankConjecture, AffinePlankConjectureFor]
  constructor
  · intro h n K hK u lo hi hu hle hcover
    exact h K hK n u lo hi hu hle hcover
  · intro h K hK n u lo hi hu hle hcover
    exact h n K hK u lo hi hu hle hcover

/-- The full simplex conjecture is equivalent to fixing both dimension and plank count. -/
theorem affinePlankConjectureSimplex_iff_for [FiniteDimensional ℝ E] :
    AffinePlankConjectureSimplex E ↔ ∀ d n, AffinePlankConjectureSimplexFor E d n := by
  simp only [AffinePlankConjectureSimplex, AffinePlankConjectureSimplexFor]
  constructor
  · intro h d n s hs u lo hi hu hle hcover
    exact h d s hs n u lo hi hu hle hcover
  · intro h d s hs n u lo hi hu hle hcover
    exact h d n s hs u lo hi hu hle hcover

/-- **Sharp Ambrus reduction** (parameterized by `n' : ℕ`, for `n' + 1` planks).

For a fixed number of planks `n = n' + 1`, if the plank conjecture holds for `n` planks
on every `(2n−1)`-simplex in `EuclideanSpace ℝ (Fin (2n−1))`, then the plank conjecture
holds for `n` planks on **any** convex body in **any** finite-dimensional inner product
space.

This is strictly weaker than the hypothesis in `AffinePlankConjectureSimplex.general`,
which quantifies over all spaces and all simplex dimensions.

**Dimension arithmetic.** For `n' + 1` planks the Ambrus lifting produces `2(n'+1)` points,
forming a `(2n'+1)`-simplex in `ℝ^{2n'+1}`. We parameterize by `n'` to avoid natural
number subtraction: `2n−1 = 2(n'+1)−1 = 2n'+1`. -/
theorem AffinePlankConjectureSimplex.general_sharp (n' : ℕ)
    (hsimplex : AffinePlankConjectureSimplexFor
      (EuclideanSpace ℝ (Fin (2 * n' + 1))) (2 * n' + 1) (n' + 1))
    [FiniteDimensional ℝ E] :
    AffinePlankConjectureFor E (n' + 1) := by
  intro K hK u lo hi hu hle hcover
  -- Step 1: For each plank direction, obtain width-realizing points in K
  choose xp hxp xm hxm hwidth using
    fun i => widthAlong_attained (↑K) K.isCompact' K.nonempty' (u i)
  -- Step 2: Arrange 2(n'+1) points from K
  set m := 2 * (n' + 1) with hm_def
  let pts : Fin m → E := fun j =>
    if h : j.val < n' + 1 then xp ⟨j.val, h⟩
    else xm ⟨j.val - (n' + 1), by omega⟩
  have hpts_mem : ∀ j, pts j ∈ (↑K : Set E) := by
    intro j; simp only [pts]; split_ifs <;> [exact hxp _; exact hxm _]
  have hpts_xp : ∀ i : Fin (n' + 1), pts ⟨i.val, by omega⟩ = xp i := by
    intro i; simp only [pts, show i.val < n' + 1 from i.isLt, dite_true]
  have hpts_xm : ∀ i : Fin (n' + 1), pts ⟨i.val + (n' + 1), by omega⟩ = xm i := by
    intro i; simp only [pts, show ¬(i.val + (n' + 1) < n' + 1) from by omega, dite_false]
    congr 1; exact Fin.ext (by simp)
  -- Step 3: Build the simplex in EuclideanSpace ℝ (Fin (2*n'+1))
  set d := 2 * n' + 1 with hd_def
  set F := EuclideanSpace ℝ (Fin d) with hF_def
  let verts : Fin (d + 1) → F :=
    Fin.cons (0 : F) (fun j : Fin d => EuclideanSpace.single j (1 : ℝ))
  let s : Affine.Simplex ℝ F d := ⟨verts, affineIndependent_origin_stdBasis d⟩
  have hs_int : (interior (convexHull ℝ (Set.range s.points))).Nonempty :=
    interior_convexHull_origin_stdBasis d
  -- Step 4: Define lifted plank directions and shifted boundaries
  let base_ip : Fin (n' + 1) → ℝ := fun i => ⟪pts ⟨0, by omega⟩, u i⟫
  let ũ : Fin (n' + 1) → F := fun i =>
    (EuclideanSpace.equiv (Fin d) ℝ).symm
      (fun j : Fin d => ⟪pts ⟨j.val + 1, by omega⟩, u i⟫ - base_ip i)
  let lo' : Fin (n' + 1) → ℝ := fun i => lo i - base_ip i
  let hi' : Fin (n' + 1) → ℝ := fun i => hi i - base_ip i
  -- Step 5: Verify hypotheses
  have hũ_ne : ∀ i, ũ i ≠ 0 := by
    intro i habs
    have hcoord : ∀ j : Fin d, ⟪pts ⟨j.val + 1, by omega⟩, u i⟫ = base_ip i := by
      intro j
      have : (EuclideanSpace.equiv (Fin d) ℝ) (ũ i) = 0 := by simp [habs]
      have hj := congr_fun this j
      simp [ũ, EuclideanSpace.equiv] at hj
      linarith
    have hall : ∀ k : Fin m, ⟪pts k, u i⟫ = base_ip i := by
      intro ⟨k, hk⟩
      by_cases hk0 : k = 0
      · subst hk0; rfl
      · have hk' : 0 < k := Nat.pos_of_ne_zero hk0
        specialize hcoord ⟨k - 1, by omega⟩
        simp only [show k - 1 + 1 = k from Nat.succ_pred_eq_of_pos hk'] at hcoord
        exact hcoord
    have h1 : ⟪xp i, u i⟫ = base_ip i := hpts_xp i ▸ hall ⟨i.val, by omega⟩
    have h2 : ⟪xm i, u i⟫ = base_ip i := hpts_xm i ▸ hall ⟨i.val + (n' + 1), by omega⟩
    have hpos : 0 < widthAlong (↑K) (u i) :=
      widthAlong_pos_of_interior hK K.isBounded (hu i)
    linarith [hwidth i]
  have hle' : ∀ i, lo' i ≤ hi' i := fun i => by
    show lo i - base_ip i ≤ hi i - base_ip i; linarith [hle i]
  have hcover' : convexHull ℝ (Set.range s.points) ⊆
      ⋃ i, {x : F | lo' i ≤ ⟪x, ũ i⟫ ∧ ⟪x, ũ i⟫ ≤ hi' i} := by
    let p0 : E := pts ⟨0, by omega⟩
    let φ : F → E := fun c =>
      p0 + ∑ j : Fin d, (c j) • (pts ⟨j.val + 1, by omega⟩ - p0)
    have hφ_inner : ∀ (c : F) (i : Fin (n' + 1)),
        ⟪c, ũ i⟫ = ⟪φ c, u i⟫ - base_ip i := by
      intro c i
      have lhs : ⟪c, ũ i⟫ =
          ∑ j : Fin d, c j * (⟪pts ⟨j.val + 1, by omega⟩, u i⟫ - base_ip i) := by
        erw [PiLp.inner_apply]; congr 1; ext j
        erw [RCLike.inner_apply, starRingEnd_self_apply, mul_comm]
        simp [ũ, EuclideanSpace.equiv]
      have rhs : ⟪φ c, u i⟫ - base_ip i =
          ∑ j : Fin d, c j * (⟪pts ⟨j.val + 1, by omega⟩, u i⟫ - base_ip i) := by
        simp only [φ, inner_add_left, sum_inner, real_inner_smul_left,
          inner_sub_left, p0, base_ip]
        ring
      linarith [lhs, rhs]
    have hφ_mem : ∀ c ∈ convexHull ℝ (Set.range (show Fin (d + 1) → F from verts)),
        φ c ∈ (↑K : Set E) := by
      apply convexHull_min (t := φ ⁻¹' (↑K : Set E))
      · rintro _ ⟨k, rfl⟩
        show φ (verts k) ∈ (↑K : Set E)
        induction k using Fin.cases with
        | zero =>
          simp [φ, verts, Fin.cons_zero]
          exact hpts_mem ⟨0, by omega⟩
        | succ j =>
          have hφ_ej : φ (verts (Fin.succ j)) = pts ⟨j.val + 1, by omega⟩ := by
            simp only [φ, verts, Fin.cons_succ]
            have h_single : ∀ k : Fin d, (EuclideanSpace.single j (1 : ℝ)) k =
                if k = j then 1 else 0 := by
              intro k; simp [EuclideanSpace.single]
            simp_rw [h_single, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq']
            simp
          rw [hφ_ej]; exact hpts_mem ⟨j.val + 1, by omega⟩
      · intro x hx y hy a b ha hb hab
        show φ (a • x + b • y) ∈ ↑K
        have hφ_affine : φ (a • x + b • y) = a • φ x + b • φ y := by
          simp only [φ]
          simp_rw [show ∀ j : Fin d, (a • x + b • y) j =
              a * x j + b * y j from fun _ => rfl,
            add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum]
          have hp0 : p0 = a • p0 + b • p0 := by rw [← add_smul, hab, one_smul]
          conv_lhs => arg 1; rw [hp0]
          rw [smul_add, smul_add]
          abel
        rw [hφ_affine]
        exact K.convex hx hy ha hb hab
    intro c hc
    rw [show s.points = verts from rfl] at hc
    have hφc_mem : φ c ∈ (↑K : Set E) := hφ_mem c hc
    obtain ⟨i, hi_mem⟩ := Set.mem_iUnion.mp (hcover hφc_mem)
    exact Set.mem_iUnion.mpr ⟨i, by
      constructor <;> [linarith [(hφ_inner c i).symm, hi_mem.1];
                        linarith [(hφ_inner c i).symm, hi_mem.2]]⟩
  -- Step 6: Apply the simplex hypothesis — only needs (2n'+1)-simplex with n'+1 planks
  have h_result := hsimplex s hs_int ũ lo' hi' hũ_ne hle' hcover'
  -- Step 7: Width equality
  have hwidth_eq : ∀ i, widthAlong (convexHull ℝ (Set.range s.points)) (ũ i) =
      widthAlong (↑K) (u i) := by
    intro i
    rw [show s.points = verts from rfl,
        widthAlong_convexHull (Set.range_nonempty _) ((Set.finite_range _).isBounded)]
    have hxp_sup : ⟪xp i, u i⟫ = sSup ((fun x => ⟪x, u i⟫) '' ↑K) := by
      have h1 := le_csSup (bddAbove_inner_image K.isBounded (u i))
        (Set.mem_image_of_mem _ (hxp i))
      have h2 := csInf_le (bddBelow_inner_image K.isBounded (u i))
        (Set.mem_image_of_mem _ (hxm i))
      have : widthAlong (↑K) (u i) =
          sSup ((fun x => ⟪x, u i⟫) '' ↑K) - sInf ((fun x => ⟪x, u i⟫) '' ↑K) := rfl
      linarith [hwidth i]
    have hxm_inf : ⟪xm i, u i⟫ = sInf ((fun x => ⟪x, u i⟫) '' ↑K) := by
      have h1 := le_csSup (bddAbove_inner_image K.isBounded (u i))
        (Set.mem_image_of_mem _ (hxp i))
      have h2 := csInf_le (bddBelow_inner_image K.isBounded (u i))
        (Set.mem_image_of_mem _ (hxm i))
      have : widthAlong (↑K) (u i) =
          sSup ((fun x => ⟪x, u i⟫) '' ↑K) - sInf ((fun x => ⟪x, u i⟫) '' ↑K) := rfl
      linarith [hwidth i]
    have hm_eq : d + 1 = m := by omega
    have hvert_ip : ∀ k : Fin (d + 1),
        ⟪verts k, ũ i⟫ = ⟪pts (k.cast hm_eq), u i⟫ - base_ip i := by
      intro k
      induction k using Fin.cases with
      | zero =>
        simp only [verts, Fin.cons_zero, inner_zero_left]
        simp [base_ip, Fin.cast]
      | succ j =>
        simp only [verts, Fin.cons_succ]
        erw [EuclideanSpace.inner_single_left]; simp [EuclideanSpace.equiv, ũ]
        exact congr_arg (fun x => ⟪pts x, u i⟫) (Fin.ext rfl)
    have hvert_le : ∀ k, ⟪verts k, ũ i⟫ ≤ ⟪xp i, u i⟫ - base_ip i := by
      intro k; rw [hvert_ip, hxp_sup]
      linarith [le_csSup (bddAbove_inner_image K.isBounded (u i))
        (Set.mem_image_of_mem _ (hpts_mem (k.cast hm_eq)))]
    have hvert_ge : ∀ k, ⟪xm i, u i⟫ - base_ip i ≤ ⟪verts k, ũ i⟫ := by
      intro k; rw [hvert_ip, hxm_inf]
      linarith [csInf_le (bddBelow_inner_image K.isBounded (u i))
        (Set.mem_image_of_mem _ (hpts_mem (k.cast hm_eq)))]
    have hxp_at : ⟪verts ⟨i.val, by omega⟩, ũ i⟫ = ⟪xp i, u i⟫ - base_ip i := by
      rw [hvert_ip]; congr 1
      rw [show (Fin.cast hm_eq ⟨i.val, _⟩ : Fin m) = ⟨i.val, by omega⟩ from
        Fin.ext (by simp [Fin.cast])]
      exact congr_arg (fun x => ⟪x, u i⟫) (hpts_xp i)
    have hxm_at : ⟪verts ⟨i.val + (n' + 1), by omega⟩, ũ i⟫ =
        ⟪xm i, u i⟫ - base_ip i := by
      rw [hvert_ip]; congr 1
      rw [show (Fin.cast hm_eq ⟨i.val + (n' + 1), _⟩ : Fin m) =
          ⟨i.val + (n' + 1), by omega⟩ from Fin.ext (by simp [Fin.cast])]
      exact congr_arg (fun x => ⟪x, u i⟫) (hpts_xm i)
    unfold widthAlong
    have hbdd_v := (Set.finite_range verts).isBounded
    have hsSup : sSup ((fun x => ⟪x, ũ i⟫) '' Set.range verts) =
        ⟪xp i, u i⟫ - base_ip i := le_antisymm
      (csSup_le ((Set.range_nonempty _).image _)
        (by rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩; exact hvert_le k))
      (hxp_at ▸ le_csSup (bddAbove_inner_image hbdd_v (ũ i))
        (Set.mem_image_of_mem _ (Set.mem_range_self _)))
    have hsInf : sInf ((fun x => ⟪x, ũ i⟫) '' Set.range verts) =
        ⟪xm i, u i⟫ - base_ip i := le_antisymm
      (hxm_at ▸ csInf_le (bddBelow_inner_image hbdd_v (ũ i))
        (Set.mem_image_of_mem _ (Set.mem_range_self _)))
      (le_csInf ((Set.range_nonempty _).image _)
        (by rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩; exact hvert_ge k))
    rw [hsSup, hsInf]; linarith [hwidth i]
  -- Conclude
  have hwidth_shift : ∀ i, hi' i - lo' i = hi i - lo i := fun i => by
    show (hi i - base_ip i) - (lo i - base_ip i) = hi i - lo i; ring
  calc 1 ≤ ∑ i, (hi' i - lo' i) /
        widthAlong (convexHull ℝ (Set.range s.points)) (ũ i) := h_result
    _ = ∑ i, (hi i - lo i) / widthAlong (↑K) (u i) := by
        congr 1; ext i; rw [hwidth_shift i, hwidth_eq i]

/-- The original `AffinePlankConjectureSimplex.general` follows from the sharp version:
if the simplex conjecture holds for all dimensions and plank counts, then in particular
it holds for the `(2n'+1)`-simplex with `n'+1` planks, so the sharp reduction applies. -/
theorem AffinePlankConjectureSimplex.general_of_sharp
    (hsimplex : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F], AffinePlankConjectureSimplex F)
    [FiniteDimensional ℝ E] :
    AffinePlankConjecture E := by
  rw [affinePlankConjecture_iff_for]
  intro n
  match n with
  | 0 =>
    intro K _ _ _ _ _ _ hcover
    exfalso
    obtain ⟨x, hx⟩ := K.nonempty'
    have := hcover hx
    simp at this
  | n' + 1 =>
    exact general_sharp n'
      ((affinePlankConjectureSimplex_iff_for.mp (hsimplex _)) _ _)

/-- The general simplex hypothesis specializes to the fixed-dimension
reduction, so the full conjecture needs only that one lifting proof. -/
theorem AffinePlankConjectureSimplex.general
    (hsimplex : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F], AffinePlankConjectureSimplex F)
    [FiniteDimensional ℝ E] :
    AffinePlankConjecture E := by
  exact AffinePlankConjectureSimplex.general_of_sharp hsimplex

/-! ## Equivalence of simplex and general cases -/

/-- The simplex case of Bang's conjecture (across all finite-dimensional inner product
spaces) is equivalent to the full conjecture: the simplex case trivially follows from the
general case, and Ambrus (2010) proved the converse via a lifting argument. -/
theorem affinePlankConjecture_iff_simplex :
    (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
      AffinePlankConjectureSimplex E) ↔
    (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
      AffinePlankConjecture E) := by
  constructor
  · intro h E _ _ _
    exact AffinePlankConjectureSimplex.general (fun F => h F)
  · intro h E _ _ _
    exact (h E).simplex
