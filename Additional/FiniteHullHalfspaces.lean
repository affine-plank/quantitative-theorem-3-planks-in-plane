/-
# Finite affine halfspace descriptions of finite convex hulls

The proof uses scalar elimination of finite systems of non-strict linear
inequalities. No full-dimensionality assumption is used.
-/
module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteHullHalfspaces

open Set

theorem exists_between_finite_sets {L U : Set ℝ} (hL : L.Finite) (hU : U.Finite)
    (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    ∃ t : ℝ, (∀ l ∈ L, l ≤ t) ∧ (∀ u ∈ U, t ≤ u) := by
  by_cases hne : L.Nonempty
  · exact ⟨sSup L, fun l hl => le_csSup hL.bddAbove hl,
      fun u hu => csSup_le hne (fun l hl => h l hl u hu)⟩
  · obtain ⟨t, ht⟩ := hU.bddBelow
    exact ⟨t, fun l hl => (hne ⟨l, hl⟩).elim, ht⟩

/-- One-variable elimination: zero coefficients and every lower/upper pair are
the complete conditions for feasibility. -/
theorem exists_scalar_iff {ι : Type*} [Finite ι] (a c : ι → ℝ) :
    (∃ t : ℝ, ∀ i, a i * t ≤ c i) ↔
      (∀ i, a i = 0 → 0 ≤ c i) ∧
      (∀ i j, a i < 0 → 0 < a j → c i / a i ≤ c j / a j) := by
  constructor
  · rintro ⟨t, ht⟩
    constructor
    · intro i hi
      simpa [hi] using ht i
    · intro i j hi hj
      exact ((div_le_iff_of_neg hi).2 (by simpa [mul_comm] using ht i)).trans
        ((le_div_iff₀ hj).2 (by simpa [mul_comm] using ht j))
  · rintro ⟨hzero, hpairs⟩
    let L : Set ℝ := (fun i => c i / a i) '' {i | a i < 0}
    let U : Set ℝ := (fun i => c i / a i) '' {i | 0 < a i}
    have hL : L.Finite := (Set.toFinite _).image _
    have hU : U.Finite := (Set.toFinite _).image _
    obtain ⟨t, hlow, hupp⟩ := exists_between_finite_sets hL hU (by
      rintro l ⟨i, hi, rfl⟩ u ⟨j, hj, rfl⟩
      exact hpairs i j hi hj)
    refine ⟨t, fun i => ?_⟩
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · have h := (div_le_iff_of_neg hi).1 (hlow _ ⟨i, hi, rfl⟩)
      simpa [mul_comm] using h
    · simpa [hi] using hzero i hi
    · have h := (le_div_iff₀ hi).1 (hupp _ ⟨i, hi, rfl⟩)
      simpa [mul_comm] using h

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- A set has a description by finitely many closed affine halfspaces. -/
def HasFiniteHalfspaces (S : Set E) : Prop :=
  ∃ s : Finset (E →ᵃ[ℝ] ℝ), ∀ x, x ∈ S ↔ ∀ f ∈ s, f x ≤ 0

theorem hasFiniteHalfspaces_family {ι : Type*} [Fintype ι] (f : ι → E →ᵃ[ℝ] ℝ) :
    HasFiniteHalfspaces {x | ∀ i, f i x ≤ 0} := by
  classical
  exact ⟨Finset.univ.image f, fun x => by simp⟩

theorem HasFiniteHalfspaces.inter {S T : Set E}
    (hS : HasFiniteHalfspaces S) (hT : HasFiniteHalfspaces T) :
    HasFiniteHalfspaces (S ∩ T) := by
  classical
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  exact ⟨s ∪ t, fun x => by simp [hs x, ht x, or_imp, forall_and]⟩

theorem HasFiniteHalfspaces.preimage {S : Set F}
    (hS : HasFiniteHalfspaces S) (g : E →ᵃ[ℝ] F) :
    HasFiniteHalfspaces (g ⁻¹' S) := by
  classical
  obtain ⟨s, hs⟩ := hS
  exact ⟨s.image (fun f => f.comp g), fun x => by simp [hs (g x)]⟩

/-- Eliminate one scalar variable in an affine family with known scalar
coefficients. The remaining inequalities are affine in the retained variables. -/
theorem hasFiniteHalfspaces_exists_scalar {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (c : ι → E →ᵃ[ℝ] ℝ) :
    HasFiniteHalfspaces {x | ∃ t : ℝ, ∀ i, a i * t ≤ c i x} := by
  classical
  let Z := {i : ι // a i = 0}
  let P := {i : ι // 0 < a i}
  let N := {i : ι // a i < 0}
  let f : Z ⊕ (N × P) → E →ᵃ[ℝ] ℝ := Sum.elim
    (fun i => -c i.1)
    (fun ij => (a ij.1.1)⁻¹ • c ij.1.1 - (a ij.2.1)⁻¹ • c ij.2.1)
  have heq : {x | ∃ t : ℝ, ∀ i, a i * t ≤ c i x} = {x | ∀ i, f i x ≤ 0} := by
    ext x
    rw [Set.mem_ofPred_eq, exists_scalar_iff]
    constructor
    · rintro ⟨hz, hp⟩
      rintro (i | ⟨i, j⟩)
      · change -(c i.1 x) ≤ 0
        linarith [hz i.1 i.2]
      · change (a i.1)⁻¹ * c i.1 x - (a j.1)⁻¹ * c j.1 x ≤ 0
        exact sub_nonpos.mpr (by simpa only [div_eq_inv_mul] using hp i.1 j.1 i.2 j.2)
    · intro h
      constructor
      · intro i hi
        have hi' := h (Sum.inl ⟨i, hi⟩)
        change -(c i x) ≤ 0 at hi'
        linarith
      · intro i j hi hj
        have hij := h (Sum.inr (⟨i, hi⟩, ⟨j, hj⟩))
        change (a i)⁻¹ * c i x - (a j)⁻¹ * c j x ≤ 0 at hij
        simpa only [div_eq_inv_mul] using sub_nonpos.mp hij
  rw [heq]
  exact hasFiniteHalfspaces_family f

theorem affine_apply_prod (f : E × ℝ →ᵃ[ℝ] ℝ) (x : E) (t : ℝ) :
    f (x, t) = f.linear (0, 1) * t + f (x, 0) := by
  have h := f.map_vadd (x, 0) (t • (0, 1))
  rw [f.linear.map_smul] at h
  simpa [vadd_eq_add, smul_eq_mul, mul_comm] using h

/-- Projection along one real coordinate preserves finite halfspace descriptions. -/
theorem HasFiniteHalfspaces.exists_scalar {S : Set (E × ℝ)}
    (hS : HasFiniteHalfspaces S) :
    HasFiniteHalfspaces {x | ∃ t : ℝ, (x, t) ∈ S} := by
  classical
  obtain ⟨s, hs⟩ := hS
  let g : E →ᵃ[ℝ] E × ℝ := (AffineMap.id ℝ E).prod (AffineMap.const ℝ E 0)
  have heq : {x | ∃ t : ℝ, (x, t) ∈ S} =
      {x | ∃ t : ℝ, ∀ f : s, f.1.linear (0, 1) * t ≤ (-f.1.comp g) x} := by
    ext x
    simp only [Set.mem_ofPred_eq, hs]
    apply exists_congr
    intro t
    constructor
    · intro h f
      have hf := h f.1 f.2
      rw [affine_apply_prod] at hf
      change f.1.linear (0, 1) * t ≤ -f.1 (x, 0)
      linarith
    · intro h f hf
      have hh := h ⟨f, hf⟩
      change f.linear (0, 1) * t ≤ -f (x, 0) at hh
      rw [affine_apply_prod]
      linarith
  rw [heq]
  exact hasFiniteHalfspaces_exists_scalar _ _

/-- Split the first coordinate off a finite real tuple. -/
def consMap (n : ℕ) : (E × (Fin n → ℝ)) × ℝ →ₗ[ℝ] E × (Fin (n + 1) → ℝ) where
  toFun p := (p.1.1, Fin.cons p.2 p.1.2)
  map_add' _ _ := Prod.ext rfl (funext (Fin.cases rfl (fun _ => rfl)))
  map_smul' _ _ := Prod.ext rfl (funext (Fin.cases rfl (fun _ => rfl)))

/-- Projection along any finite tuple of real coordinates preserves finite
halfspace descriptions. -/
theorem HasFiniteHalfspaces.exists_fin (n : ℕ) {S : Set (E × (Fin n → ℝ))}
    (hS : HasFiniteHalfspaces S) :
    HasFiniteHalfspaces {x | ∃ w : Fin n → ℝ, (x, w) ∈ S} := by
  induction n with
  | zero =>
      let g : E →ᵃ[ℝ] E × (Fin 0 → ℝ) :=
        (AffineMap.id ℝ E).prod (AffineMap.const ℝ E 0)
      have heq : {x | ∃ w : Fin 0 → ℝ, (x, w) ∈ S} = g ⁻¹' S := by
        ext x
        constructor
        · rintro ⟨w, hw⟩
          have hwzero : w = 0 := Subsingleton.elim _ _
          simpa [g, hwzero] using hw
        · intro hx
          exact ⟨0, hx⟩
      rw [heq]
      exact hS.preimage g
  | succ n ih =>
      have hfirst := (hS.preimage (consMap (E := E) n).toAffineMap).exists_scalar
      have hrest := ih hfirst
      have heq : {x | ∃ w : Fin (n + 1) → ℝ, (x, w) ∈ S} =
          {x | ∃ w : Fin n → ℝ, ∃ t : ℝ, (x, Fin.cons t w) ∈ S} := by
        ext x
        constructor
        · rintro ⟨w, hw⟩
          exact ⟨Fin.tail w, w 0, by simpa using hw⟩
        · rintro ⟨w, t, hwt⟩
          exact ⟨Fin.cons t w, hwt⟩
      rw [heq]
      exact hrest

/-- The projected coordinates may have any finite indexing type. -/
theorem HasFiniteHalfspaces.exists_fintype {ι : Type*} [Fintype ι]
    {S : Set (E × (ι → ℝ))} (hS : HasFiniteHalfspaces S) :
    HasFiniteHalfspaces {x | ∃ w : ι → ℝ, (x, w) ∈ S} := by
  let e := Fintype.equivFin ι
  let g : E × (Fin (Fintype.card ι) → ℝ) →ₗ[ℝ] E × (ι → ℝ) :=
    { toFun := fun p => (p.1, fun i => p.2 (e i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hp := (hS.preimage g.toAffineMap).exists_fin (Fintype.card ι)
  have heq : {x | ∃ w : ι → ℝ, (x, w) ∈ S} =
      {x | ∃ w : Fin (Fintype.card ι) → ℝ, (x, w) ∈ g ⁻¹' S} := by
    ext x
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨fun i => w (e.symm i), ?_⟩
      simpa [g] using hw
    · rintro ⟨w, hw⟩
      exact ⟨fun i => w (e i), hw⟩
  rw [heq]
  exact hp

theorem hasFiniteHalfspaces_eq (f : E →ᵃ[ℝ] ℝ) (b : ℝ) :
    HasFiniteHalfspaces {x | f x = b} := by
  let pos := f - AffineMap.const ℝ E b
  let neg := -pos
  have hp := hasFiniteHalfspaces_family (fun _ : Unit => pos)
  have hn := hasFiniteHalfspaces_family (fun _ : Unit => neg)
  have heq : {x | f x = b} = {x | ∀ _ : Unit, pos x ≤ 0} ∩
      {x | ∀ _ : Unit, neg x ≤ 0} := by
    ext x
    change f x = b ↔ (∀ _ : Unit, f x - b ≤ 0) ∧ (∀ _ : Unit, -(f x - b) ≤ 0)
    simp only [forall_const]
    constructor
    · intro h
      simp [h]
    · rintro ⟨hp, hn⟩
      linarith
  rw [heq]
  exact hp.inter hn

theorem hasFiniteHalfspaces_stdSimplex (ι : Type*) [Fintype ι] :
    HasFiniteHalfspaces (stdSimplex ℝ ι) := by
  let p : ι → (ι → ℝ) →ᵃ[ℝ] ℝ := fun i => -(LinearMap.proj i).toAffineMap
  let s : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ i, LinearMap.proj i
  have heq : stdSimplex ℝ ι = {w | ∀ i, p i w ≤ 0} ∩ {w | s w = 1} := by
    ext w
    simp only [stdSimplex, Set.mem_ofPred_eq, Set.mem_inter_iff, s,
      LinearMap.sum_apply, LinearMap.proj_apply]
    apply and_congr_left
    intro _
    exact forall_congr' fun i => by change 0 ≤ w i ↔ -(w i) ≤ 0; simp
  rw [heq]
  exact (hasFiniteHalfspaces_family p).inter (hasFiniteHalfspaces_eq s.toAffineMap 1)

/-- Equality of two maps into a finite coordinate space uses two halfspaces per
coordinate. -/
theorem hasFiniteHalfspaces_eq_maps {δ : Type*} [Fintype δ]
    (f g : E →ᵃ[ℝ] (δ → ℝ)) : HasFiniteHalfspaces {x | f x = g x} := by
  let p : δ → E →ᵃ[ℝ] ℝ := fun i => (LinearMap.proj i).toAffineMap.comp (f - g)
  have hp := hasFiniteHalfspaces_family p
  have hn := hasFiniteHalfspaces_family (fun i => -p i)
  have heq : {x | f x = g x} = {x | ∀ i, p i x ≤ 0} ∩ {x | ∀ i, (-p i) x ≤ 0} := by
    ext x
    constructor
    · intro hx
      change f x = g x at hx
      constructor <;> intro i
      · change f x i - g x i ≤ 0
        rw [hx]
        simp
      · change -(f x i - g x i) ≤ 0
        rw [hx]
        simp
    · rintro ⟨hp, hn⟩
      apply funext
      intro i
      have hpi := hp i
      have hni := hn i
      change f x i - g x i ≤ 0 at hpi
      change -(f x i - g x i) ≤ 0 at hni
      linarith
  rw [heq]
  exact hp.inter hn

/-- An affine image between finite real coordinate spaces preserves finite
halfspace descriptions. -/
theorem HasFiniteHalfspaces.image {ι δ : Type*} [Fintype ι] [Fintype δ]
    {S : Set (ι → ℝ)} (hS : HasFiniteHalfspaces S) (f : (ι → ℝ) →ᵃ[ℝ] (δ → ℝ)) :
    HasFiniteHalfspaces (f '' S) := by
  let p : ((δ → ℝ) × (ι → ℝ)) →ᵃ[ℝ] (δ → ℝ) := AffineMap.fst
  let q : ((δ → ℝ) × (ι → ℝ)) →ᵃ[ℝ] (ι → ℝ) := AffineMap.snd
  have hgraph := (hS.preimage q).inter (hasFiniteHalfspaces_eq_maps p (f.comp q))
  have hproj := hgraph.exists_fintype
  have heq : f '' S = {x | ∃ w : ι → ℝ, (x, w) ∈ q ⁻¹' S ∩ {y | p y = f (q y)}} := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, rfl⟩
    · rintro ⟨w, hw, hx⟩
      exact ⟨w, hw, hx.symm⟩
  rw [heq]
  exact hproj

/-- Every finite convex hull in a finite real coordinate space has a finite
closed affine-halfspace description, including all degenerate cases. -/
theorem hasFiniteHalfspaces_convexHull {δ : Type*} [Fintype δ]
    (V : Finset (δ → ℝ)) : HasFiniteHalfspaces (convexHull ℝ (V : Set (δ → ℝ))) := by
  classical
  let := V.finite_toSet.fintype
  let A : (↑(V : Set (δ → ℝ)) → ℝ) →ₗ[ℝ] (δ → ℝ) :=
    ∑ x : (V : Set (δ → ℝ)), (LinearMap.proj (R := ℝ) x).smulRight x.1
  have hA (x : (V : Set (δ → ℝ))) : A (Pi.single x 1) = x.1 := by
    simp [A, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Pi.single_apply, ite_smul]
  have himage : A '' range (fun x : (V : Set (δ → ℝ)) => Pi.single x 1) =
      (V : Set (δ → ℝ)) := by
    rw [← range_comp']
    simp_rw [hA]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact x.property
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  have h := (hasFiniteHalfspaces_stdSimplex (V : Set (δ → ℝ))).image A.toAffineMap
  change HasFiniteHalfspaces (A '' stdSimplex ℝ (V : Set (δ → ℝ))) at h
  rw [← convexHull_rangle_single_eq_stdSimplex, A.image_convexHull, himage] at h
  exact h

/-- Enumerate a finite halfspace description by `Fin k`. -/
theorem HasFiniteHalfspaces.exists_fin_description {S : Set E} (hS : HasFiniteHalfspaces S) :
    ∃ (k : ℕ) (g : Fin k → E →ᵃ[ℝ] ℝ) (b : Fin k → ℝ),
      S = {x | ∀ j, g j x ≤ b j} := by
  classical
  obtain ⟨s, hs⟩ := hS
  let e := s.equivFin
  refine ⟨s.card, fun j => (e.symm j).1, fun _ => 0, ?_⟩
  ext x
  rw [hs]
  constructor
  · intro h j
    exact h _ (e.symm j).2
  · intro h f hf
    have hh := h (e ⟨f, hf⟩)
    simpa using hh

/-- A finite hull in any finite real coordinate space is an intersection of
finitely many closed affine halfspaces. In particular, take `δ = Fin 2` for the
plane. Empty, singleton, and lower-dimensional hulls are included. -/
theorem convexHull_eq_finite_halfspaces {δ : Type*} [Fintype δ] (V : Finset (δ → ℝ)) :
    ∃ (k : ℕ) (g : Fin k → (δ → ℝ) →ᵃ[ℝ] ℝ) (b : Fin k → ℝ),
      convexHull ℝ (V : Set (δ → ℝ)) = {x | ∀ j, g j x ≤ b j} :=
  (hasFiniteHalfspaces_convexHull V).exists_fin_description

end Plank.FiniteHullHalfspaces
end

#print axioms Plank.FiniteHullHalfspaces.exists_between_finite_sets
#print axioms Plank.FiniteHullHalfspaces.exists_scalar_iff
#print axioms Plank.FiniteHullHalfspaces.hasFiniteHalfspaces_family
#print axioms Plank.FiniteHullHalfspaces.HasFiniteHalfspaces.inter
#print axioms Plank.FiniteHullHalfspaces.HasFiniteHalfspaces.preimage
#print axioms Plank.FiniteHullHalfspaces.hasFiniteHalfspaces_exists_scalar
#print axioms Plank.FiniteHullHalfspaces.affine_apply_prod
#print axioms Plank.FiniteHullHalfspaces.HasFiniteHalfspaces.exists_scalar
#print axioms Plank.FiniteHullHalfspaces.HasFiniteHalfspaces.exists_fin
#print axioms Plank.FiniteHullHalfspaces.HasFiniteHalfspaces.exists_fintype
#print axioms Plank.FiniteHullHalfspaces.hasFiniteHalfspaces_eq
#print axioms Plank.FiniteHullHalfspaces.hasFiniteHalfspaces_stdSimplex
#print axioms Plank.FiniteHullHalfspaces.hasFiniteHalfspaces_eq_maps
#print axioms Plank.FiniteHullHalfspaces.HasFiniteHalfspaces.image
#print axioms Plank.FiniteHullHalfspaces.hasFiniteHalfspaces_convexHull
#print axioms Plank.FiniteHullHalfspaces.HasFiniteHalfspaces.exists_fin_description
#print axioms Plank.FiniteHullHalfspaces.convexHull_eq_finite_halfspaces
