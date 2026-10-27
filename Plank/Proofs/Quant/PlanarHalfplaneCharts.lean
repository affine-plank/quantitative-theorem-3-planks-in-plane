/- Parameter charts for half-planes of arbitrary fixed directions. -/
module

public import Plank.Proofs.Quant.PlanarPolygonCharts
import Mathlib.Tactic.Choose

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarHalfplaneCharts

open Set MeasureTheory PlanarPolygonHalfplanes PlanarPolygonCharts

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Points in one open sign region preserve every weak comparison that
holds at any other point of that region. -/
theorem compatible_of_mem_openRegion {τ : Type*} (F : τ → E →ᵃ[ℝ] ℝ)
    (s : τ → Bool) {x y : E} (hx : x ∈ openRegion F s) (hy : y ∈ openRegion F s) :
    Compatible F x y := by
  classical
  intro w hw
  by_cases hz : F w = 0
  · simp [hz]
  · have hxw := hx w
    have hyw := hy w
    simp only [hz, if_false] at hxw hyw
    by_cases hs : s w = true
    · simp only [hs, if_pos] at hyw
      exact hyw.le
    · simp only [hs] at hxw
      exact (not_lt_of_ge hw hxw).elim

/-- Affine bounds are formed before evaluation, so they retain affine
dependence on the full parameter vector. -/
def boundMap {ι : Type*} {p : ι → Prop}
    (D : ι → ℝ) (C : ι → E →ᵃ[ℝ] ℝ) (a : E →ᵃ[ℝ] ℝ) :
    Option {i // p i} → E →ᵃ[ℝ] ℝ
  | none => a
  | some i => (D i)⁻¹ • C i

theorem boundMap_eval {ι : Type*} {p : ι → Prop}
    (D : ι → ℝ) (C : ι → E →ᵃ[ℝ] ℝ) (a : E →ᵃ[ℝ] ℝ) (x : E)
    (k : Option {i // p i}) :
    boundMap D C a k x = withBound (fun i => C i x/D i) (a x) k := by
  cases k with
  | none => rfl
  | some i =>
    change (D i)⁻¹*C i x = C i x/D i
    rw [div_eq_mul_inv, mul_comm]

abbrev LowerX {ι : Type*} (A B : ι → ℝ) := Option {i // B i = 0 ∧ A i < 0}
abbrev UpperX {ι : Type*} (A B : ι → ℝ) := Option {i // B i = 0 ∧ 0 < A i}
abbrev LowerY {ι : Type*} (B : ι → ℝ) := Option {i // B i < 0}
abbrev UpperY {ι : Type*} (B : ι → ℝ) := Option {i // 0 < B i}

/-- At fixed selected horizontal extrema, the actual closed half-plane
intersection is the graph model. Arbitrary vertical sides are included;
each half-plane normal is required to be nonzero. -/
theorem boxedRegion_eq_graph_of_active {ι : Type*}
    (a b c d : E →ᵃ[ℝ] ℝ) (A B : ι → ℝ) (C : ι → E →ᵃ[ℝ] ℝ)
    (hnormal : ∀ i, B i = 0 → A i ≠ 0) (x : E)
    (p : LowerX A B) (q : UpperX A B)
    (hL : ∀ k : LowerX A B, boundMap A C a k x ≤ boundMap A C a p x)
    (hU : ∀ k : UpperX A B, boundMap A C b q x ≤ boundMap A C b k x) :
    boxedRegion (a x) (b x) (c x) (d x) A B (fun i => C i x) =
      closedSlab (boundMap A C a p x) (boundMap A C b q x)
        (graphSlope (p := fun i => B i < 0) A B) (fun k => boundMap B C c k x)
        (graphSlope (p := fun i => 0 < B i) A B) (fun k => boundMap B C d k x) := by
  have hvertical (y : ℝ) :
      y ∈ Icc (boundMap A C a p x) (boundMap A C b q x) ↔
        y ∈ Icc (a x) (b x) ∧ ∀ i, B i = 0 → A i*y ≤ C i x := by
    constructor
    · intro hy
      have hl (k : LowerX A B) : boundMap A C a k x ≤ y := (hL k).trans hy.1
      have hu (k : UpperX A B) : y ≤ boundMap A C b k x := hy.2.trans (hU k)
      refine ⟨⟨hl none, hu none⟩, fun i hBi => ?_⟩
      rcases lt_or_gt_of_ne (hnormal i hBi) with hneg | hpos
      · have h : C i x/A i ≤ y := by
          simpa only [boundMap_eval, withBound] using hl (some ⟨i, hBi, hneg⟩)
        simpa only [mul_comm] using (div_le_iff_of_neg hneg).mp h
      · have h : y ≤ C i x/A i := by
          simpa only [boundMap_eval, withBound] using hu (some ⟨i, hBi, hpos⟩)
        simpa only [mul_comm] using (le_div_iff₀ hpos).mp h
    · rintro ⟨hy, h⟩
      constructor
      · cases p with
        | none => exact hy.1
        | some i =>
          rw [boundMap_eval]
          apply (div_le_iff_of_neg i.property.2).mpr
          simpa only [mul_comm] using h i i.property.1
      · cases q with
        | none => exact hy.2
        | some i =>
          rw [boundMap_eval]
          apply (le_div_iff₀ i.property.2).mpr
          simpa only [mul_comm] using h i i.property.1
  have hl : (fun k : LowerY B => boundMap B C c k x) = graphOffset B (fun i => C i x) (c x) := by
    funext k
    exact boundMap_eval B C c x k
  have hu : (fun k : UpperY B => boundMap B C d k x) = graphOffset B (fun i => C i x) (d x) := by
    funext k
    exact boundMap_eval B C d x k
  rw [hl, hu]
  exact boxedRegion_eq_closedSlab_of_vertical_interval (a x) (b x) (c x) (d x)
    _ _ A B (fun i => C i x) hvertical

/-- The common wall family includes all choices of horizontal extremal
facets and the graph arrangement associated to every such choice. -/
abbrev HalfplaneWallIndex {ι : Type*} (A B : ι → ℝ) :=
  (LowerX A B × LowerX A B) ⊕ ((UpperX A B × UpperX A B) ⊕
    ((LowerX A B × UpperX A B) × WallIndex (LowerY B) (UpperY B)))

def halfplaneWalls {ι : Type*}
    (a b c d : E →ᵃ[ℝ] ℝ) (A B : ι → ℝ) (C : ι → E →ᵃ[ℝ] ℝ) :
    HalfplaneWallIndex A B → E →ᵃ[ℝ] ℝ
  | Sum.inl (p, q) => boundMap A C a p-boundMap A C a q
  | Sum.inr (Sum.inl (p, q)) => boundMap A C b p-boundMap A C b q
  | Sum.inr (Sum.inr ((p, q), w)) => wall (boundMap A C a p) (boundMap A C b q)
      (graphSlope (p := fun i => B i < 0) A B) (boundMap B C c)
      (graphSlope (p := fun i => 0 < B i) A B) (boundMap B C d) w

/-- The finite extremal choices and the graph certificates remain valid
under the common affine comparisons. This constructs a quadratic actual
area formula with arbitrary fixed nonzero half-plane normals. -/
theorem exists_boxed_formula_on_compatible {ι : Type*} [Fintype ι]
    (a b c d : E →ᵃ[ℝ] ℝ) (A B : ι → ℝ) (C : ι → E →ᵃ[ℝ] ℝ)
    (hnormal : ∀ i, B i = 0 → A i ≠ 0) (x : E) :
    ∃ Q : QuadraticFormula E, ∀ y : E, Compatible (halfplaneWalls a b c d A B C) x y →
      (volume (boxedRegion (a y) (b y) (c y) (d y) A B (fun i => C i y))).toReal = Q.eval y := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_max_image Finset.univ
    (fun k : LowerX A B => boundMap A C a k x) Finset.univ_nonempty
  obtain ⟨q, _, hq⟩ := Finset.exists_min_image Finset.univ
    (fun k : UpperX A B => boundMap A C b k x) Finset.univ_nonempty
  obtain ⟨Q, hQ⟩ := exists_formula_on_compatible (boundMap A C a p) (boundMap A C b q)
    (graphSlope (p := fun i => B i < 0) A B) (boundMap B C c)
    (graphSlope (p := fun i => 0 < B i) A B) (boundMap B C d) x
  refine ⟨Q, fun y hy => ?_⟩
  have hL (k : LowerX A B) : boundMap A C a k y ≤ boundMap A C a p y :=
    sub_nonpos.mp (hy (Sum.inl (k, p)) (sub_nonpos.mpr (hp k (Finset.mem_univ _))))
  have hU (k : UpperX A B) : boundMap A C b q y ≤ boundMap A C b k y :=
    sub_nonpos.mp (hy (Sum.inr (Sum.inl (q, k))) (sub_nonpos.mpr (hq k (Finset.mem_univ _))))
  rw [boxedRegion_eq_graph_of_active a b c d A B C hnormal y p q hL hU]
  exact hQ y (fun w hw => hy (Sum.inr (Sum.inr ((p, q), w))) hw)

/-- The generic comparison profile for any affine wall family. -/
def signProfile {τ : Type*} (F : τ → E →ᵃ[ℝ] ℝ) (x : E) : τ → Bool := by
  classical
  exact fun w => decide (F w x ≤ 0)

theorem mem_openRegion_signProfile {τ : Type*} (F : τ → E →ᵃ[ℝ] ℝ) (x : E)
    (hoff : ∀ w, F w ≠ 0 → F w x ≠ 0) : x ∈ openRegion F (signProfile F x) := by
  classical
  intro w
  by_cases hz : F w = 0
  · simp [hz, signProfile]
  · simp only [hz, if_false]
    by_cases hle : F w x ≤ 0
    · have hlt := lt_of_le_of_ne hle (hoff w hz)
      simpa only [signProfile, decide_eq_true hle, if_pos] using hlt
    · have hlt := lt_of_not_ge hle
      simpa only [signProfile, decide_eq_false hle, Bool.false_eq_true, if_false] using hlt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem isClosed_compatible {τ : Type*} (F : τ → V →ᵃ[ℝ] ℝ) (x : V) :
    IsClosed {y | Compatible F x y} := by
  unfold Compatible
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro w
  exact isClosed_iInter fun _ => isClosed_le (continuous_affine (F w)) continuous_const

/-- The closures of open regions of any finite affine arrangement cover
the full parameter space; identically zero walls are harmless. -/
theorem closures_regions_cover {τ : Type*} [Finite τ] (F : τ → V →ᵃ[ℝ] ℝ) :
    (⋃ s : τ → Bool, closure (openRegion F s)) = univ := by
  have hd : Dense (⋃ s : τ → Bool, openRegion F s) := by
    apply (dense_off_walls F).mono
    intro x hx
    exact mem_iUnion.mpr ⟨signProfile F x, mem_openRegion_signProfile F x hx⟩
  rw [← closure_iUnion_of_finite]
  exact hd.closure_eq

/-- A local construction from preserved weak inequalities yields a finite
atlas valid on chart closures, with no assumed continuity of the target. -/
theorem exists_closed_atlas {τ : Type*} (F : τ → V →ᵃ[ℝ] ℝ) (g : V → ℝ)
    (hpoint : ∀ x, ∃ q : QuadraticFormula V, ∀ y, Compatible F x y → g y = q.eval y) :
    ∃ q : (τ → Bool) → QuadraticFormula V, ∀ s, ∀ y ∈ closure (openRegion F s),
      g y = (q s).eval y := by
  classical
  have hex (s : τ → Bool) : ∃ q : QuadraticFormula V, ∀ y ∈ closure (openRegion F s),
      g y = q.eval y := by
    by_cases hs : (openRegion F s).Nonempty
    · obtain ⟨x, hx⟩ := hs
      obtain ⟨q, hq⟩ := hpoint x
      refine ⟨q, fun y hy => hq y ?_⟩
      exact closure_minimal (fun z hz => compatible_of_mem_openRegion F s hx hz)
        (isClosed_compatible F x) hy
    · refine ⟨QuadraticFormula.zero, fun y hy => ?_⟩
      have hempty := not_nonempty_iff_eq_empty.mp hs
      simp only [hempty, closure_empty, mem_empty_iff_false] at hy
  choose q hq using hex
  exact ⟨q, hq⟩

/-- Continuity follows from the constructed finite closed atlas. -/
theorem continuous_of_closed_atlas {τ : Type*} [Finite τ]
    (F : τ → V →ᵃ[ℝ] ℝ) (g : V → ℝ) (q : (τ → Bool) → QuadraticFormula V)
    (hq : ∀ s, ∀ x ∈ closure (openRegion F s), g x = (q s).eval x) : Continuous g := by
  apply continuous_iff_isClosed.mpr
  intro T hT
  have heq : g ⁻¹' T = ⋃ s, closure (openRegion F s) ∩ ((q s).eval ⁻¹' T) := by
    ext x
    constructor
    · intro hx
      have hxcover : x ∈ ⋃ s : τ → Bool, closure (openRegion F s) := by
        rw [closures_regions_cover]
        trivial
      obtain ⟨s, hs⟩ := mem_iUnion.mp hxcover
      refine mem_iUnion.mpr ⟨s, hs, ?_⟩
      change (q s).eval x ∈ T
      rwa [← hq s x hs]
    · intro hx
      obtain ⟨s, hs, hv⟩ := mem_iUnion.mp hx
      change g x ∈ T
      rwa [hq s x hs]
  rw [heq]
  exact isClosed_iUnion_of_finite fun s =>
    isClosed_closure.inter (hT.preimage (q s).continuous_eval)

/-- Arbitrary fixed nonzero normals now have a common finite affine atlas
for the actual area, including vertical sides and all boundary incidences. -/
theorem exists_boxed_area_charts {ι : Type*} [Fintype ι]
    (a b c d : V →ᵃ[ℝ] ℝ) (A B : ι → ℝ) (C : ι → V →ᵃ[ℝ] ℝ)
    (hnormal : ∀ i, B i = 0 → A i ≠ 0) :
    ∃ Q : (HalfplaneWallIndex A B → Bool) → QuadraticFormula V, ∀ s,
      IsOpen (openRegion (halfplaneWalls a b c d A B C) s) ∧
      Convex ℝ (openRegion (halfplaneWalls a b c d A B C) s) ∧
      ∀ x ∈ closure (openRegion (halfplaneWalls a b c d A B C) s),
        (volume (boxedRegion (a x) (b x) (c x) (d x) A B (fun i => C i x))).toReal = (Q s).eval x := by
  classical
  obtain ⟨Q, hQ⟩ := exists_closed_atlas (halfplaneWalls a b c d A B C)
    (fun x => (volume (boxedRegion (a x) (b x) (c x) (d x) A B (fun i => C i x))).toReal)
    (exists_boxed_formula_on_compatible a b c d A B C hnormal)
  exact ⟨Q, fun s => ⟨isOpen_openRegion _ _, convex_openRegion _ _, hQ s⟩⟩

theorem continuous_boxed_area {ι : Type*} [Fintype ι]
    (a b c d : V →ᵃ[ℝ] ℝ) (A B : ι → ℝ) (C : ι → V →ᵃ[ℝ] ℝ)
    (hnormal : ∀ i, B i = 0 → A i ≠ 0) :
    Continuous (fun x =>
      (volume (boxedRegion (a x) (b x) (c x) (d x) A B (fun i => C i x))).toReal) := by
  obtain ⟨Q, hQ⟩ := exists_boxed_area_charts a b c d A B C hnormal
  exact continuous_of_closed_atlas _ _ Q (fun s => (hQ s).2.2)

/-- Refining finitely many affine wall families constructs a single atlas
on which all component functions have their own quadratic formulas. -/
theorem exists_common_closed_atlas {σ : Type*} {τ : σ → Type*}
    (F : (j : σ) → τ j → V →ᵃ[ℝ] ℝ) (g : σ → V → ℝ)
    (hpoint : ∀ j x, ∃ q : QuadraticFormula V, ∀ y,
      Compatible (F j) x y → g j y = q.eval y) :
    ∃ q : ((Sigma τ) → Bool) → σ → QuadraticFormula V, ∀ s j,
      ∀ x ∈ closure (openRegion (fun w : Sigma τ => F w.1 w.2) s),
        g j x = (q s j).eval x := by
  classical
  have hex (j : σ) : ∃ q : ((Sigma τ) → Bool) → QuadraticFormula V, ∀ s,
      ∀ x ∈ closure (openRegion (fun w : Sigma τ => F w.1 w.2) s),
        g j x = (q s).eval x := by
    apply exists_closed_atlas
    intro x
    obtain ⟨q, hq⟩ := hpoint j x
    exact ⟨q, fun y hy => hq y (fun w hw => hy ⟨j, w⟩ hw)⟩
  choose q hq using hex
  exact ⟨fun s j => q j s, fun s j => hq j s⟩

/-- A finite family of actual bounded half-plane intersections has one
common finite affine arrangement. All component area formulas hold on
the closures of the same open convex regions, including degeneracies. -/
theorem exists_common_boxed_area_charts {σ ι : Type*} [Fintype σ] [Fintype ι]
    (a b c d : σ → V →ᵃ[ℝ] ℝ) (A B : σ → ι → ℝ)
    (C : σ → ι → V →ᵃ[ℝ] ℝ) (hnormal : ∀ j i, B j i = 0 → A j i ≠ 0) :
    let W := Sigma (fun j => HalfplaneWallIndex (A j) (B j))
    let F := fun w : W => halfplaneWalls (a w.1) (b w.1) (c w.1) (d w.1) (A w.1) (B w.1) (C w.1) w.2
    ∃ Q : (W → Bool) → σ → QuadraticFormula V,
      (∀ s, IsOpen (openRegion F s) ∧ Convex ℝ (openRegion F s) ∧
        ∀ j, ∀ x ∈ closure (openRegion F s),
          (volume (boxedRegion (a j x) (b j x) (c j x) (d j x)
            (A j) (B j) (fun i => C j i x))).toReal = (Q s j).eval x) ∧
      (⋃ s, closure (openRegion F s)) = univ := by
  classical
  dsimp only
  obtain ⟨Q, hQ⟩ := exists_common_closed_atlas
    (fun j => halfplaneWalls (a j) (b j) (c j) (d j) (A j) (B j) (C j))
    (fun j x => (volume (boxedRegion (a j x) (b j x) (c j x) (d j x)
      (A j) (B j) (fun i => C j i x))).toReal)
    (fun j => exists_boxed_formula_on_compatible (a j) (b j) (c j) (d j)
      (A j) (B j) (C j) (hnormal j))
  exact ⟨Q, fun s => ⟨isOpen_openRegion _ _, convex_openRegion _ _, hQ s⟩,
    closures_regions_cover _⟩

end Plank.PlanarHalfplaneCharts
