module
/-
# Proofs/Transport — the width toolbox and the one-triangle reduction

Mirror of `Plank/Transport.lean`.  §0 (elementary width algebra) now lives in
`Plank.Proofs.TriangleGeometry`, re-exported here, except the two
`stdTriangle` readings kept below; §1
builds the affine chart of a triangle and pulls planks back along it,
which is the whole content of "one triangle suffices"; §2 is the
dictionary with `EuclideanSpace ℝ (Fin 2)`.
-/
public import Plank.Proofs.Basic
public import Plank.Proofs.TriangleGeometry
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

@[expose] public section


public section

noncomputable section

open Proofs.Basic

namespace Proofs.Transport

/-! ## §0  The width toolbox — see `Plank.Proofs.TriangleGeometry`

Only the two readings of the standard triangle remain here. -/

theorem stdTriangle_mem_iff (P : ℝ × ℝ) :
    P ∈ stdTriangle ↔ 0 ≤ P.1 ∧ 0 ≤ P.2 ∧ P.1 + P.2 ≤ 1 := by
  constructor
  · rintro ⟨α, β, γ, hα, hβ, hγ, hsum, rfl⟩
    refine ⟨by simpa [stdTriangle] using hβ, by simpa [stdTriangle] using hγ, ?_⟩
    simp only [stdTriangle, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul]
    norm_num
    linarith
  · rintro ⟨h1, h2, h3⟩
    exact ⟨1 - P.1 - P.2, P.1, P.2, by linarith, h1, h2, by ring,
      by simp [stdTriangle]⟩

theorem stdTriangle_width_eq (u : ℝ × ℝ) :
    stdTriangle.width u = max 0 (max u.1 u.2) - min 0 (min u.1 u.2) := by
  simp [Triangle.width, stdTriangle, dot]

/-! ## §1  The affine chart of a triangle

`chart T` is the affine map carrying the standard triangle onto `T`;
`pullbackPlank T` is the induced map on planks.  Together they say that
a covering of `T` is a covering of the standard triangle with the same
relative widths. -/

/-- The affine chart `(x, y) ↦ A + x(B − A) + y(C − A)`. -/
def chart (T : Triangle) (P : ℝ × ℝ) : ℝ × ℝ :=
  T.A + P.1 • (T.B - T.A) + P.2 • (T.C - T.A)

theorem chart_std_A (T : Triangle) : chart T stdTriangle.A = T.A := by
  simp [chart, stdTriangle]

theorem chart_std_B (T : Triangle) : chart T stdTriangle.B = T.B := by
  simp [chart, stdTriangle]

theorem chart_std_C (T : Triangle) : chart T stdTriangle.C = T.C := by
  simp [chart, stdTriangle]

theorem chart_mem (T : Triangle) {P : ℝ × ℝ} (hP : P ∈ stdTriangle) :
    chart T P ∈ T := by
  obtain ⟨h1, h2, h3⟩ := (stdTriangle_mem_iff P).mp hP
  exact ⟨1 - P.1 - P.2, P.1, P.2, by linarith, h1, h2, by ring, by
    simp only [chart]; module⟩

/-- The pulled-back normal: the chart's transpose applied to `u`. -/
theorem pullback_u_ne_zero (T : Triangle) (p : Plank) :
    ((dot p.u (T.B - T.A), dot p.u (T.C - T.A)) : ℝ × ℝ) ≠ 0 := by
  intro h
  refine det3_ne_zero T (det3_eq_zero_of_dot_edges p.u_ne_zero ?_ ?_)
  · simpa using congrArg Prod.fst h
  · simpa using congrArg Prod.snd h

/-- The plank `p ⊆ ℝ²`, read in the chart of `T`. -/
def pullbackPlank (T : Triangle) (p : Plank) : Plank :=
  ⟨(dot p.u (T.B - T.A), dot p.u (T.C - T.A)),
   p.lo - dot p.u T.A, p.hi - dot p.u T.A,
   pullback_u_ne_zero T p, by linarith [p.lo_le_hi]⟩

theorem dot_pullback (T : Triangle) (p : Plank) (P : ℝ × ℝ) :
    dot (pullbackPlank T p).u P = dot p.u (chart T P) - dot p.u T.A := by
  simp only [pullbackPlank, chart, dot, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
  ring

theorem width_pullback (T : Triangle) (p : Plank) :
    stdTriangle.width (pullbackPlank T p).u = T.width p.u := by
  rw [stdTriangle_width_eq]
  have h1 : ((pullbackPlank T p).u).1 = dot p.u T.B - dot p.u T.A := by
    simp [pullbackPlank, dot_sub_right]
  have h2 : ((pullbackPlank T p).u).2 = dot p.u T.C - dot p.u T.A := by
    simp [pullbackPlank, dot_sub_right]
  rw [h1, h2, spread_shift]
  rfl

theorem relWidth_pullback (T : Triangle) (p : Plank) :
    (pullbackPlank T p).relWidth stdTriangle = p.relWidth T := by
  rw [Plank.relWidth, Plank.relWidth, width_pullback]
  simp only [pullbackPlank]
  ring

theorem mem_pullback_iff (T : Triangle) (p : Plank) (P : ℝ × ℝ) :
    P ∈ pullbackPlank T p ↔ chart T P ∈ p := by
  rw [mem_plank_iff, mem_plank_iff, dot_pullback]
  have hlo : (pullbackPlank T p).lo = p.lo - dot p.u T.A := rfl
  have hhi : (pullbackPlank T p).hi = p.hi - dot p.u T.A := rfl
  rw [hlo, hhi]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **The one-triangle reduction.** -/
theorem threePlanks_of_std
    (h : ∀ C : Config, C.Covers → 1 ≤ C.sumRelW) :
    ThreePlanksOnATriangle := by
  intro T p₁ p₂ p₃ hcov
  set C : Config :=
    ⟨![pullbackPlank T p₁, pullbackPlank T p₂, pullbackPlank T p₃]⟩ with hC
  have hCcov : C.Covers := by
    intro P hP
    rcases hcov (chart T P) (chart_mem T hP) with h1 | h1 | h1
    · exact ⟨0, by simpa [hC, mem_pullback_iff] using h1⟩
    · exact ⟨1, by simpa [hC, mem_pullback_iff] using h1⟩
    · exact ⟨2, by simpa [hC, mem_pullback_iff] using h1⟩
  have hsum : C.sumRelW =
      p₁.relWidth T + p₂.relWidth T + p₃.relWidth T := by
    simp only [Config.sumRelW, Config.relW, Fin.sum_univ_three, hC]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [relWidth_pullback, relWidth_pullback, relWidth_pullback]
  rw [← hsum]
  exact h C hCcov

/-- Any triangle is an invertible affine image of the standard one. -/
theorem exists_affineEquiv_stdTriangle (T : Triangle) :
    ∃ f : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ),
      f stdTriangle.A = T.A ∧ f stdTriangle.B = T.B ∧
      f stdTriangle.C = T.C := by
  have hD : det3 T.A T.B T.C ≠ 0 := det3_ne_zero T
  set p : ℝ × ℝ := T.B - T.A with hp
  set q : ℝ × ℝ := T.C - T.A with hq
  set D : ℝ := p.1 * q.2 - p.2 * q.1 with hDdef
  have hD' : D ≠ 0 := by
    simpa [hDdef, hp, hq, det3, Prod.fst_sub, Prod.snd_sub] using hD
  let L : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
    { toFun := fun v => (v.1 * p.1 + v.2 * q.1, v.1 * p.2 + v.2 * q.2)
      map_add' := by intro v w; simp [Prod.ext_iff]; constructor <;> ring
      map_smul' := by intro c v; simp [Prod.ext_iff]; constructor <;> ring
      invFun := fun w => ((w.1 * q.2 - w.2 * q.1) / D,
        (w.2 * p.1 - w.1 * p.2) / D)
      left_inv := by
        intro v
        refine Prod.ext ?_ ?_ <;> field_simp <;> ring
      right_inv := by
        intro w
        refine Prod.ext ?_ ?_ <;> field_simp <;> ring }
  refine ⟨(L.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ (ℝ × ℝ) T.A)), ?_, ?_, ?_⟩
  · simp [L, stdTriangle, AffineEquiv.constVAdd, Equiv.constVAdd, vadd_eq_add]
  · simp [L, stdTriangle, AffineEquiv.constVAdd, Equiv.constVAdd, vadd_eq_add, hp, Prod.ext_iff]
  · simp [L, stdTriangle, AffineEquiv.constVAdd, Equiv.constVAdd, vadd_eq_add, hq, Prod.ext_iff]

/-! ## §2  The dictionary with `EuclideanSpace ℝ (Fin 2)` -/

/-- The plane `ℝ × ℝ` viewed inside `EuclideanSpace ℝ (Fin 2)`. -/
def planeToEuc : (ℝ × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (LinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv.symm

/-- The real inner product of two reals is their product.  (`ℝ` carries
the real-ification of its own `RCLike` inner product, so this is not
`rfl`.) -/
@[simp] theorem real_inner_real (a b : ℝ) : inner ℝ a b = a * b := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]; simp [mul_comm]

theorem inner_planeToEuc (u v : ℝ × ℝ) :
    inner ℝ (planeToEuc u) (planeToEuc v) = dot u v := by
  simp [planeToEuc, PiLp.inner_apply, Fin.sum_univ_two, dot,
    LinearEquiv.finTwoArrow, EuclideanSpace.equiv, mul_comm]

/-! ### The seam: `sSup`/`sInf` over a hull are attained at the vertices -/

section Seam

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `x ↦ ⟪x, w⟫` is a real-linear functional. -/
theorem isLinear_inner_right (w : E) :
    IsLinearMap ℝ (fun x : E => inner ℝ x w) :=
  ⟨fun _ _ => inner_add_left _ _ _, fun _ _ => real_inner_smul_left _ _ _⟩

theorem hull_le (A B C w : E) :
    convexHull ℝ ({A, B, C} : Set E) ⊆
      {x | inner ℝ x w ≤
        max (inner ℝ A w) (max (inner ℝ B w) (inner ℝ C w))} := by
  refine convexHull_min ?_ (convex_halfSpace_le (isLinear_inner_right w) _)
  rintro x (rfl | rfl | rfl) <;> simp only [Set.mem_ofPred_eq]
  · exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem hull_ge (A B C w : E) :
    convexHull ℝ ({A, B, C} : Set E) ⊆
      {x | min (inner ℝ A w) (min (inner ℝ B w) (inner ℝ C w))
        ≤ inner ℝ x w} := by
  refine convexHull_min ?_ (convex_halfSpace_ge (isLinear_inner_right w) _)
  rintro x (rfl | rfl | rfl) <;> simp only [Set.mem_ofPred_eq]
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem mem_hull_triple (A B C : E) :
    A ∈ convexHull ℝ ({A, B, C} : Set E) ∧
    B ∈ convexHull ℝ ({A, B, C} : Set E) ∧
    C ∈ convexHull ℝ ({A, B, C} : Set E) :=
  ⟨subset_convexHull _ _ (by simp), subset_convexHull _ _ (by simp),
    subset_convexHull _ _ (by simp)⟩

theorem sSup_inner_hull (A B C w : E) :
    sSup ((fun x => inner ℝ x w) '' convexHull ℝ ({A, B, C} : Set E))
      = max (inner ℝ A w) (max (inner ℝ B w) (inner ℝ C w)) := by
  obtain ⟨hA, hB, hC⟩ := mem_hull_triple A B C
  have hle : ∀ y ∈ (fun x => inner ℝ x w) '' convexHull ℝ ({A, B, C} : Set E),
      y ≤ max (inner ℝ A w) (max (inner ℝ B w) (inner ℝ C w)) := by
    rintro y ⟨x, hx, rfl⟩; exact hull_le A B C w hx
  have hbdd : BddAbove ((fun x => inner ℝ x w) ''
      convexHull ℝ ({A, B, C} : Set E)) := ⟨_, hle⟩
  refine le_antisymm (csSup_le ⟨_, ⟨A, hA, rfl⟩⟩ hle) ?_
  exact max_le (le_csSup hbdd ⟨A, hA, rfl⟩)
    (max_le (le_csSup hbdd ⟨B, hB, rfl⟩) (le_csSup hbdd ⟨C, hC, rfl⟩))

theorem sInf_inner_hull (A B C w : E) :
    sInf ((fun x => inner ℝ x w) '' convexHull ℝ ({A, B, C} : Set E))
      = min (inner ℝ A w) (min (inner ℝ B w) (inner ℝ C w)) := by
  obtain ⟨hA, hB, hC⟩ := mem_hull_triple A B C
  have hge : ∀ y ∈ (fun x => inner ℝ x w) '' convexHull ℝ ({A, B, C} : Set E),
      min (inner ℝ A w) (min (inner ℝ B w) (inner ℝ C w)) ≤ y := by
    rintro y ⟨x, hx, rfl⟩; exact hull_ge A B C w hx
  have hbdd : BddBelow ((fun x => inner ℝ x w) ''
      convexHull ℝ ({A, B, C} : Set E)) := ⟨_, hge⟩
  refine le_antisymm ?_ (le_csInf ⟨_, ⟨A, hA, rfl⟩⟩ hge)
  exact le_min (csInf_le hbdd ⟨A, hA, rfl⟩)
    (le_min (csInf_le hbdd ⟨B, hB, rfl⟩) (csInf_le hbdd ⟨C, hC, rfl⟩))

end Seam

/-! ### The `Triangle` ↔ `Affine.Simplex` dictionary -/

/-- Collinearity is a linear-equivalence invariant. -/
theorem collinear_of_linearEquiv {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V ≃ₗ[ℝ] W) {A B C : V}
    (h : Collinear ℝ ({f A, f B, f C} : Set W)) :
    Collinear ℝ ({A, B, C} : Set V) := by
  rw [collinear_iff_of_mem (Set.mem_insert (f A) _)] at h
  obtain ⟨v, hv⟩ := h
  rw [collinear_iff_of_mem (Set.mem_insert A _)]
  refine ⟨f.symm v, fun x hx => ?_⟩
  have hfx : f x ∈ ({f A, f B, f C} : Set W) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
  obtain ⟨r, hr⟩ := hv (f x) hfx
  exact ⟨r, by simpa [vadd_eq_add, map_add, map_smul] using congrArg f.symm hr⟩

theorem not_collinear_planeToEuc (T : Triangle) :
    ¬ Collinear ℝ ({planeToEuc T.A, planeToEuc T.B, planeToEuc T.C} :
      Set (EuclideanSpace ℝ (Fin 2))) := fun h =>
  T.not_collinear (collinear_of_linearEquiv planeToEuc h)

/-- The image of the filled triangle is the hull of the mapped vertices. -/
theorem image_triangle (T : Triangle) :
    planeToEuc '' T.set
      = convexHull ℝ ({planeToEuc T.A, planeToEuc T.B, planeToEuc T.C} :
        Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [set_eq_convexHull, ← LinearEquiv.coe_coe,
    planeToEuc.toLinearMap.image_convexHull]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, (rfl | rfl | rfl), rfl⟩
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
  · rintro (rfl | rfl | rfl)
    exacts [⟨T.A, Or.inl rfl, rfl⟩, ⟨T.B, Or.inr (Or.inl rfl), rfl⟩,
      ⟨T.C, Or.inr (Or.inr rfl), rfl⟩]

theorem range_fin_three {α : Type*} (f : Fin 3 → α) :
    Set.range f = {f 0, f 1, f 2} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩; fin_cases i
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
  · rintro (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-- **The seam**: the elementary vertex-shadow width equals the
`sSup − sInf` width of the hull in the Euclidean plane. -/
theorem width_eq_widthAlong (T : Triangle) (u : ℝ × ℝ) :
    Bang.widthAlong
      (convexHull ℝ ({planeToEuc T.A, planeToEuc T.B, planeToEuc T.C} :
        Set (EuclideanSpace ℝ (Fin 2))))
      (planeToEuc u) = T.width u := by
  have hcomm : ∀ v : ℝ × ℝ,
      inner ℝ (planeToEuc v) (planeToEuc u) = dot u v := by
    intro v; rw [inner_planeToEuc]; exact dot_comm v u
  rw [Bang.widthAlong, sSup_inner_hull, sInf_inner_hull, hcomm, hcomm, hcomm]
  rfl


/-! ### The two named statements are one -/

theorem threePlanks_iff_simplexFor :
    ThreePlanksOnATriangle ↔ Bang.SimplexFor (EuclideanSpace ℝ (Fin 2)) 2 3 := by
  constructor
  · -- the elementary statement implies the Euclidean simplex statement
    intro hthree s _ u lo hi hu hle hcov
    have hpts : s.points = ![s.points 0, s.points 1, s.points 2] := by
      funext i; fin_cases i <;> rfl
    have hnotcol : ¬ Collinear ℝ ({s.points 0, s.points 1, s.points 2} :
        Set (EuclideanSpace ℝ (Fin 2))) :=
      affineIndependent_iff_not_collinear_set.mp (hpts ▸ s.independent)
    have hrange : Set.range s.points = {s.points 0, s.points 1, s.points 2} :=
      range_fin_three _
    have hnc : ¬ Collinear ℝ ({planeToEuc.symm (s.points 0),
        planeToEuc.symm (s.points 1), planeToEuc.symm (s.points 2)} :
        Set (ℝ × ℝ)) := fun h =>
      hnotcol (collinear_of_linearEquiv planeToEuc.symm h)
    set T : Triangle := ⟨planeToEuc.symm (s.points 0),
      planeToEuc.symm (s.points 1), planeToEuc.symm (s.points 2), hnc⟩ with hT
    have e0 : planeToEuc T.A = s.points 0 := by simp [hT]
    have e1 : planeToEuc T.B = s.points 1 := by simp [hT]
    have e2 : planeToEuc T.C = s.points 2 := by simp [hT]
    have hhull : convexHull ℝ (Set.range s.points) = planeToEuc '' T.set := by
      rw [hrange, image_triangle, e0, e1, e2]
    have hune : ∀ i, planeToEuc.symm (u i) ≠ 0 := fun i h =>
      hu i (by simpa using congrArg planeToEuc h)
    set p : Fin 3 → Plank := fun i =>
      ⟨planeToEuc.symm (u i), lo i, hi i, hune i, hle i⟩ with hp
    have hwidth : ∀ i, Bang.widthAlong (convexHull ℝ (Set.range s.points)) (u i)
        = T.width (p i).u := by
      intro i
      have hw := width_eq_widthAlong T (planeToEuc.symm (u i))
      rw [e0, e1, e2, LinearEquiv.apply_symm_apply, ← hrange] at hw
      exact hw
    have hcov' : ∀ P ∈ T, P ∈ p 0 ∨ P ∈ p 1 ∨ P ∈ p 2 := by
      intro P hP
      have hmem : planeToEuc P ∈ convexHull ℝ (Set.range s.points) := by
        rw [hhull]; exact ⟨P, hP, rfl⟩
      obtain ⟨t, ⟨i, rfl⟩, hti⟩ := hcov hmem
      have hd : inner ℝ (planeToEuc P) (u i) = dot (planeToEuc.symm (u i)) P := by
        rw [show u i = planeToEuc (planeToEuc.symm (u i)) by simp, inner_planeToEuc]
        exact dot_comm P (planeToEuc.symm (u i))
      simp only [Set.mem_ofPred_eq, hd] at hti
      have hmp : P ∈ p i := ⟨hti.1, hti.2⟩
      fin_cases i
      exacts [Or.inl hmp, Or.inr (Or.inl hmp), Or.inr (Or.inr hmp)]
    have hmain := hthree T (p 0) (p 1) (p 2) hcov'
    simp only [Fin.sum_univ_three, hwidth]
    simpa [Plank.relWidth, hp] using hmain
  · -- and conversely
    intro hsimplex T p₁ p₂ p₃ hcov
    set q : Fin 3 → Plank := ![p₁, p₂, p₃] with hq
    set pts : Fin 3 → EuclideanSpace ℝ (Fin 2) :=
      ![planeToEuc T.A, planeToEuc T.B, planeToEuc T.C] with hpts
    have hind : AffineIndependent ℝ pts :=
      affineIndependent_iff_not_collinear_set.mpr
        (by simpa [hpts] using not_collinear_planeToEuc T)
    set s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨pts, hind⟩ with hs
    have hrange : Set.range s.points
        = {planeToEuc T.A, planeToEuc T.B, planeToEuc T.C} := by
      rw [show s.points = pts from rfl, range_fin_three]
      simp [hpts]
    have hhull : convexHull ℝ (Set.range s.points) = planeToEuc '' T.set := by
      rw [hrange, image_triangle]
    have hint : (interior (convexHull ℝ (Set.range s.points))).Nonempty := by
      rw [Convex.interior_nonempty_iff_affineSpan_eq_top (convex_convexHull ℝ _),
        affineSpan_convexHull, show Set.range s.points = Set.range pts from rfl,
        hind.affineSpan_eq_top_iff_card_eq_finrank_add_one]
      simp
    have hune0 : ∀ i : Fin 3, planeToEuc (q i).u ≠ 0 := by
      intro i h
      exact (q i).u_ne_zero (by simpa using congrArg planeToEuc.symm h)
    set u : Fin 3 → EuclideanSpace ℝ (Fin 2) := fun i => planeToEuc (q i).u with hu
    set lo : Fin 3 → ℝ := fun i => (q i).lo with hlo
    set hiv : Fin 3 → ℝ := fun i => (q i).hi with hhi
    have hune : ∀ i, u i ≠ 0 := hune0
    have hlei : ∀ i, lo i ≤ hiv i := fun i => (q i).lo_le_hi
    have hd : ∀ (i : Fin 3) (P : ℝ × ℝ),
        inner ℝ (planeToEuc P) (u i) = dot (q i).u P := by
      intro i P
      rw [hu, inner_planeToEuc]
      exact dot_comm P (q i).u
    have hcov' : convexHull ℝ (Set.range s.points)
        ⊆ ⋃ i, {x | lo i ≤ inner ℝ x (u i) ∧ inner ℝ x (u i) ≤ hiv i} := by
      rw [hhull]
      rintro _ ⟨P, hP, rfl⟩
      rcases hcov P hP with h | h | h
      · exact Set.mem_iUnion.mpr ⟨0, by simp only [Set.mem_ofPred_eq, hd]; exact h⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simp only [Set.mem_ofPred_eq, hd]; exact h⟩
      · exact Set.mem_iUnion.mpr ⟨2, by simp only [Set.mem_ofPred_eq, hd]; exact h⟩
    have hwidth : ∀ i, Bang.widthAlong (convexHull ℝ (Set.range s.points)) (u i)
        = T.width (q i).u := by
      intro i
      rw [hrange, hu]
      exact width_eq_widthAlong T (q i).u
    have hmain := hsimplex s hint u lo hiv hune hlei hcov'
    simp only [Fin.sum_univ_three, hwidth] at hmain
    simpa [Plank.relWidth, hq, hlo, hhi] using hmain

end Proofs.Transport

end
