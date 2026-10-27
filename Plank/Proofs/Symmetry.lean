module
/-
# Proofs/Symmetry — the analytic content behind the moves

Mirror of `Plank/Symmetry.lean`.

ARCHITECTURE NOTE (P1).  `Plank/Symmetry.lean` *introduces* `Move`, the
sector predicates and the chamber predicates, and guard G2 forbids this
mirror from importing its own topic file — so the mirror cannot mention
those names.  It therefore carries every statement in raw form: the two
plane symmetries as explicit maps (`rotMap`, `swapMap`, definitionally
equal to `rotStd`/`swapStd`), the trichotomy with the sector predicates
unfolded, and the transport lemmas over bare `Config`s.  The topic file
does the six-case `Move` induction, each case one line into this file.

§1 the two plane symmetries and their measure invariance;
§2 transport of covering / uncovered set along a chart;
§3 the width of the standard triangle under the symmetries;
§4 the sector trichotomy, unfolded.
-/
public import Plank.Proofs.Transport
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section


public section

noncomputable section

open Proofs.Basic Proofs.Transport MeasureTheory

namespace Proofs.Symmetry

/-! ## §0  Coordinates -/

theorem smul_pair (c a b : ℝ) : c • ((a : ℝ), b) = (c * a, c * b) := rfl

/-! ## §1  The two plane symmetries of the standard triangle

`rotMap` and `swapMap` are the bodies of `rotStd` and `swapStd`; the
topic file's definitions are definitionally these. -/

/-- The vertex 3-cycle `A ↦ B ↦ C ↦ A`, as a map of the plane. -/
@[expose] def rotMap (P : ℝ × ℝ) : ℝ × ℝ := (1 - P.1 - P.2, P.1)

/-- The vertex transposition `B ↔ C`. -/
@[expose] def swapMap (P : ℝ × ℝ) : ℝ × ℝ := (P.2, P.1)

theorem rotMap_mem {P : ℝ × ℝ} (hP : P ∈ stdTriangle) :
    rotMap P ∈ stdTriangle := by
  obtain ⟨h1, h2, h3⟩ := (stdTriangle_mem_iff P).mp hP
  refine (stdTriangle_mem_iff _).mpr ⟨?_, ?_, ?_⟩ <;> simp only [rotMap] <;> linarith

theorem rotMap_surj {Q : ℝ × ℝ} (hQ : Q ∈ stdTriangle) :
    ∃ P ∈ stdTriangle, rotMap P = Q := by
  obtain ⟨h1, h2, h3⟩ := (stdTriangle_mem_iff Q).mp hQ
  refine ⟨(Q.2, 1 - Q.1 - Q.2), (stdTriangle_mem_iff _).mpr ⟨h2, by simp; linarith,
    by simp; linarith⟩, ?_⟩
  refine Prod.ext ?_ ?_ <;> simp [rotMap] <;> ring

theorem swapMap_mem {P : ℝ × ℝ} (hP : P ∈ stdTriangle) :
    swapMap P ∈ stdTriangle := by
  obtain ⟨h1, h2, h3⟩ := (stdTriangle_mem_iff P).mp hP
  exact (stdTriangle_mem_iff _).mpr ⟨h2, h1, by simp only [swapMap]; linarith⟩

theorem swapMap_involutive (P : ℝ × ℝ) : swapMap (swapMap P) = P := rfl

theorem rotMap_mem_iff (P : ℝ × ℝ) : P ∈ stdTriangle ↔ rotMap P ∈ stdTriangle := by
  refine ⟨fun h => rotMap_mem h, fun h => ?_⟩
  obtain ⟨h1, h2, h3⟩ := (stdTriangle_mem_iff _).mp h
  simp only [rotMap] at h1 h2 h3
  exact (stdTriangle_mem_iff P).mpr ⟨h2, by linarith, by linarith⟩

theorem swapMap_mem_iff (P : ℝ × ℝ) : P ∈ stdTriangle ↔ swapMap P ∈ stdTriangle :=
  ⟨fun h => swapMap_mem h, fun h => by
    have h2 := swapMap_mem h
    rwa [swapMap_involutive] at h2⟩

/-- The linear part of `rotMap`. -/
def rotLin : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun P := (-P.1 - P.2, P.1)
  map_add' := by intro x y; simp [Prod.ext_iff]; ring
  map_smul' := by intro c x; simp [Prod.ext_iff]; ring

/-- The linear part of `swapMap`. -/
def swapLin : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun P := (P.2, P.1)
  map_add' := by intro x y; simp
  map_smul' := by intro c x; simp

theorem rotLin_det : LinearMap.det rotLin = 1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, rotLin]

theorem swapLin_det : LinearMap.det swapLin = -1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, swapLin]

/-- Lebesgue area on the plane is an additive Haar measure.  Mathlib has
the instance for `volume.prod volume`; on `ℝ × ℝ` that is the same
measure but instance search does not unfold `Prod.instMeasureSpace`. -/
instance volume_isAddHaar : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℝ × ℝ)).IsAddHaarMeasure)

/-- Both symmetries have determinant `±1`, so Lebesgue area survives
taking preimages along them. -/
theorem volume_preimage_rotMap (S : Set (ℝ × ℝ)) :
    volume (rotMap ⁻¹' S) = volume S := by
  have hpre : rotMap ⁻¹' S
      = rotLin ⁻¹' ((fun x => ((1 : ℝ), (0 : ℝ)) + x) ⁻¹' S) := by
    ext P
    simp only [Set.mem_preimage, rotMap, rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    congr! 1
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  rw [hpre, Measure.addHaar_preimage_linearMap volume (by rw [rotLin_det]; norm_num),
    measure_preimage_add, rotLin_det]
  norm_num

theorem volume_preimage_swapMap (S : Set (ℝ × ℝ)) :
    volume (swapMap ⁻¹' S) = volume S := by
  have hpre : swapMap ⁻¹' S = swapLin ⁻¹' S := rfl
  rw [hpre, Measure.addHaar_preimage_linearMap volume (by rw [swapLin_det]; norm_num),
    swapLin_det]
  norm_num

/-! ## §2  Transport along a re-presentation or a chart -/

/-- Configurations whose planks are equal as sets have the same gap. -/
theorem uncovered_congr {C C' : Config}
    (h : ∀ j, (C'.plank j).set = (C.plank j).set) :
    C'.uncovered = C.uncovered := by
  simp only [Config.uncovered]
  congr 1
  exact Set.iUnion_congr h

/-- …and the same covering property. -/
theorem covers_congr {C C' : Config}
    (h : ∀ j P, P ∈ C'.plank j ↔ P ∈ C.plank j) : C.Covers ↔ C'.Covers := by
  constructor
  · intro hc P hP
    obtain ⟨j, hj⟩ := hc P hP
    exact ⟨j, (h j P).mpr hj⟩
  · intro hc P hP
    obtain ⟨j, hj⟩ := hc P hP
    exact ⟨j, (h j P).mp hj⟩

/-- A covering transported along a self-bijection of the standard
triangle. -/
theorem covers_chart {C C' : Config} (φ : (ℝ × ℝ) → (ℝ × ℝ))
    (hmem : ∀ P ∈ stdTriangle, φ P ∈ stdTriangle)
    (hsurj : ∀ Q ∈ stdTriangle, ∃ P ∈ stdTriangle, φ P = Q)
    (h : ∀ j P, P ∈ C'.plank j ↔ φ P ∈ C.plank j) :
    C.Covers ↔ C'.Covers := by
  constructor
  · intro hc P hP
    obtain ⟨j, hj⟩ := hc (φ P) (hmem P hP)
    exact ⟨j, (h j P).mpr hj⟩
  · intro hc Q hQ
    obtain ⟨P, hP, rfl⟩ := hsurj Q hQ
    obtain ⟨j, hj⟩ := hc P hP
    exact ⟨j, (h j P).mp hj⟩

/-- …and the gap set is then the preimage of the gap set. -/
theorem uncovered_chart {C C' : Config} (φ : (ℝ × ℝ) → (ℝ × ℝ))
    (hstd : ∀ P, P ∈ stdTriangle ↔ φ P ∈ stdTriangle)
    (h : ∀ j P, P ∈ C'.plank j ↔ φ P ∈ C.plank j) :
    C'.uncovered = φ ⁻¹' C.uncovered := by
  ext P
  simp only [Config.uncovered, Set.mem_diff, Set.mem_iUnion, Set.mem_preimage,
    Plank.set, Triangle.set, Set.mem_setOf_eq, not_exists]
  constructor
  · rintro ⟨hP, hn⟩
    exact ⟨(hstd P).mp hP, fun j hj => hn j ((h j P).mpr hj)⟩
  · rintro ⟨hP, hn⟩
    exact ⟨(hstd P).mpr hP, fun j hj => hn j ((h j P).mp hj)⟩

/-- The gap area is invariant along a measure-preserving chart. -/
theorem volume_uncovered_chart {C C' : Config} (φ : (ℝ × ℝ) → (ℝ × ℝ))
    (hstd : ∀ P, P ∈ stdTriangle ↔ φ P ∈ stdTriangle)
    (hvol : ∀ S : Set (ℝ × ℝ), volume (φ ⁻¹' S) = volume S)
    (h : ∀ j P, P ∈ C'.plank j ↔ φ P ∈ C.plank j) :
    volume C'.uncovered = volume C.uncovered := by
  rw [uncovered_chart φ hstd h, hvol]

/-- Three values determine a function on `Fin 3`. -/
theorem forall_fin_three {p : Fin 3 → Prop} (h0 : p 0) (h1 : p 1) (h2 : p 2) :
    ∀ i, p i := by
  intro i; fin_cases i
  exacts [h0, h1, h2]

/-- Three distinct indices give an injective `Fin 3` self-map. -/
theorem inj_three {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Injective (![i, j, k] : Fin 3 → Fin 3) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all

/-! ## §3  The standard triangle's width under the two symmetries -/

theorem width_rot (u : ℝ × ℝ) :
    stdTriangle.width ((u.2 - u.1, -u.1) : ℝ × ℝ) = stdTriangle.width u := by
  rw [stdTriangle_width_eq, stdTriangle_width_eq]
  have hs := spread_shift u.1 u.2 0
  simp only [zero_sub] at hs
  rw [show ((u.2 - u.1, -u.1) : ℝ × ℝ).1 = u.2 - u.1 from rfl,
    show ((u.2 - u.1, -u.1) : ℝ × ℝ).2 = -u.1 from rfl, hs]
  simp [max_comm, max_assoc, max_left_comm, min_comm, min_assoc, min_left_comm]

theorem width_swap (u : ℝ × ℝ) :
    stdTriangle.width ((u.2, u.1) : ℝ × ℝ) = stdTriangle.width u := by
  rw [stdTriangle_width_eq, stdTriangle_width_eq,
    show ((u.2, u.1) : ℝ × ℝ).1 = u.2 from rfl,
    show ((u.2, u.1) : ℝ × ℝ).2 = u.1 from rfl, max_comm u.2 u.1, min_comm u.2 u.1]

/-! ## §4  The sector trichotomy, with the predicates unfolded

The statement is `Plank/Symmetry.lean`'s `sector_trichotomy` with
`SectorAB`, `SectorAC`, `SectorBC`, `SectorBoundary` replaced by their
definitions; the topic file's theorem is this one, verbatim. -/

theorem sector_trichotomy_raw {u : ℝ × ℝ} (hu : u ≠ 0) :
    (∃ c b : ℝ, 0 < c ∧ 0 < b ∧ b < 1 ∧
        (u = c • ((1 : ℝ), b) ∨ u = -(c • ((1 : ℝ), b)))) ∨
    (∃ c a : ℝ, 0 < c ∧ 0 < a ∧ a < 1 ∧
        (u = c • (a, (1 : ℝ)) ∨ u = -(c • (a, (1 : ℝ))))) ∨
    (∃ c a : ℝ, 0 < c ∧ 0 < a ∧ a < 1 ∧
        (u = c • (a, a - 1) ∨ u = -(c • (a, a - 1)))) ∨
    (∃ c : ℝ, c ≠ 0 ∧ (u = c • ((1 : ℝ), (0 : ℝ)) ∨ u = c • ((0 : ℝ), (1 : ℝ)) ∨
        u = c • ((1 : ℝ), (1 : ℝ)))) := by
  have mk_eq : ∀ p q r s : ℝ, p = r → q = s → ((p, q) : ℝ × ℝ) = (r, s) := by
    intro p q r s h1 h2; rw [h1, h2]
  have mk_neg : ∀ p q r s : ℝ, p = -r → q = -s →
      ((p, q) : ℝ × ℝ) = -((r, s) : ℝ × ℝ) := by
    intro p q r s h1 h2; rw [h1, h2]; rfl
  obtain ⟨x, y⟩ := u
  have hxy : x ≠ 0 ∨ y ≠ 0 := ne_zero_iff.mp hu
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by tauto
    exact Or.inr (Or.inr (Or.inr ⟨x, hx, Or.inl (by simp [smul_pair, hy])⟩))
  by_cases hx : x = 0
  · exact Or.inr (Or.inr (Or.inr ⟨y, hy, Or.inr (Or.inl (by simp [smul_pair, hx]))⟩))
  by_cases hxy' : x = y
  · exact Or.inr (Or.inr (Or.inr ⟨x, hx, Or.inr (Or.inr (by simp [smul_pair, hxy']))⟩))
  rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
  · rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
    · rcases lt_trichotomy x y with hlt | hlt | hlt
      · -- x < y < 0 : sector AB, negated branch
        refine Or.inl ⟨-x, y / x, by linarith, div_pos_of_neg_of_neg hy0 hx0, ?_,
          Or.inr ?_⟩
        · rw [div_lt_iff_of_neg hx0]; linarith
        · rw [smul_pair]
          exact mk_neg _ _ _ _ (by ring) (by field_simp)
      · exact absurd hlt hxy'
      · -- y < x < 0 : sector AC, negated branch
        refine Or.inr (Or.inl ⟨-y, x / y, by linarith, div_pos_of_neg_of_neg hx0 hy0,
          ?_, Or.inr ?_⟩)
        · rw [div_lt_iff_of_neg hy0]; linarith
        · rw [smul_pair]
          exact mk_neg _ _ _ _ (by field_simp) (by ring)
    · exact absurd hy0 hy
    · -- x < 0 < y : sector BC, negated branch
      have hne : y - x ≠ 0 := ne_of_gt (by linarith)
      refine Or.inr (Or.inr (Or.inl ⟨y - x, -x / (y - x), by linarith,
        div_pos (by linarith) (by linarith), ?_, Or.inr ?_⟩))
      · rw [div_lt_one (by linarith)]; linarith
      · rw [smul_pair]
        exact mk_neg _ _ _ _ (by field_simp) (by field_simp; ring)
  · exact absurd hx0 hx
  · rcases lt_trichotomy y 0 with hy0 | hy0 | hy0
    · -- 0 < x, y < 0 : sector BC
      have hne : x - y ≠ 0 := ne_of_gt (by linarith)
      refine Or.inr (Or.inr (Or.inl ⟨x - y, x / (x - y), by linarith,
        div_pos hx0 (by linarith), ?_, Or.inl ?_⟩))
      · rw [div_lt_one (by linarith)]; linarith
      · rw [smul_pair]
        exact mk_eq _ _ _ _ (by field_simp) (by field_simp; ring)
    · exact absurd hy0 hy
    · rcases lt_trichotomy y x with hlt | hlt | hlt
      · -- 0 < y < x : sector AB
        refine Or.inl ⟨x, y / x, hx0, div_pos hy0 hx0, ?_, Or.inl ?_⟩
        · rw [div_lt_one hx0]; exact hlt
        · rw [smul_pair]
          exact mk_eq _ _ _ _ (by ring) (by field_simp)
      · exact absurd hlt.symm hxy'
      · -- 0 < x < y : sector AC
        refine Or.inr (Or.inl ⟨y, x / y, hy0, div_pos hx0 hy0, ?_, Or.inl ?_⟩)
        · rw [div_lt_one hy0]; exact hlt
        · rw [smul_pair]
          exact mk_eq _ _ _ _ (by field_simp) (by ring)

end Proofs.Symmetry

end
