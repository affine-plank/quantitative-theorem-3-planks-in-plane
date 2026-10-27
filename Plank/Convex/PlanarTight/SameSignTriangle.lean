/- Balanced same-sign supports with strict upper endpoints force the
original planar convex body itself to be a triangle. -/
module
public import Plank.Convex.PlanarTight.SameSignEquality
public import Plank.Convex.PlanarTight.TriangleSupportShape
public import Plank.Convex.PlanarTight.PlanarCoordinateIndependence
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.SameSignTriangle

open SameSignCapAlgebra SameSignCapTransfer

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Conditional shape classification for the balanced same-sign case.
The triangle vertices are actual coordinate maxima of the original body.
Neither compactness nor movement of the endpoints is used. -/
theorem eq_triangle_of_balanced (hdim : Module.finrank ℝ E = 2)
    (K : Set E) (hK : Convex ℝ K) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ f i x ∧ f i x ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, f i x = 0) (hU : ∀ i, ∃ x ∈ K, f i x = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, A i ≠ 0)
    (hplane : ∀ x, ∑ i, A i * f i x = D)
    (hinj : Function.Injective (fun x => fun i => f i x))
    (lo hi a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hwidth : ∀ i, lo i < hi i) (hhi : ∀ i, hi i < 1)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (hupper : ∀ i, ∀ x ∈ K, f i x + a i * f (next i) x ≤ hi i + a i * hi (next i))
    (hlower : ∀ i, ∀ x ∈ K, lo i + b i * lo (next i) ≤ f i x + b i * f (next i) x)
    (hbalanced : slopeProduct a b = 1) :
    ∃ v : Fin 3 → E, (∀ i, v i ∈ K) ∧ (∀ i, f i (v i) = 1) ∧
      AffineIndependent ℝ v ∧ K = convexHull ℝ (Set.range v) := by
  choose v hv hdiag using hU
  have hupperBound (i : Fin 3) : hi i + a i * hi (next i) < 1 + a i :=
    add_lt_add (hhi i) (by simpa only [mul_one] using mul_lt_mul_of_pos_left (hhi _) (ha i))
  have hnextMax (i : Fin 3) : f i (v (next i)) < 1 := by
    have h := hupper i (v (next i)) (hv _)
    rw [hdiag, mul_one] at h
    have hbound := hupperBound i
    linarith only [h, hbound]
  have hprevMax (i : Fin 3) : f i (v (prev i)) < 1 := by
    have h := hupper (prev i) (v (prev i)) (hv _)
    rw [next_prev, hdiag] at h
    have hbound := hupperBound (prev i)
    rw [next_prev] at hbound
    have hp := ha (prev i)
    nlinarith only [h, hbound, hp]
  have hoffMax (i j : Fin 3) (hji : j ≠ i) : f i (v j) < 1 := by
    rcases index_cases i j with rfl | rfl | rfl
    · exact False.elim (hji rfl)
    · exact hnextMax i
    · exact hprevMax i
  have hind := TriangleSupportShape.independent_of_strict_maxima v f hdiag hoffMax
  let F : E →ᵃ[ℝ] Point := AffineMap.pi f
  let J : Set Point := F '' K
  have hboxJ : ∀ y ∈ J, ∀ i, 0 ≤ y i ∧ y i ≤ 1 := by
    rintro y ⟨x, hx, rfl⟩ i
    exact hbox x hx i
  have hLJ : ∀ i, ∃ y ∈ J, y i = 0 := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hL i
    exact ⟨F x, ⟨x, hx, rfl⟩, hxi⟩
  have hUJ : ∀ i, ∃ y ∈ J, y i = 1 :=
    fun i => ⟨F (v i), ⟨v i, hv i, rfl⟩, hdiag i⟩
  have hupperJ : UpperSupports J hi a := by
    rintro i y ⟨x, hx, rfl⟩
    exact hupper i x hx
  have hlowerJ : LowerSupports J lo b := by
    rintro i y ⟨x, hx, rfl⟩
    exact hlower i x hx
  have hcontacts := SameSignEquality.upper_contacts J hboxJ hLJ hUJ lo hi a b ha hb
    hwidth hsum hupperJ hlowerJ hbalanced
  have hc₀ (i : Fin 3) : f i (v i) + a i * f (next i) (v i) = hi i + a i * hi (next i) :=
    (hcontacts i (F (v i)) ⟨v i, hv i, rfl⟩ (hdiag i)).1
  have hc₁ (i : Fin 3) : f (prev i) (v i) + a (prev i) * f i (v i) =
      hi (prev i) + a (prev i) * hi i :=
    (hcontacts i (F (v i)) ⟨v i, hv i, rfl⟩ (hdiag i)).2.1
  let g : Fin 3 → E →ᵃ[ℝ] ℝ := fun i =>
    AffineMap.const ℝ E (hi (next i) + a (next i) * hi (prev i)) -
      (f (next i) + a (next i) • f (prev i))
  have hg (i : Fin 3) (x : E) : g i x =
      (hi (next i) + a (next i) * hi (prev i)) -
        (f (next i) x + a (next i) * f (prev i) x) := by
    simp [g, AffineMap.coe_sub, AffineMap.coe_add, AffineMap.coe_smul]
  have hside : ∀ x ∈ K, ∀ i, 0 ≤ g i x := by
    intro x hx i
    rw [hg]
    apply sub_nonneg.mpr
    simpa only [next_next] using hupper (next i) x hx
  have hprevprev (i : Fin 3) : prev (prev i) = next i := by fin_cases i <;> rfl
  have hoff : ∀ i j, j ≠ i → g i (v j) = 0 := by
    intro i j hji
    rw [hg]
    apply sub_eq_zero.mpr
    rcases index_cases i j with rfl | rfl | rfl
    · exact False.elim (hji rfl)
    · simpa only [next_next] using (hc₀ (next i)).symm
    · simpa only [hprevprev] using (hc₁ (prev i)).symm
  have hnonzero : ∀ i, ∃ x, g i x ≠ 0 := by
    intro i
    obtain ⟨x, hx⟩ := PlanarCoordinateIndependence.nonzero_pair_cut hdim f A D hA hplane hinj
      (next i) (a (next i)) (hi (next i) + a (next i) * hi (prev i)) (ha _).ne'
    refine ⟨x, ?_⟩
    rw [hg]
    simpa only [next_next] using hx
  exact ⟨v, hv, hdiag, hind,
    TriangleSupportShape.eq_convexHull_of_supports hdim K hK v hv hind g hside hoff hnonzero⟩

end Plank.Convex.PlanarTight.SameSignTriangle

/-- info: 'Plank.Convex.PlanarTight.SameSignTriangle.eq_triangle_of_balanced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.SameSignTriangle.eq_triangle_of_balanced
