/- Elementary affine normalization, independently of volume minimization. -/
module

public import Plank.Proofs.AffineWidthCore
public import Plank.Measure.LinearBandsCore
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Choose

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Plank.FiniteDimensionalCapWindowScaling

open Set MeasureTheory

abbrev Point (d : ℕ) := Fin (d+1) → ℝ

variable {d : ℕ}

theorem continuous_form (f : Point d →ᵃ[ℝ] ℝ) : Continuous f :=
  f.continuous_of_finiteDimensional

theorem measure_level_zero (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (c : ℝ) :
    volume {x | f x = c} = 0 := by
  have hne : f.linear.toContinuousLinearMap ≠ 0 := by
    intro h
    apply hf
    simpa using congrArg ContinuousLinearMap.toLinearMap h
  have hset : {x | f x = c} =
      {x | f.linear.toContinuousLinearMap x = c-f 0} := by
    ext x
    have he : f x = f.linear x+f 0 := congrFun f.decomp x
    change f x = c ↔ f.linear x = c-f 0
    rw [he, eq_sub_iff_add_eq]
  rw [hset]
  exact LinearBands.measure_level_zero volume _ hne _

end Plank.FiniteDimensionalCapWindowScaling

namespace Plank.FiniteDimensionalEndpointMajorants

abbrev Endpoints (κ : Type*) := (κ → ℝ) × (κ → ℝ)

end Plank.FiniteDimensionalEndpointMajorants

namespace Plank.FiniteDimensionalFewCellScaling

open Set MeasureTheory FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants

variable {n m : ℕ}

def budget (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m)) : ℝ :=
  ∑ i, (p.2 i-p.1 i)/Body.width K (f i)

def gapVolume (K : Set (Point n)) (f : Fin m → (Point n) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m)) : ℝ :=
  (volume (K \ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i})).toReal

end Plank.FiniteDimensionalFewCellScaling

namespace Plank.FiniteDimensionalNormalization

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling

variable {d : ℕ}

/-- Endpoints in the unit interval determine a canonical centre, independently
of the body and its dimension. The remaining support length must be positive. -/
theorem canonical_window {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ 1)
    (hwidth : hi-lo < 1) :
    let c := lo/(1-(hi-lo))
    c ∈ Icc (0 : ℝ) 1 ∧ (1-(hi-lo))*c=lo ∧ c+(1-c)*(hi-lo)=hi := by
  dsimp only
  have hd := sub_pos.mpr hwidth
  have hl : (1-(hi-lo))*(lo/(1-(hi-lo)))=lo := mul_div_cancel₀ _ hd.ne'
  refine ⟨⟨div_nonneg hlo hd.le, (div_le_one hd).mpr (by linarith only [hhi])⟩,
    hl, ?_⟩
  nlinarith only [hl]

/-- Positive actual width excludes a constant affine form. -/
theorem linear_ne_zero_of_width_pos {K : Set (Point d)} (hne : K.Nonempty)
    (f : (Point d) →ᵃ[ℝ] ℝ) (hwidth : 0 < Body.width K f) : f.linear ≠ 0 := by
  exact Body.linear_ne_zero_of_width_pos hne f hwidth

/-- Unit width and unit-interval bounds give actual zero and one support points. -/
theorem unit_realisers {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (f : (Point d) →ᵃ[ℝ] ℝ) (hnorm : ∀ x ∈ K, 0 ≤ f x ∧ f x ≤ 1)
    (hunit : Body.width K f = 1) :
    (∃ x ∈ K, f x = 0) ∧ (∃ x ∈ K, f x = 1) := by
  obtain ⟨a,ha,b,hb,hmax,hmin⟩ := Body.exists_realisers hK hne (continuous_form f)
  have hspan : f a-f b = 1 :=
    (Body.width_eq_of_realisers ha hb hmax hmin).symm.trans hunit
  have hzero : f b = 0 := by linarith only [hspan,(hnorm a ha).2,(hnorm b hb).1]
  have hone : f a = 1 := by linarith only [hspan,hzero]
  exact ⟨⟨b,hb,hzero⟩,⟨a,ha,hone⟩⟩

/-- Normalize one affine functional using actual support points. Its new
range is exactly one and its values on the body lie in the unit interval. -/
theorem exists_unit_form {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (f : (Point d) →ᵃ[ℝ] ℝ) (hW : 0 < Body.width K f) :
    ∃ (g : (Point d) →ᵃ[ℝ] ℝ) (c : ℝ),
      (∀ x, g x = (f x-c)/Body.width K f) ∧
      (∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1) ∧ Body.width K g = 1 := by
  obtain ⟨a, ha, b, hb, hmax, hmin⟩ := Body.exists_realisers hK hne (continuous_form f)
  have hspan : Body.width K f = f a-f b := Body.width_eq_of_realisers ha hb hmax hmin
  let g : (Point d) →ᵃ[ℝ] ℝ := (Body.width K f)⁻¹ • (f - AffineMap.const ℝ (Point d) (f b))
  have happly (x : (Point d)) : g x = (f x-f b)/Body.width K f := by
    simp [g, div_eq_mul_inv, mul_comm]
  have hbounds : ∀ x ∈ K, 0 ≤ g x ∧ g x ≤ 1 := by
    intro x hx
    rw [happly]
    refine ⟨div_nonneg (sub_nonneg.mpr (hmin x hx)) hW.le, ?_⟩
    apply (div_le_one hW).mpr
    rw [hspan]
    linarith only [hmax x hx]
  have hga : g a = 1 := by rw [happly, ← hspan, div_self hW.ne']
  have hgb : g b = 0 := by rw [happly, sub_self, zero_div]
  have hwidth : Body.width K g = g a-g b :=
    Body.width_eq_of_realisers ha hb
      (fun x hx => by rw [hga]; exact (hbounds x hx).2)
      (fun x hx => by rw [hgb]; exact (hbounds x hx).1)
  refine ⟨g, f b, happly, hbounds, ?_⟩
  rw [hwidth, hga, hgb, sub_zero]

/-- Normalize a finite family once, retaining the exact affine formulas and
each actual plank set. Endpoints may extend outside the support interval. -/
theorem normalize_data_with_formula {m : ℕ} {K : Set (Point d)}
    (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < Body.width K (f i)) :
    ∃ (g : Fin m → (Point d) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m)) (c : Fin m → ℝ),
      (∀ i x, g i x = (f i x-c i)/Body.width K (f i)) ∧
      (∀ i, Body.width K (g i) = 1) ∧
      (∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1) ∧
      (∀ i, p.1 i ≤ p.2 i) ∧ budget K g p = budget K f (lo, hi) ∧
      (∀ i, {x | p.1 i ≤ g i x ∧ g i x ≤ p.2 i} =
        {x | lo i ≤ f i x ∧ f i x ≤ hi i}) ∧
      gapVolume K g p = gapVolume K f (lo, hi) := by
  choose g c happly hbounds hunit using fun i => exists_unit_form hK hne (f i) (hW i)
  let p : Endpoints (Fin m) := (fun i => (lo i-c i)/Body.width K (f i),
    fun i => (hi i-c i)/Body.width K (f i))
  have hordered : ∀ i, p.1 i ≤ p.2 i := by
    intro i
    apply (div_le_div_iff_of_pos_right (hW i)).mpr
    exact sub_le_sub_right (horder i) _
  have hbudget : budget K g p = budget K f (lo, hi) := by
    unfold budget
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit]
    dsimp only [p]
    ring
  have hbands (i) : {x | p.1 i ≤ g i x ∧ g i x ≤ p.2 i} =
      {x | lo i ≤ f i x ∧ f i x ≤ hi i} := by
    ext x
    change (p.1 i ≤ g i x ∧ g i x ≤ p.2 i) ↔ (lo i ≤ f i x ∧ f i x ≤ hi i)
    rw [happly]
    dsimp only [p]
    simp only [div_le_div_iff_of_pos_right (hW i), sub_le_sub_iff_right]
  refine ⟨g, p, c, happly, hunit, hbounds, hordered, hbudget, hbands, ?_⟩
  unfold gapVolume
  rw [iUnion_congr hbands]

/-- Simultaneous normalization preserves the actual plank sets, gap volume
and relative budget. Endpoints may extend outside the new support interval. -/
theorem normalize_data {m : ℕ} {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hW : ∀ i, 0 < Body.width K (f i)) :
    ∃ (g : Fin m → (Point d) →ᵃ[ℝ] ℝ) (p : Endpoints (Fin m)),
      (∀ i, Body.width K (g i) = 1) ∧
      (∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1) ∧
      (∀ i, p.1 i ≤ p.2 i) ∧ budget K g p = budget K f (lo, hi) ∧
      gapVolume K g p = gapVolume K f (lo, hi) := by
  obtain ⟨g, p, _, _, hunit, hbounds, hordered, hbudget, _, hgap⟩ :=
    normalize_data_with_formula hK hne f lo hi horder hW
  exact ⟨g, p, hunit, hbounds, hordered, hbudget, hgap⟩

end Plank.FiniteDimensionalNormalization

#print axioms Plank.FiniteDimensionalCapWindowScaling.continuous_form
#print axioms Plank.FiniteDimensionalCapWindowScaling.measure_level_zero
#print axioms Plank.FiniteDimensionalNormalization.linear_ne_zero_of_width_pos
#print axioms Plank.FiniteDimensionalNormalization.unit_realisers
#print axioms Plank.FiniteDimensionalNormalization.exists_unit_form
#print axioms Plank.FiniteDimensionalNormalization.normalize_data_with_formula
#print axioms Plank.FiniteDimensionalNormalization.normalize_data
