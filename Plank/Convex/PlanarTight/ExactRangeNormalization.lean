/- Exact affine range normalization, retaining every original endpoint. -/
module
public import Plank.Convex.AffineRangeWidth
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.ExactRangeNormalization

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

abbrev Point := Fin 3 → ℝ

def forms (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : Point) : Fin 3 → E →ᵃ[ℝ] ℝ :=
  fun i => (W i)⁻¹ • (f i - AffineMap.const ℝ E (m i))

def chart (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : Point) : E →ᵃ[ℝ] Point :=
  AffineMap.pi (forms f m W)

def endpoint (m W t : Point) : Point := fun i => (t i - m i) / W i

theorem forms_apply (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : Point) (x : E) (i : Fin 3) :
    forms f m W i x = (f i x - m i) / W i := by
  change (W i)⁻¹ * (f i x - m i) = (f i x - m i) / W i
  rw [div_eq_mul_inv, mul_comm]

theorem window_iff (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W lo hi : Point)
    (hW : ∀ i, 0 < W i) (x : E) (i : Fin 3) :
    (endpoint m W lo i ≤ forms f m W i x ∧ forms f m W i x ≤ endpoint m W hi i) ↔
      (lo i ≤ f i x ∧ f i x ≤ hi i) := by
  simp only [endpoint, forms_apply, div_le_div_iff_of_pos_right (hW i), sub_le_sub_iff_right]

theorem ordered (m W lo hi : Point) (hW : ∀ i, 0 < W i) (horder : ∀ i, lo i ≤ hi i) :
    ∀ i, endpoint m W lo i ≤ endpoint m W hi i := by
  intro i
  exact (div_le_div_iff_of_pos_right (hW i)).mpr (sub_le_sub_right (horder i) _)

theorem width_eq (m W lo hi : Point) (i : Fin 3) :
    endpoint m W hi i - endpoint m W lo i = (hi i - lo i) / W i := by
  dsimp [endpoint]
  ring

theorem sum_width_eq (m W lo hi : Point) :
    (∑ i, (endpoint m W hi i - endpoint m W lo i)) = ∑ i, (hi i - lo i) / W i := by
  simp only [width_eq]

theorem cover_iff (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W lo hi : Point)
    (hW : ∀ i, 0 < W i) :
    (∀ z ∈ chart f m W '' K, ∃ i, endpoint m W lo i ≤ z i ∧ z i ≤ endpoint m W hi i) ↔
      (∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) := by
  constructor
  · intro h x hx
    obtain ⟨i, hi⟩ := h (chart f m W x) ⟨x, hx, rfl⟩
    exact ⟨i, (window_iff f m W lo _ hW x i).mp hi⟩
  · rintro h _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := h x hx
    exact ⟨i, (window_iff f m W lo _ hW x i).mpr hi⟩

theorem box (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : Point) (hW : ∀ i, 0 < W i)
    (hb : ∀ x ∈ K, ∀ i, m i ≤ f i x ∧ f i x ≤ m i + W i) :
    ∀ z ∈ chart f m W '' K, ∀ i, 0 ≤ z i ∧ z i ≤ 1 := by
  rintro _ ⟨x, hx, rfl⟩ i
  change 0 ≤ forms f m W i x ∧ forms f m W i x ≤ 1
  rw [forms_apply]
  exact ⟨div_nonneg (sub_nonneg.mpr (hb x hx i).1) (hW i).le,
    (div_le_one (hW i)).mpr (by linarith only [(hb x hx i).2])⟩

theorem zero_contacts (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : Point)
    (hL : ∀ i, ∃ x ∈ K, f i x = m i) :
    ∀ i, ∃ z ∈ chart f m W '' K, z i = 0 := by
  intro i
  obtain ⟨x, hx, he⟩ := hL i
  refine ⟨chart f m W x, ⟨x, hx, rfl⟩, ?_⟩
  change forms f m W i x = 0
  rw [forms_apply, he, sub_self, zero_div]

theorem unit_contacts (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : Point)
    (hW : ∀ i, 0 < W i) (hU : ∀ i, ∃ x ∈ K, f i x = m i + W i) :
    ∀ i, ∃ z ∈ chart f m W '' K, z i = 1 := by
  intro i
  obtain ⟨x, hx, he⟩ := hU i
  refine ⟨chart f m W x, ⟨x, hx, rfl⟩, ?_⟩
  change forms f m W i x = 1
  rw [forms_apply, he, add_sub_cancel_left, div_self (hW i).ne']

theorem plane (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W a : Point) (d : ℝ)
    (hW : ∀ i, W i ≠ 0) (hp : ∀ x ∈ K, ∑ i, a i * f i x = d) :
    ∀ z ∈ chart f m W '' K, ∑ i, (a i * W i) * z i = d - ∑ i, a i * m i := by
  rintro _ ⟨x, hx, rfl⟩
  have he (i : Fin 3) : (a i * W i) * chart f m W x i = a i * f i x - a i * m i := by
    change (a i * W i) * forms f m W i x = _
    rw [forms_apply]
    field_simp [hW i]
  simp only [he, Finset.sum_sub_distrib, hp x hx]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A compact body provides the exact minima, maxima, and ranges required
by the normalization. No covering assumption is used. -/
theorem exists_ranges (K : Set F) (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin 3 → F →ᵃ[ℝ] ℝ) :
    ∃ m : Point,
      (∀ x ∈ K, ∀ i, m i ≤ f i x ∧ f i x ≤ m i + DeficientHeightTilt.rangeWidth K (f i)) ∧
      (∀ i, ∃ x ∈ K, f i x = m i) ∧
      (∀ i, ∃ x ∈ K, f i x = m i + DeficientHeightTilt.rangeWidth K (f i)) := by
  have hmin (i : Fin 3) :=
    (hK.image (f i).continuous_of_finiteDimensional).isLeast_sInf (hne.image (f i))
  have hmax (i : Fin 3) :=
    (hK.image (f i).continuous_of_finiteDimensional).isGreatest_sSup (hne.image (f i))
  refine ⟨fun i => sInf (f i '' K), ?_, ?_, ?_⟩
  · intro x hx i
    simpa only [DeficientHeightTilt.rangeWidth, Body.width, add_sub_cancel] using
      And.intro ((hmin i).2 (Set.mem_image_of_mem (f i) hx))
        ((hmax i).2 (Set.mem_image_of_mem (f i) hx))
  · exact fun i => (hmin i).1
  · simp only [DeficientHeightTilt.rangeWidth, Body.width, add_sub_cancel]
    exact fun i => (hmax i).1

end Plank.Convex.PlanarTight.ExactRangeNormalization

/-- info: 'Plank.Convex.PlanarTight.ExactRangeNormalization.cover_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ExactRangeNormalization.cover_iff

/-- info: 'Plank.Convex.PlanarTight.ExactRangeNormalization.sum_width_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ExactRangeNormalization.sum_width_eq

/-- info: 'Plank.Convex.PlanarTight.ExactRangeNormalization.exists_ranges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ExactRangeNormalization.exists_ranges
