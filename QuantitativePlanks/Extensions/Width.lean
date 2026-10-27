/- Genuine finite or infinite directional spans, with the old finite-width API recovered. -/
module

public import QuantitativePlanks.Extensions.FiniteVolume
public import ResearchFormalized.Metric.ExtendedDiameter

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.ExtendedWidth

open Set MeasureTheory Metric Filter FiniteDimensionalCapWindowScaling
open scoped ENNReal Topology BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Extended directional width: the diameter of the affine image. Empty and
singleton images have width zero; unbounded images have infinite width. -/
def width (K : Set E) (f : E →ᵃ[ℝ] ℝ) : ℝ≥0∞ := ediam (f '' K)

theorem width_mono {K L : Set E} (h : K ⊆ L) (f : E →ᵃ[ℝ] ℝ) :
    width K f ≤ width L f := ediam_mono (image_mono h)

theorem tendsto_width_iUnion (K : ℕ → Set E) (hK : Monotone K) (f : E →ᵃ[ℝ] ℝ) :
    Tendsto (fun n => width (K n) f) atTop (𝓝 (width (⋃ n, K n) f)) := by
  unfold width
  rw [image_iUnion]
  exact ResearchFormalized.ExtendedDiameter.tendsto_ediam_iUnion _
    (fun i j hij => image_mono (hK hij))

theorem width_eq_of_image_bounded {K : Set E} (f : E →ᵃ[ℝ] ℝ)
    (hb : Bornology.IsBounded (f '' K)) : width K f = ENNReal.ofReal (Body.width K f) :=
  Real.ediam_eq hb

theorem width_eq_top_of_image_unbounded {K : Set E} (f : E →ᵃ[ℝ] ℝ)
    (hb : ¬Bornology.IsBounded (f '' K)) : width K f = ∞ :=
  Metric.ediam_of_unbounded hb

section FiniteDimension

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem width_eq_of_isBounded {K : Set F} (hb : Bornology.IsBounded K) (f : F →ᵃ[ℝ] ℝ) :
    width K f = ENNReal.ofReal (Body.width K f) := by
  apply width_eq_of_image_bounded
  exact ((Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure).image
    f.continuous_of_finiteDimensional).isBounded.subset (image_mono subset_closure)

end FiniteDimension

theorem volume_eq_zero_of_width_eq_zero {d : ℕ} {K : Set (Point d)}
    (f : Point d →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0) (hz : width K f = 0) : volume K = 0 := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hsub : K ⊆ {x | f x = f a} := by
      intro x hx
      exact (Metric.ediam_eq_zero_iff.mp hz) ⟨x, hx, rfl⟩ ⟨a, ha, rfl⟩
    exact measure_mono_null hsub (measure_level_zero f hf (f a))
  · simp [not_nonempty_iff_eq_empty.mp hne]

/-- Relative cost with the ordinary nonnegative width of a window. Reversed
endpoints describe an empty window and have cost zero. -/
def budget {m : ℕ} (K : Set E) (f : Fin m → E →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (hi i - lo i) / width K (f i)

theorem budget_eq_of_isBounded {d m : ℕ} {K : Set (Point d)}
    (hb : Bornology.IsBounded K) (f : Fin m → Point d →ᵃ[ℝ] ℝ)
    (lo hi : Fin m → ℝ) (horder : ∀ i, lo i ≤ hi i)
    (hW : ∀ i, 0 < Body.width K (f i)) :
    budget K f lo hi = ENNReal.ofReal (∑ i, (hi i - lo i) / Body.width K (f i)) := by
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => div_nonneg (sub_nonneg.mpr (horder i)) (hW i).le)]
  unfold budget
  apply Finset.sum_congr rfl
  intro i _
  rw [width_eq_of_isBounded hb, ENNReal.ofReal_div_of_pos (hW i)]

theorem tendsto_budget_iUnion {m : ℕ} (K : ℕ → Set E) (hK : Monotone K)
    (f : Fin m → E →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ) :
    Tendsto (fun n => budget (K n) f lo hi) atTop (𝓝 (budget (⋃ n, K n) f lo hi)) := by
  unfold budget
  apply tendsto_finsetSum
  intro i _
  simpa only [div_eq_mul_inv, Function.comp_def] using
    ((ENNReal.continuous_const_mul (a := ENNReal.ofReal (hi i - lo i)) ENNReal.ofReal_ne_top).tendsto _).comp
      (tendsto_width_iUnion K hK (f i)).inv

end Plank.ExtendedWidth
