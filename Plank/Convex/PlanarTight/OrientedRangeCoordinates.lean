/- Exact range coordinates with all label permutations and independent reflections. -/
module
public import Plank.Convex.PlanarTight.ExactRangeNormalization
public import Plank.Convex.PlanarTight.IndependentReflection
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.OrientedRangeCoordinates

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
abbrev P := Fin 3 → ℝ

def forms (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : P) (σ : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) : Fin 3 → E →ᵃ[ℝ] ℝ :=
  OrientedCommonChord.coordinates flip (fun i => ExactRangeNormalization.forms f m W (σ i))

def lower (m W lo hi : P) (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) : P :=
  OrientedCommonChord.lower flip (fun i => ExactRangeNormalization.endpoint m W lo (σ i))
    (fun i => ExactRangeNormalization.endpoint m W hi (σ i))

def upper (m W lo hi : P) (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) : P :=
  OrientedCommonChord.upper flip (fun i => ExactRangeNormalization.endpoint m W lo (σ i))
    (fun i => ExactRangeNormalization.endpoint m W hi (σ i))

theorem window_iff (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W lo hi : P)
    (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (hW : ∀ i, 0 < W i) (x : E) (i : Fin 3) :
    (lower m W lo hi σ flip i ≤ forms f m W σ flip i x ∧
      forms f m W σ flip i x ≤ upper m W lo hi σ flip i) ↔
      (lo (σ i) ≤ f (σ i) x ∧ f (σ i) x ≤ hi (σ i)) :=
  (OrientedCommonChord.window_iff flip _ _ _ x i).trans
    (ExactRangeNormalization.window_iff f m W lo hi hW x (σ i))

theorem width_eq (m W lo hi : P) (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (i : Fin 3) :
    upper m W lo hi σ flip i - lower m W lo hi σ flip i = (hi (σ i) - lo (σ i)) / W (σ i) := by
  exact (OrientedCommonChord.width_eq flip _ _ i).trans
    (ExactRangeNormalization.width_eq m W lo hi (σ i))

theorem sum_width_eq (m W lo hi : P) (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) :
    (∑ i, (upper m W lo hi σ flip i - lower m W lo hi σ flip i)) =
      ∑ i, (hi i - lo i) / W i := by
  simp only [width_eq]
  exact Equiv.sum_comp σ (fun i => (hi i - lo i) / W i)

theorem positive (m W lo hi : P) (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool)
    (hW : ∀ i, 0 < W i) (hw : ∀ i, lo i < hi i) :
    ∀ i, lower m W lo hi σ flip i < upper m W lo hi σ flip i := by
  intro i
  apply sub_pos.mp
  rw [width_eq]
  exact div_pos (sub_pos.mpr (hw (σ i))) (hW (σ i))

theorem cover_iff (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W lo hi : P)
    (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (hW : ∀ i, 0 < W i) :
    (∀ x ∈ K, ∃ i, lower m W lo hi σ flip i ≤ forms f m W σ flip i x ∧
      forms f m W σ flip i x ≤ upper m W lo hi σ flip i) ↔
      (∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) := by
  constructor
  · intro h x hx
    obtain ⟨i, hi'⟩ := h x hx
    exact ⟨σ i, (window_iff f m W lo hi σ flip hW x i).mp hi'⟩
  · intro h x hx
    obtain ⟨i, hi'⟩ := h x hx
    refine ⟨σ.symm i, (window_iff f m W lo hi σ flip hW x (σ.symm i)).mpr ?_⟩
    simpa using hi'

theorem box (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : P)
    (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (hW : ∀ i, 0 < W i)
    (hb : ∀ x ∈ K, ∀ i, m i ≤ f i x ∧ f i x ≤ m i + W i) :
    ∀ x ∈ K, ∀ i, 0 ≤ forms f m W σ flip i x ∧ forms f m W σ flip i x ≤ 1 := by
  intro x hx i
  apply OrientedCommonChord.box
  exact ExactRangeNormalization.box K f m W hW hb _ ⟨x, hx, rfl⟩ (σ i)

theorem zero_contacts (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : P)
    (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (hW : ∀ i, 0 < W i)
    (hL : ∀ i, ∃ x ∈ K, f i x = m i) (hU : ∀ i, ∃ x ∈ K, f i x = m i + W i) :
    ∀ i, ∃ x ∈ K, forms f m W σ flip i x = 0 := by
  intro i
  cases hf : flip i
  · obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := ExactRangeNormalization.zero_contacts K f m W hL (σ i)
    change ExactRangeNormalization.forms f m W (σ i) x = 0 at he
    exact ⟨x, hx, by simpa [forms, OrientedCommonChord.coordinates, hf] using he⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := ExactRangeNormalization.unit_contacts K f m W hW hU (σ i)
    refine ⟨x, hx, ?_⟩
    change ExactRangeNormalization.forms f m W (σ i) x = 1 at he
    simp [forms, OrientedCommonChord.coordinates, hf, TwoPlankClassification.reflect_apply, he]

theorem unit_contacts (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (m W : P)
    (σ : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (hW : ∀ i, 0 < W i)
    (hL : ∀ i, ∃ x ∈ K, f i x = m i) (hU : ∀ i, ∃ x ∈ K, f i x = m i + W i) :
    ∀ i, ∃ x ∈ K, forms f m W σ flip i x = 1 := by
  intro i
  cases hf : flip i
  · obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := ExactRangeNormalization.unit_contacts K f m W hW hU (σ i)
    change ExactRangeNormalization.forms f m W (σ i) x = 1 at he
    exact ⟨x, hx, by simpa [forms, OrientedCommonChord.coordinates, hf] using he⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := ExactRangeNormalization.zero_contacts K f m W hL (σ i)
    refine ⟨x, hx, ?_⟩
    change ExactRangeNormalization.forms f m W (σ i) x = 0 at he
    simp [forms, OrientedCommonChord.coordinates, hf, TwoPlankClassification.reflect_apply, he]

end Plank.Convex.PlanarTight.OrientedRangeCoordinates

/-- info: 'Plank.Convex.PlanarTight.OrientedRangeCoordinates.cover_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.OrientedRangeCoordinates.cover_iff
