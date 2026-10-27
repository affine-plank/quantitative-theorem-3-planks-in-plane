/- Actual supporting-cut variations at a global quantitative minimum.
The ambient dimension is arbitrary; only the cut's noncoincidence is needed. -/
module
public import NoncoincidentCutDerivatives
public import GlobalPlankBodyEnlargement
public import GlobalSupportingFaceBalance
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalBodyCutVariation

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum
open MovingCutArea
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem compact_window {L : Set (ℝ × E)} (hL : IsCompact L) (a t : ℝ) :
    IsCompact (window L a t) :=
  hL.inter_right (isClosed_Icc.prod isClosed_univ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem convex_window {L : Set (ℝ × E)} (hc : Convex ℝ L) (a t : ℝ) :
    Convex ℝ (window L a t) :=
  hc.inter ((convex_Icc a t).prod convex_univ)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] in
theorem window_mono (L : Set (ℝ × E)) (a : ℝ) {b t : ℝ} (hbt : b≤t) :
    window L a b⊆window L a t := by
  rintro x ⟨hx,⟨hl,hu⟩,_⟩
  exact ⟨hx,⟨hl,hu.trans hbt⟩,mem_univ _⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gap_window (L : Set (ℝ × E)) (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (a t : ℝ) :
    window L a t\covered f lo hi=
      window (NoncoincidentCutDerivatives.residual L Finset.univ f lo hi) a t := by
  ext x
  simp only [window,covered,NoncoincidentCutDerivatives.residual,
    mem_inter_iff,mem_sdiff,mem_iUnion,Finset.mem_univ,exists_const]
  tauto

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] in
theorem fiber_window_upper (L : Set (ℝ × E)) {a b : ℝ} (hab : a≤b) :
    ConvexSections.fiber (window L a b) b=ConvexSections.fiber L b := by
  ext y
  simp [ConvexSections.fiber,window,hab]

/-- Relaxing a real supporting cut forces its uncovered-section fraction to
be at least the body's uncovered-volume fraction. The body is the actual
window in a convex extension, not an independently supplied cap. -/
theorem section_density_ge (ν : Measure E) [ν.IsAddHaarMeasure]
    {L : Set (ℝ × E)} (hL : IsCompact L) (hc : Convex ℝ L)
    (hfull : (interior L).Nonempty) {a b : ℝ} (hab : a<b)
    (hcut : b∈interior (Prod.fst '' L))
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i,lo i≤hi i)
    (hsep : ∀ j, (¬∀ y,f j (b,y)=lo j) ∧ (¬∀ y,f j (b,y)=hi j))
    (hV : 0<(volume.prod ν).real (window L a b))
    (hW : ∀ i,0<Body.width (window L a b) (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget (window L a b) f lo hi≤B)
    (hglobal : IsGlobalMinimum (volume.prod ν) (window L a b) f lo hi d B) :
    (volume.prod ν).real (window L a b\covered f lo hi)/
        (volume.prod ν).real (window L a b)*density ν L b≤
      density ν (NoncoincidentCutDerivatives.residual L Finset.univ f lo hi) b := by
  clear hfull hcut
  have hh := GlobalSupportingFaceBalance.section_ge ν
    (compact_window hL a b) (convex_window hc a b) b (fun p hp => hp.2.1.2)
    f lo hi horder hV hW hsep d hbudget hglobal
  rw [gap_window,fiber_window_upper _ hab.le,fiber_window_upper _ hab.le] at hh
  simpa only [gap_window,density,ConvexSections.fiber] using hh

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The actual section at an interior cut has positive Haar volume, including
the zero-dimensional transverse space. -/
theorem density_pos (ν : Measure E) [ν.IsAddHaarMeasure]
    {L : Set (ℝ × E)} (hL : IsCompact L) (hc : Convex ℝ L)
    (hfull : (interior L).Nonempty) {b : ℝ}
    (hcut : b∈interior (Prod.fst '' L)) : 0<density ν L b := by
  have hp := ConvexSections.image_interior_eq
    (ContinuousLinearMap.fst ℝ ℝ E) isOpenMap_fst hc hfull
  obtain ⟨p,hp,hpb⟩ := hp.symm ▸ hcut
  have hi : (interior (ConvexSections.fiber L b)).Nonempty := by
    rw [ConvexSections.interior_fiber_eq hc hfull hcut]
    refine ⟨p.2,?_⟩
    change (b,p.2)∈interior L
    rw [←hpb]
    exact hp
  exact ENNReal.toReal_pos (ne_of_gt (Measure.measure_pos_of_nonempty_interior ν hi))
    (ConvexSections.compact_fiber hL b).measure_ne_top

/-- A fully covered, noncoincident supporting cut cannot occur at a
positive-gap minimum when the body admits this actual convex extension. -/
theorem not_fully_covered (ν : Measure E) [ν.IsAddHaarMeasure]
    {L : Set (ℝ × E)} (hL : IsCompact L) (hc : Convex ℝ L)
    (hfull : (interior L).Nonempty) {a b : ℝ} (hab : a<b)
    (hcut : b∈interior (Prod.fst '' L))
    (f : ι → (ℝ × E) →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ i,lo i≤hi i)
    (hsep : ∀ j, (¬∀ y,f j (b,y)=lo j) ∧ (¬∀ y,f j (b,y)=hi j))
    (hV : 0<(volume.prod ν).real (window L a b))
    (hW : ∀ i,0<Body.width (window L a b) (f i))
    (d : ℕ) {B : ℝ} (hbudget : budget (window L a b) f lo hi≤B)
    (hglobal : IsGlobalMinimum (volume.prod ν) (window L a b) f lo hi d B)
    (hgap : 0<(volume.prod ν).real (window L a b\covered f lo hi)) :
    ¬∀ y,(b,y)∈L → (b,y)∈covered f lo hi := by
  intro hcover
  have hz : density ν (NoncoincidentCutDerivatives.residual L Finset.univ f lo hi) b=0 := by
    have he : Prod.mk b ⁻¹' NoncoincidentCutDerivatives.residual L Finset.univ f lo hi=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hh : (b,y)∈L\covered f lo hi := by
        simpa only [NoncoincidentCutDerivatives.residual,covered,Finset.mem_univ,
          iUnion_true,mem_preimage] using hy
      exact hh.2 (hcover y hh.1)
    simp [density,he]
  have hh := section_density_ge ν hL hc hfull hab hcut f lo hi horder hsep
    hV hW d hbudget hglobal
  rw [hz] at hh
  exact (not_le_of_gt (mul_pos (div_pos hgap hV) (density_pos ν hL hc hfull hcut))) hh

end Plank.GlobalBodyCutVariation
