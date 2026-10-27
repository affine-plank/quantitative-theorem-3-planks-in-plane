/- Longest-chord attainment and Bang's chord-length theorem for unit normals.
Independent of the unfinished research scaffold with its normalization defect. -/
module

public import Plank.Convex.BangChord

@[expose] public section
noncomputable section
open scoped RealInnerProductSpace

namespace Plank.Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def chordParameter (K : Set E) (u : E) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ ∃ x ∈ K, ∃ y ∈ K, x - y = t • u}

/-- A compact nonempty body attains its longest chord in a unit direction.
No finite-dimensional assumption is needed once compactness is given. -/
theorem longest_chord_attained (K : Set E) (hc : IsCompact K) (hne : K.Nonempty)
    (u : E) (hu : ‖u‖ = 1) :
    0 ≤ chordParameter K u ∧
      ∃ x ∈ K, ∃ y ∈ K, x - y = chordParameter K u • u := by
  let g : E × E → ℝ := fun p => ⟪p.1 - p.2, u⟫
  let D : Set (E × E) := (K ×ˢ K) ∩ {p | p.1 - p.2 = g p • u ∧ 0 ≤ g p}
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hclosed : IsClosed {p : E × E | p.1 - p.2 = g p • u ∧ 0 ≤ g p} :=
    (isClosed_eq (continuous_fst.sub continuous_snd) (hg.smul continuous_const)).inter
      (isClosed_le continuous_const hg)
  have hD : IsCompact D := (hc.prod hc).inter_right hclosed
  obtain ⟨z, hz⟩ := hne
  have hDne : D.Nonempty := ⟨(z,z), ⟨⟨hz,hz⟩, by simp [g]⟩⟩
  obtain ⟨p, hp, hmax⟩ := hD.exists_isMaxOn hDne hg.continuousOn
  let T := {t : ℝ | 0 ≤ t ∧ ∃ x ∈ K, ∃ y ∈ K, x - y = t • u}
  have hgp : g p ∈ T := ⟨hp.2.2, p.1, hp.1.1, p.2, hp.1.2, hp.2.1⟩
  have hub : ∀ t ∈ T, t ≤ g p := by
    rintro t ⟨ht, x, hx, y, hy, hxy⟩
    have hgxy : g (x,y) = t := by
      dsimp [g]
      rw [hxy, real_inner_smul_left, real_inner_self_eq_norm_sq, hu]
      ring
    have hxyD : (x,y) ∈ D := by
      refine ⟨⟨hx,hy⟩, ?_⟩
      change x-y = g (x,y) • u ∧ 0 ≤ g (x,y)
      rw [hgxy]
      exact ⟨hxy, ht⟩
    simpa only [hgxy] using isMaxOn_iff.mp hmax (x,y) hxyD
  have heq : chordParameter K u = g p :=
    le_antisymm (csSup_le ⟨g p, hgp⟩ hub) (le_csSup ⟨g p, hub⟩ hgp)
  rw [heq]
  exact hgp

/-- Interior nonemptiness gives a positive longest chord in every unit direction. -/
theorem chordParameter_pos (K : Set E) (hc : IsCompact K)
    (hint : (interior K).Nonempty) (u : E) (hu : ‖u‖ = 1) :
    0 < chordParameter K u := by
  obtain ⟨z, hz⟩ := hint
  obtain ⟨ε, he, hb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  have hzK : z ∈ K := interior_subset hz
  have hp : z + (ε/2) • u ∈ K := by
    apply hb
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
      Real.norm_of_nonneg (by positivity : 0 ≤ ε/2)]
    linarith
  have hbdd : BddAbove {t : ℝ | 0 ≤ t ∧ ∃ x ∈ K, ∃ y ∈ K, x-y=t • u} := by
    obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : E)
    refine ⟨2*R, ?_⟩
    rintro t ⟨ht, a, ha, b, hb, hab⟩
    have haR := hR ha
    have hbR := hR hb
    rw [Metric.mem_closedBall, dist_zero_right] at haR hbR
    have hnorm := norm_sub_le a b
    rw [hab, norm_smul, hu, mul_one, Real.norm_of_nonneg ht] at hnorm
    linarith
  have hmem : ε/2 ∈ {t : ℝ | 0 ≤ t ∧ ∃ x ∈ K, ∃ y ∈ K, x-y=t • u} :=
    ⟨by positivity, z+(ε/2) • u, hp, z, hzK, by simp⟩
  have hle : ε/2 ≤ chordParameter K u := le_csSup hbdd hmem
  linarith

/-- Bang's chord bound, with full plank widths and unit normals. -/
theorem sum_ge_one_of_longest_chord_cover
    {n : ℕ} (hn : 0 < n) (K : Set E) (hc : IsCompact K)
    (hK : Convex ℝ K) (hint : (interior K).Nonempty)
    (u : Fin n → E) (hu : ∀ i, ‖u i‖ = 1)
    (lo hi : Fin n → ℝ) (hle : ∀ i, lo i ≤ hi i)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ ⟪z, u i⟫ ∧ ⟪z, u i⟫ ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / chordParameter K (u i) := by
  classical
  have hne : K.Nonempty := hint.mono interior_subset
  have hpos (i : Fin n) := chordParameter_pos K hc hint (u i) (hu i)
  choose x hx y hy hxy using fun i =>
    (longest_chord_attained K hc hne (u i) (hu i)).2
  let c : Fin n → E := fun i => (1/2 : ℝ) • (x i + y i)
  let r : Fin n → ℝ := fun i => chordParameter K (u i) / 2
  have hr (i : Fin n) : 0 < r i := div_pos (hpos i) (by norm_num)
  have hends (i : Fin n) : c i - r i • u i ∈ K ∧ c i + r i • u i ∈ K := by
    have hs : r i • u i = (1/2 : ℝ) • (x i-y i) := by
      rw [hxy i, smul_smul]
      congr 1
      dsimp [r]
      ring
    have hm : c i - r i • u i = y i := by rw [hs]; dsimp [c]; module
    have hp : c i + r i • u i = x i := by rw [hs]; dsimp [c]; module
    exact ⟨hm ▸ hy i, hp ▸ hx i⟩
  have hbound := sum_ge_one_of_realized_chord_cover hn K hK c u r hr hu hends
    (fun i => (lo i+hi i)/2) (fun i => (hi i-lo i)/2)
    (fun i => div_nonneg (sub_nonneg.mpr (hle i)) (by norm_num)) (by
      intro z hz
      obtain ⟨i, hl, hh⟩ := hcover z hz
      exact ⟨i, abs_le.mpr ⟨by linarith only [hl], by linarith only [hh]⟩⟩)
  have heq (i : Fin n) : ((hi i-lo i)/2) / r i =
      (hi i-lo i) / chordParameter K (u i) := by
    dsimp [r]
    field_simp
  simpa only [heq] using hbound

/-- info: 'Plank.Convex.longest_chord_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms longest_chord_attained

/-- info: 'Plank.Convex.sum_ge_one_of_longest_chord_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_ge_one_of_longest_chord_cover

end Plank.Convex
