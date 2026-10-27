/- Choose supporting slopes toward one. Ordered tangencies then give the
planar slope inequalities without requiring the pair corners to be attained. -/
module
public import Plank.Convex.PlanarChosenWeights
public import Plank.Convex.PlanarSupportWidth
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
@[expose] public section
set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace Plank.Convex.PlanarChosenSupports

/-- Move a feasible slope at least one down toward one. A slope that stops
above one is supported at a point where the first excess is positive. -/
theorem choose_above {ι : Type*} [Fintype ι] [Nonempty ι]
    (g h : ι → ℝ) (s₀ : ℝ) (hs₀ : 1 ≤ s₀)
    (hsupport : ∀ v, g v + s₀ * h v ≤ 0) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ s₀ ∧ (∀ v, g v + s * h v ≤ 0) ∧
      (1 < s → ∃ v, 0 < g v ∧ g v + s * h v = 0) := by
  classical
  let q : ι → ℝ := fun v => if h v < 0 then g v / (-h v) else 1
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
  let s := max 1 (q v)
  have hq (u : ι) : q u ≤ s₀ := by
    by_cases hu : h u < 0
    · simp only [q, if_pos hu]
      apply (div_le_iff₀ (neg_pos.mpr hu)).mpr
      nlinarith only [hsupport u]
    · simpa [q, hu] using hs₀
  have hss : s ≤ s₀ := max_le hs₀ (hq v)
  have hs : 1 ≤ s := le_max_left _ _
  refine ⟨s, hs, hss, ?_, ?_⟩
  · intro u
    by_cases hu : h u < 0
    · have huq : g u / (-h u) ≤ s := by
        calc g u / (-h u) = q u := by simp [q, hu]
             _ ≤ q v := hv u (Finset.mem_univ _)
             _ ≤ s := le_max_right _ _
      have hm := (div_le_iff₀ (neg_pos.mpr hu)).mp huq
      nlinarith only [hm]
    · have hm := mul_le_mul_of_nonneg_right hss (le_of_not_gt hu)
      linarith only [hsupport u, hm]
  · intro hgt
    have hvq : 1 < q v := (lt_max_iff.mp hgt).resolve_left (lt_irrefl _)
    have hvh : h v < 0 := by
      by_contra hn
      simp [q, hn] at hvq
    have he : s = g v / (-h v) := by
      rw [show s = q v from max_eq_right hvq.le]
      simp [q, hvh]
    have hm : s * (-h v) = g v := by
      rw [he]
      exact div_mul_cancel₀ _ (neg_ne_zero.mpr (ne_of_lt hvh))
    refine ⟨v, ?_, ?_⟩
    · have hp := mul_pos (lt_trans zero_lt_one hgt) (neg_pos.mpr hvh)
      linarith only [hm, hp]
    · nlinarith only [hm]

theorem choose_support {ι : Type*} [Fintype ι] [Nonempty ι]
    (g h : ι → ℝ) (s₀ : ℝ) (hs₀ : 0 < s₀)
    (hsupport : ∀ v, g v + s₀ * h v ≤ 0) : ∃ s, Chosen g h s := by
  by_cases hs₁ : 1 ≤ s₀
  · obtain ⟨s, hs, _, hvalid, hcontact⟩ := choose_above g h s₀ hs₁ hsupport
    exact ⟨s, lt_of_lt_of_le zero_lt_one hs, hvalid, hcontact,
      fun hlt => False.elim (not_lt_of_ge hs hlt)⟩
  · -- Reflect the slope about one: s = 2 - t.
    obtain ⟨t, ht, htle, hvalid, hcontact⟩ :=
      choose_above (fun v => g v + 2 * h v) (fun v => -h v) (2 - s₀)
        (by linarith) (fun v => by nlinarith only [hsupport v])
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    refine ⟨2 - t, by linarith only [hs₀, htle], ?_, ?_, ?_⟩
    · intro v
      have h := hvalid v
      nlinarith only [h]
    · intro hgt
      linarith only [ht, hgt]
    · intro hlt
      obtain ⟨v, hv, he⟩ := hcontact (by linarith only [hlt])
      refine ⟨v, ?_, ?_⟩
      · exact pos_of_mul_pos_right (show 0 < t * h v by nlinarith only [hv, he]) htpos.le
      · nlinarith only [he]

/-- Any positive six-row planar support system on finitely many points has
a replacement satisfying the six slope inequalities. No pair corners occur. -/
theorem choose_six_supports {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Point) (lo hi a₀ b₀ : Point) (D : ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hplane : ∀ v, ∑ i, X v i = D)
    (ha₀ : ∀ i, 0 < a₀ i) (hb₀ : ∀ i, 0 < b₀ i)
    (hupper : ∀ i v, X v i + a₀ i * X v (i + 1) ≤ hi i + a₀ i * hi (i + 1))
    (hlower : ∀ i v, lo i + b₀ i * lo (i + 1) ≤ X v i + b₀ i * X v (i + 1)) :
    ∃ a b : Point, (∀ i, 0 < a i) ∧ (∀ i, 0 < b i) ∧
      (∀ i v, X v i + a i * X v (i + 1) ≤ hi i + a i * hi (i + 1)) ∧
      (∀ i v, lo i + b i * lo (i + 1) ≤ X v i + b i * X v (i + 1)) ∧
      (∀ i, a (i + 1) * (1 - b i) ≤ 1) ∧
      (∀ i, b (i + 1) * (1 - a i) ≤ 1) := by
  have hU (i : Fin 3) := choose_support (fun v => X v i - hi i)
    (fun v => X v (i + 1) - hi (i + 1)) (a₀ i) (ha₀ i)
    (fun v => by nlinarith only [hupper i v])
  have hL (i : Fin 3) := choose_support (fun v => lo i - X v i)
    (fun v => lo (i + 1) - X v (i + 1)) (b₀ i) (hb₀ i)
    (fun v => by nlinarith only [hlower i v])
  choose a ha using hU
  choose b hb using hL
  refine ⟨a, b, fun i => (ha i).1, fun i => (hb i).1, ?_, ?_,
    weights_of_chosen X lo hi a b D horder hplane ha hb⟩
  · intro i v
    have h := (ha i).2.1 v
    dsimp at h
    nlinarith only [h]
  · intro i v
    have h := (hb i).2.1 v
    dsimp at h
    nlinarith only [h]

/-- The finite planar same-sign support bound needs no pair-corner witnesses,
convexity, coverage, or compactness. -/
theorem width_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Point) (lo hi R a₀ b₀ : Point) (D : ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hR : ∀ i, 0 < R i)
    (hplane : ∀ v, ∑ i, X v i = D)
    (hzero : ∀ i, ∃ v, X v i = 0) (hmax : ∀ i, ∃ v, X v i = R i)
    (ha₀ : ∀ i, 0 < a₀ i) (hb₀ : ∀ i, 0 < b₀ i)
    (hupper : ∀ i v, X v i + a₀ i * X v (i + 1) ≤ hi i + a₀ i * hi (i + 1))
    (hlower : ∀ i v, lo i + b₀ i * lo (i + 1) ≤ X v i + b₀ i * X v (i + 1)) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  obtain ⟨a, b, ha, hb, hU, hL, hab, hba⟩ :=
    choose_six_supports X lo hi a₀ b₀ D horder hplane ha₀ hb₀ hupper hlower
  have hg : 0 ≤ Plank.Convex.PlanarSlopeGap.gap a b := by
    apply Plank.Convex.PlanarSlopeGap.gap_nonneg a b (fun _ => 1)
      (fun i => (ha i).le) (fun i => (hb i).le) (fun _ => zero_lt_one)
    · intro i
      have h := hab i
      nlinarith only [h]
    · intro i
      have h := hba i
      nlinarith only [h]
  apply PlanarSupportWidth.support_width_bound Set.univ
    (fun i v => X v i) lo hi a b R (fun i => (ha i).le) (fun i => (hb i).le)
    horder hR
  · intro i
    obtain ⟨v, hv⟩ := hzero i
    exact ⟨v, Set.mem_univ _, hv⟩
  · intro i
    obtain ⟨v, hv⟩ := hmax i
    exact ⟨v, Set.mem_univ _, hv⟩
  · exact fun i v _ => hU i v
  · exact fun i v _ => hL i v
  · exact hg

/-- Absorb positive plane coefficients into the coordinates. -/
theorem weighted_width_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Point) (lo hi R a b c : Point) (D : ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hR : ∀ i, 0 < R i) (hc : ∀ i, 0 < c i)
    (hplane : ∀ v, ∑ i, c i * X v i = D)
    (hzero : ∀ i, ∃ v, X v i = 0) (hmax : ∀ i, ∃ v, X v i = R i)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hupper : ∀ i v, X v i + a i * X v (i + 1) ≤ hi i + a i * hi (i + 1))
    (hlower : ∀ i v, lo i + b i * lo (i + 1) ≤ X v i + b i * X v (i + 1)) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  have transform (d x : Point) (i : Fin 3) :
      c i * x i + (c i * d i / c (i + 1)) * (c (i + 1) * x (i + 1)) =
        c i * (x i + d i * x (i + 1)) := by
    field_simp [(hc (i + 1)).ne']
  have h := width_bound (fun v i => c i * X v i)
    (fun i => c i * lo i) (fun i => c i * hi i) (fun i => c i * R i)
    (fun i => c i * a i / c (i + 1)) (fun i => c i * b i / c (i + 1)) D
    (fun i => mul_le_mul_of_nonneg_left (horder i) (hc i).le)
    (fun i => mul_pos (hc i) (hR i)) hplane
    (fun i => (hzero i).imp fun v hv => by rw [hv, mul_zero])
    (fun i => (hmax i).imp fun v hv => by rw [hv])
    (fun i => div_pos (mul_pos (hc i) (ha i)) (hc (i + 1)))
    (fun i => div_pos (mul_pos (hc i) (hb i)) (hc (i + 1)))
    (fun i v => by
      rw [transform, transform]
      exact mul_le_mul_of_nonneg_left (hupper i v) (hc i).le)
    (fun i v => by
      rw [transform, transform]
      exact mul_le_mul_of_nonneg_left (hlower i v) (hc i).le)
  have hratio (i : Fin 3) : (c i * hi i - c i * lo i) / (c i * R i) =
      (hi i - lo i) / R i := by
    rw [← mul_sub, mul_div_mul_left _ _ (hc i).ne']
  simpa only [hratio] using h

/-- Six coordinate witnesses suffice, even when the original planar set is
infinite, nonconvex or noncompact. No pair-corner contacts are assumed. -/
theorem set_width_bound (K : Set Point) (lo hi R a b c : Point) (D : ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hR : ∀ i, 0 < R i) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D)
    (hzero : ∀ i, ∃ x ∈ K, x i = 0) (hmax : ∀ i, ∃ x ∈ K, x i = R i)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hupper : ∀ i, ∀ x ∈ K, x i + a i * x (i + 1) ≤ hi i + a i * hi (i + 1))
    (hlower : ∀ i, ∀ x ∈ K, lo i + b i * lo (i + 1) ≤ x i + b i * x (i + 1)) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  choose x hx hxzero using hzero
  choose y hy hymax using hmax
  let X : Fin 3 × Bool → Point := fun v => if v.2 then y v.1 else x v.1
  have hX (v : Fin 3 × Bool) : X v ∈ K := by
    rcases v with ⟨i, b⟩
    cases b
    · exact hx i
    · exact hy i
  apply weighted_width_bound X lo hi R a b c D horder hR hc
    (fun v => hplane _ (hX v))
  · exact fun i => ⟨(i, false), hxzero i⟩
  · exact fun i => ⟨(i, true), hymax i⟩
  · exact ha
  · exact hb
  · exact fun i v => hupper i _ (hX v)
  · exact fun i v => hlower i _ (hX v)

end Plank.Convex.PlanarChosenSupports
