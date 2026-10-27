/- On a finite convex hull, one slope choice gives separation and tangency. -/
module
public import Plank.Convex.ConvexPairSegments
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarChosenSupports

def Chosen {ι : Type*} (g h : ι → ℝ) (s : ℝ) : Prop :=
  0 < s ∧ (∀ v, g v + s * h v ≤ 0) ∧
    (1 < s → ∃ v, 0 < g v ∧ g v + s * h v = 0) ∧
    (s < 1 → ∃ v, 0 < h v ∧ g v + s * h v = 0)

end Plank.Convex.PlanarChosenSupports

namespace Plank.Convex.FinitePairSupports
open PlanarChosenSupports (Chosen)

/-- The largest lower slope bound and smallest upper bound select the
feasible slope toward one, with both required tangency witnesses. -/
theorem choose {ι : Type*} [Fintype ι] (g h : ι → ℝ)
    (hp : ∃ p, 0 < g p)
    (hsign : ∀ p, 0 < g p → h p < 0)
    (hcross : ∀ p q, 0 < g p → 0 < h q → g p * h q ≤ g q * h p) :
    ∃ s, Chosen g h s := by
  classical
  obtain ⟨p₀, hp₀⟩ := hp
  let l : ι → ℝ := fun v => if 0 < g v then g v / (-h v) else 0
  let u : ι → ℝ := fun v => if 0 < h v then (-g v) / h v else 1
  obtain ⟨p, _, hmax⟩ := Finset.exists_max_image Finset.univ l ⟨p₀, Finset.mem_univ _⟩
  obtain ⟨q, _, hmin⟩ := Finset.exists_min_image Finset.univ u ⟨p₀, Finset.mem_univ _⟩
  have hpos : 0 < l p := (show 0 < l p₀ by
    simpa [l, hp₀] using div_pos hp₀ (neg_pos.mpr (hsign p₀ hp₀))).trans_le
      (hmax p₀ (Finset.mem_univ _))
  have hp : 0 < g p := by
    by_contra hn
    simp [l, hn] at hpos
  have bound (v : ι) (hv : 0 < h v) : l p ≤ (-g v) / h v := by
    simp only [l, if_pos hp]
    apply (div_le_div_iff₀ (neg_pos.mpr (hsign p hp)) hv).mpr
    nlinarith only [hcross p v hp hv]
  have hmin_one : u q ≤ 1 := by
    have H := hmin p (Finset.mem_univ _)
    simpa [u, not_lt_of_ge (hsign p hp).le] using H
  let s := max (l p) (u q)
  refine ⟨s, hpos.trans_le (le_max_left _ _), ?_, ?_, ?_⟩
  · intro v
    by_cases hg : 0 < g v
    · have H : g v / (-h v) ≤ s := by
        calc g v / (-h v) = l v := by simp [l, hg]
             _ ≤ l p := hmax v (Finset.mem_univ _)
             _ ≤ s := le_max_left _ _
      have H := (div_le_iff₀ (neg_pos.mpr (hsign v hg))).mp H
      nlinarith only [H]
    · by_cases hh : 0 < h v
      · have H : s ≤ (-g v) / h v := max_le (bound v hh) (by
          simpa [u, hh] using hmin v (Finset.mem_univ _))
        have H := (le_div_iff₀ hh).mp H
        linarith only [H]
      · exact add_nonpos (le_of_not_gt hg) (mul_nonpos_of_nonneg_of_nonpos
          (hpos.trans_le (le_max_left _ _)).le (le_of_not_gt hh))
  · intro hgt
    have H : 1 < l p := (lt_max_iff.mp hgt).resolve_right (not_lt_of_ge hmin_one)
    have hs : s = l p := max_eq_left (hmin_one.trans H.le)
    have he : l p * (-h p) = g p := by
      simp only [l, if_pos hp]
      exact div_mul_cancel₀ _ (neg_ne_zero.mpr (hsign p hp).ne)
    exact ⟨p, hp, by rw [hs]; nlinarith only [he]⟩
  · intro hlt
    have H : u q < 1 := (le_max_right _ _).trans_lt hlt
    have hq : 0 < h q := by
      by_contra hn
      simp [u, hn] at H
    have H : l p ≤ u q := by simpa [u, hq] using bound q hq
    have hs : s = u q := max_eq_right H
    have he : u q * h q = -g q := by
      simp only [u, if_pos hq]
      exact div_mul_cancel₀ _ hq.ne'
    exact ⟨q, hq, by rw [hs]; linarith only [he]⟩

/-- Convexity of the covered set supplies the finite compatibility inequalities.
The points alone need not contain their pairwise segments. -/
theorem chosen_on_points {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (K : Set E) (hK : Convex ℝ K) (X : ι → E) (hX : ∀ v, X v ∈ K)
    (g h : E →ᵃ[ℝ] ℝ) (hp : ∃ v, 0 < g (X v)) (hq : ∃ v, 0 < h (X v))
    (he : ¬ ∃ x ∈ K, 0 < g x ∧ 0 < h x) :
    ∃ s, Chosen (fun v => g (X v)) (fun v => h (X v)) s := by
  obtain ⟨q, hq⟩ := hq
  have hc (p q : ι) (hp : 0 < g (X p)) (hq : 0 < h (X q)) :=
    Plank.Convex.ConvexCellSeparation.cross_bound K hK g h (X p) (X q) (hX p) (hX q) hp hq he
  apply choose _ _ hp ?_ hc
  intro p hp
  have hgq : g (X q) ≤ 0 := le_of_not_gt (fun hg => he ⟨X q, hX q, hg, hq⟩)
  by_contra! hn
  exact (mul_pos hp hq).not_ge ((hc p q hp hq).trans
    (mul_nonpos_of_nonpos_of_nonneg hgq hn))

/-- The chosen finite separator holds on the full convex hull. Thus one finite
construction supplies both frozen supporting rows and ordered tangencies. -/
theorem chosen_on_hull {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (X : ι → E) (g h : E →ᵃ[ℝ] ℝ)
    (hp : ∃ v, 0 < g (X v)) (hq : ∃ v, 0 < h (X v))
    (he : ¬ ∃ x ∈ convexHull ℝ (Set.range X), 0 < g x ∧ 0 < h x) :
    ∃ s, Chosen (fun v => g (X v)) (fun v => h (X v)) s ∧
      ∀ x ∈ convexHull ℝ (Set.range X), g x + s * h x ≤ 0 := by
  obtain ⟨s, hs⟩ := chosen_on_points (convexHull ℝ (Set.range X))
    (convex_convexHull ℝ _) X (fun v => subset_convexHull ℝ _ ⟨v, rfl⟩) g h hp hq he
  refine ⟨s, hs, ?_⟩
  have H : convexHull ℝ (Set.range X) ⊆ {x | (g + s • h) x ≤ 0} :=
    convexHull_min (by rintro x ⟨v, rfl⟩; exact hs.2.1 v)
      ((convex_Iic (0 : ℝ)).affine_preimage (g + s • h))
  exact fun x hx => H hx

end Plank.Convex.FinitePairSupports
