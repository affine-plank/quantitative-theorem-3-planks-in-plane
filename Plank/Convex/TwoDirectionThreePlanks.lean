/- Three normalized windows in two directions: two vertical and one
horizontal. Actual coordinate realizers replace any compactness assumption.
Closed windows, empty open caps, and zero-width windows are all allowed. -/
module
public import Plank.Convex.TwoAffineWindows
public import Plank.Convex.ConvexSeparatedWindows
public import Plank.Convex.ConvexCapWidth
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.TwoDirectionThreePlanks

abbrev Point := Fin 2 → ℝ

variable (K : Set Point) (hconv : Convex ℝ K)
  (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
  (hL : ∃ p ∈ K, p 0 = 0) (hR : ∃ p ∈ K, p 0 = 1)
  (hB : ∃ p ∈ K, p 1 = 0) (hT : ∃ p ∈ K, p 1 = 1)

include hconv hbox hL hR hB hT in
private theorem two_plank_bound (l h a b : ℝ) (hlh : l ≤ h) (hab : a ≤ b)
    (hcover : ∀ p ∈ K, (l ≤ p 0 ∧ p 0 ≤ h) ∨ (a ≤ p 1 ∧ p 1 ≤ b)) :
    1 ≤ (h - l) + (b - a) := by
  exact TwoAffineWindows.width_bound K hconv (AffineMap.proj 0) (AffineMap.proj 1)
    (fun p hp => ⟨hbox p hp 0, hbox p hp 1⟩)
    l h a b hlh hab hL hR hB hT hcover

private theorem cover_of_caps (l h a b : ℝ)
    (hlower : ∀ p ∈ K, p 1 < a → l ≤ p 0 ∧ p 0 ≤ h)
    (hupper : ∀ p ∈ K, b < p 1 → l ≤ p 0 ∧ p 0 ≤ h) :
    ∀ p ∈ K, (l ≤ p 0 ∧ p 0 ≤ h) ∨ (a ≤ p 1 ∧ p 1 ≤ b) := by
  intro p hp
  by_cases hlo : p 1 < a
  · exact Or.inl (hlower p hp hlo)
  by_cases hhi : b < p 1
  · exact Or.inl (hupper p hp hhi)
  exact Or.inr ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩

include hconv hbox hL hR hB hT in
private theorem separated_bound (l1 h1 l2 h2 a b : ℝ)
    (hl1 : l1 ≤ h1) (hl2 : l2 ≤ h2) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hgap : h1 < l2)
    (hcover : ∀ p ∈ K, (l1 ≤ p 0 ∧ p 0 ≤ h1) ∨
      (l2 ≤ p 0 ∧ p 0 ≤ h2) ∨ (a ≤ p 1 ∧ p 1 ≤ b)) :
    1 ≤ (h1 - l1) + (h2 - l2) + (b - a) := by
  have hlower := ConvexSeparatedWindows.allocate_convex
    {p : Point | p ∈ K ∧ p 1 < a}
    (hconv.inter ((convex_Iio a).linear_preimage (LinearMap.proj 1 : Point →ₗ[ℝ] ℝ)))
    (fun p : Point => p 0) (continuous_apply 0).continuousOn l1 h1 l2 h2 hgap
    (by
      intro p hp
      rcases hcover p hp.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (not_lt_of_ge h.1 hp.2))
  have hupper := ConvexSeparatedWindows.allocate_convex
    {p : Point | p ∈ K ∧ b < p 1}
    (hconv.inter ((convex_Ioi b).linear_preimage (LinearMap.proj 1 : Point →ₗ[ℝ] ℝ)))
    (fun p : Point => p 0) (continuous_apply 0).continuousOn l1 h1 l2 h2 hgap
    (by
      intro p hp
      rcases hcover p hp.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (not_lt_of_ge h.2 hp.2))
  obtain ⟨pL, hpL, hxL⟩ := hL
  obtain ⟨pR, hpR, hxR⟩ := hR
  obtain ⟨pB, hpB, hyB⟩ := hB
  obtain ⟨pT, hpT, hyT⟩ := hT
  rcases hlower with hlower | hlower <;> rcases hupper with hupper | hupper
  · have htwo := two_plank_bound K hconv hbox ⟨pL, hpL, hxL⟩ ⟨pR, hpR, hxR⟩
      ⟨pB, hpB, hyB⟩ ⟨pT, hpT, hyT⟩ l1 h1 a b hl1 hab
      (cover_of_caps K l1 h1 a b (fun p hp hy => hlower p ⟨hp, hy⟩)
        (fun p hp hy => hupper p ⟨hp, hy⟩))
    linarith
  · have hlo := ConvexCapWidth.cap_bound_lower K hconv hbox pL pR pB
      hpL hpR hpB hxL hxR hyB a ha (hab.trans hb) l1 h1 hl1
      (fun p hp hy => hlower p ⟨hp, hy⟩)
    have hhi := ConvexCapWidth.cap_bound_upper K hconv hbox pL pR pT
      hpL hpR hpT hxL hxR hyT b (ha.trans hab) hb l2 h2 hl2
      (fun p hp hy => hupper p ⟨hp, hy⟩)
    linarith
  · have hlo := ConvexCapWidth.cap_bound_lower K hconv hbox pL pR pB
      hpL hpR hpB hxL hxR hyB a ha (hab.trans hb) l2 h2 hl2
      (fun p hp hy => hlower p ⟨hp, hy⟩)
    have hhi := ConvexCapWidth.cap_bound_upper K hconv hbox pL pR pT
      hpL hpR hpT hxL hxR hyT b (ha.trans hab) hb l1 h1 hl1
      (fun p hp hy => hupper p ⟨hp, hy⟩)
    linarith
  · have htwo := two_plank_bound K hconv hbox ⟨pL, hpL, hxL⟩ ⟨pR, hpR, hxR⟩
      ⟨pB, hpB, hyB⟩ ⟨pT, hpT, hyT⟩ l2 h2 a b hl2 hab
      (cover_of_caps K l2 h2 a b (fun p hp hy => hlower p ⟨hp, hy⟩)
        (fun p hp hy => hupper p ⟨hp, hy⟩))
    linarith

include hconv hbox hL hR hB hT in
/-- Two vertical windows and one horizontal window covering a convex body
whose two actual coordinate ranges are `[0,1]` have total width at least one.
The four realizer hypotheses imply nonemptiness; compactness is unnecessary.
Vertical windows may extend outside the unit interval. Empty caps and
zero-width windows require no additional nondegeneracy assumptions. -/
theorem sum_ge_one (l1 h1 l2 h2 a b : ℝ)
    (hl1 : l1 ≤ h1) (hl2 : l2 ≤ h2) (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hcover : ∀ p ∈ K, (l1 ≤ p 0 ∧ p 0 ≤ h1) ∨
      (l2 ≤ p 0 ∧ p 0 ≤ h2) ∨ (a ≤ p 1 ∧ p 1 ≤ b)) :
    1 ≤ (h1 - l1) + (h2 - l2) + (b - a) := by
  by_cases hgap : h1 < l2
  · exact separated_bound K hconv hbox hL hR hB hT l1 h1 l2 h2 a b
      hl1 hl2 hab ha hb hgap hcover
  by_cases hgap' : h2 < l1
  · have hswap := separated_bound K hconv hbox hL hR hB hT l2 h2 l1 h1 a b
      hl2 hl1 hab ha hb hgap' (by
        intro p hp
        rcases hcover p hp with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h))
    linarith
  have hcost : max h1 h2 - min l1 l2 ≤ (h1 - l1) + (h2 - l2) := by
    rcases le_total l1 l2 with hl | hl
    · rw [min_eq_left hl]
      rcases le_total h1 h2 with hh | hh
      · rw [max_eq_right hh]; linarith
      · rw [max_eq_left hh]; linarith
    · rw [min_eq_right hl]
      rcases le_total h1 h2 with hh | hh
      · rw [max_eq_right hh]; linarith
      · rw [max_eq_left hh]; linarith
  have htwo := two_plank_bound K hconv hbox hL hR hB hT
    (min l1 l2) (max h1 h2) a b
    ((min_le_left l1 l2).trans (hl1.trans (le_max_left h1 h2))) hab (by
      intro p hp
      rcases hcover p hp with h | h | h
      · exact Or.inl ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩
      · exact Or.inl ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩
      · exact Or.inr h)
  linarith

end Plank.Convex.TwoDirectionThreePlanks

/-- info: 'Plank.Convex.TwoDirectionThreePlanks.sum_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.TwoDirectionThreePlanks.sum_ge_one
