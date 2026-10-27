/- Equality forbids overlap between positive parallel windows. -/
module
public import Plank.Convex.TwoDirectionThreePlanks
public import Plank.Convex.PlanarTight.CapTriangle
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.ParallelPair

abbrev Point := Fin 2 → ℝ

variable (K : Set Point) (hK : Convex ℝ K)
  (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
  (hL : ∃ p ∈ K, p 0 = 0) (hR : ∃ p ∈ K, p 0 = 1)
  (hB : ∃ p ∈ K, p 1 = 0) (hT : ∃ p ∈ K, p 1 = 1)

include hK hbox hL hR hB hT in
/-- In a tight cover by two vertical windows and one horizontal window,
ordered lower endpoints force the positive second window to begin after the
first ends. Otherwise containment or overlap would waste positive width. -/
theorem disjoint_of_ordered (l₀ u₀ l₁ u₁ a b : ℝ)
    (h₀ : l₀ ≤ u₀) (h₁ : l₁ < u₁) (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hsort : l₀ ≤ l₁)
    (hcover : ∀ p ∈ K, (l₀ ≤ p 0 ∧ p 0 ≤ u₀) ∨
      (l₁ ≤ p 0 ∧ p 0 ≤ u₁) ∨ (a ≤ p 1 ∧ p 1 ≤ b))
    (hsum : (u₀ - l₀) + (u₁ - l₁) + (b - a) = 1) : u₀ ≤ l₁ := by
  have htwo : ∀ l u, l ≤ u →
      (∀ p ∈ K, (l ≤ p 0 ∧ p 0 ≤ u) ∨ (a ≤ p 1 ∧ p 1 ≤ b)) →
      1 ≤ (u - l) + (b - a) := by
    intro l u hlu hc
    exact TwoAffineWindows.width_bound K hK (AffineMap.proj 0) (AffineMap.proj 1)
      (fun p hp => ⟨hbox p hp 0, hbox p hp 1⟩)
      l u a b hlu hab hL hR hB hT hc
  have hupper : u₀ < u₁ := by
    by_contra! hle
    have hdrop := htwo l₀ u₀ h₀ (by
      intro p hp
      rcases hcover p hp with h | h | h
      · exact Or.inl h
      · exact Or.inl ⟨hsort.trans h.1, h.2.trans hle⟩
      · exact Or.inr h)
    linarith only [hdrop, h₁, hsum]
  by_contra! hoverlap
  have hshort : ∀ p ∈ K, (l₀ ≤ p 0 ∧ p 0 ≤ l₁) ∨
      (l₁ ≤ p 0 ∧ p 0 ≤ u₁) ∨ (a ≤ p 1 ∧ p 1 ≤ b) := by
    intro p hp
    rcases hcover p hp with h | h | h
    · by_cases hp₁ : p 0 ≤ l₁
      · exact Or.inl ⟨h.1, hp₁⟩
      · exact Or.inr (Or.inl ⟨(le_of_not_ge hp₁), h.2.trans hupper.le⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hbound := TwoDirectionThreePlanks.sum_ge_one K hK hbox hL hR hB hT
    l₀ l₁ l₁ u₁ a b hsort h₁.le hab ha hb hshort
  linarith only [hbound, hoverlap, hsum]

include hK hbox hL hR hB hT in
/-- The two positive parallel windows in a tight normalized cover have
disjoint interiors. Their boundaries are allowed to touch. -/
theorem disjoint (l₀ u₀ l₁ u₁ a b : ℝ)
    (h₀ : l₀ < u₀) (h₁ : l₁ < u₁) (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hcover : ∀ p ∈ K, (l₀ ≤ p 0 ∧ p 0 ≤ u₀) ∨
      (l₁ ≤ p 0 ∧ p 0 ≤ u₁) ∨ (a ≤ p 1 ∧ p 1 ≤ b))
    (hsum : (u₀ - l₀) + (u₁ - l₁) + (b - a) = 1) :
    u₀ ≤ l₁ ∨ u₁ ≤ l₀ := by
  rcases le_total l₀ l₁ with hsort | hsort
  · exact Or.inl (disjoint_of_ordered K hK hbox hL hR hB hT
      l₀ u₀ l₁ u₁ a b h₀.le h₁ hab ha hb hsort hcover hsum)
  · apply Or.inr
    apply disjoint_of_ordered K hK hbox hL hR hB hT
      l₁ u₁ l₀ u₀ a b h₁.le h₀ hab ha hb hsort
    · intro p hp
      rcases hcover p hp with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · linarith only [hsum]

include hK hbox hL hR hB hT in
/-- A tight cover with three positive widths and a gap between its two
parallel windows is one-dimensional in the two normalized coordinates:
the body lies on the diagonal or the reflected diagonal. -/
theorem separated_collapse (l₀ u₀ l₁ u₁ a b : ℝ)
    (h₀ : l₀ < u₀) (h₁ : l₁ < u₁) (hab : a < b)
    (hl₀ : 0 ≤ l₀) (hu₀ : u₀ ≤ 1) (hl₁ : 0 ≤ l₁) (hu₁ : u₁ ≤ 1)
    (ha : 0 ≤ a) (hb : b ≤ 1) (hgap : u₀ < l₁)
    (hcover : ∀ p ∈ K, (l₀ ≤ p 0 ∧ p 0 ≤ u₀) ∨
      (l₁ ≤ p 0 ∧ p 0 ≤ u₁) ∨ (a ≤ p 1 ∧ p 1 ≤ b))
    (hsum : (u₀ - l₀) + (u₁ - l₁) + (b - a) = 1) :
    (∀ p ∈ K, p 0 = p 1) ∨ (∀ p ∈ K, 1 - p 0 = p 1) := by
  have hbelow := ConvexSeparatedWindows.allocate_convex
    {p : Point | p ∈ K ∧ p 1 < a}
    (hK.inter ((convex_Iio a).linear_preimage (LinearMap.proj 1 : Point →ₗ[ℝ] ℝ)))
    (fun p : Point => p 0) (continuous_apply 0).continuousOn l₀ u₀ l₁ u₁ hgap
    (by
      intro p hp
      rcases hcover p hp.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (not_lt_of_ge h.1 hp.2))
  have habove := ConvexSeparatedWindows.allocate_convex
    {p : Point | p ∈ K ∧ b < p 1}
    (hK.inter ((convex_Ioi b).linear_preimage (LinearMap.proj 1 : Point →ₗ[ℝ] ℝ)))
    (fun p : Point => p 0) (continuous_apply 0).continuousOn l₀ u₀ l₁ u₁ hgap
    (by
      intro p hp
      rcases hcover p hp.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (not_lt_of_ge h.2 hp.2))
  have htwo (l u : ℝ) (hlu : l ≤ u)
      (hlo : ∀ p ∈ K, p 1 < a → l ≤ p 0 ∧ p 0 ≤ u)
      (hhi : ∀ p ∈ K, b < p 1 → l ≤ p 0 ∧ p 0 ≤ u) :
      1 ≤ (u - l) + (b - a) := by
    apply TwoAffineWindows.width_bound K hK (AffineMap.proj 0) (AffineMap.proj 1)
      (fun p hp => ⟨hbox p hp 0, hbox p hp 1⟩) l u a b hlu hab.le hL hR hB hT
    intro p hp
    by_cases hpa : p 1 < a
    · exact Or.inl (hlo p hp hpa)
    by_cases hpb : b < p 1
    · exact Or.inl (hhi p hp hpb)
    exact Or.inr ⟨le_of_not_gt hpa, le_of_not_gt hpb⟩
  have hlow_width (l u : ℝ) (hlu : l ≤ u)
      (hc : ∀ p ∈ K, p 1 < a → l ≤ p 0 ∧ p 0 ≤ u) : a ≤ u - l := by
    obtain ⟨L, hLK, hXL⟩ := hL
    obtain ⟨R, hRK, hXR⟩ := hR
    obtain ⟨B, hBK, hYB⟩ := hB
    exact ConvexCapWidth.cap_bound_lower K hK hbox L R B hLK hRK hBK hXL hXR hYB
      a ha (hab.le.trans hb) l u hlu hc
  have hupp_width (l u : ℝ) (hlu : l ≤ u)
      (hc : ∀ p ∈ K, b < p 1 → l ≤ p 0 ∧ p 0 ≤ u) : 1 - b ≤ u - l := by
    obtain ⟨L, hLK, hXL⟩ := hL
    obtain ⟨R, hRK, hXR⟩ := hR
    obtain ⟨T, hTK, hYT⟩ := hT
    exact ConvexCapWidth.cap_bound_upper K hK hbox L R T hLK hRK hTK hXL hXR hYT
      b (ha.trans hab.le) hb l u hlu hc
  rcases hbelow with hbelow | hbelow <;> rcases habove with habove | habove
  · have hdrop := htwo l₀ u₀ h₀.le (fun p hp hy => hbelow p ⟨hp, hy⟩)
      (fun p hp hy => habove p ⟨hp, hy⟩)
    exact False.elim (by linarith only [hdrop, hsum, h₁])
  · have hlow := hlow_width l₀ u₀ h₀.le (fun p hp hy => hbelow p ⟨hp, hy⟩)
    have hupp := hupp_width l₁ u₁ h₁.le (fun p hp hy => habove p ⟨hp, hy⟩)
    have hw₀ : u₀ - l₀ = a := by linarith only [hlow, hupp, hsum]
    have hw₁ : u₁ - l₁ = 1 - b := by linarith only [hlow, hupp, hsum]
    apply Or.inl
    exact CapTriangle.opposite_caps_collapse K hK (AffineMap.proj 0) (AffineMap.proj 1)
      (fun p hp => ⟨hbox p hp 0, hbox p hp 1⟩) hL hR hB hT a b l₀ u₀ l₁ u₁
      (by linarith only [hw₀, h₀]) hab (by linarith only [hw₁, h₁])
      hl₀ hu₀ hl₁ hu₁ hw₀ hw₁ hgap
      (fun p hp hy => hbelow p ⟨hp, hy⟩) (fun p hp hy => habove p ⟨hp, hy⟩)
  · have hlow := hlow_width l₁ u₁ h₁.le (fun p hp hy => hbelow p ⟨hp, hy⟩)
    have hupp := hupp_width l₀ u₀ h₀.le (fun p hp hy => habove p ⟨hp, hy⟩)
    have hw₁ : u₁ - l₁ = a := by linarith only [hlow, hupp, hsum]
    have hw₀ : u₀ - l₀ = 1 - b := by linarith only [hlow, hupp, hsum]
    let X : Point →ᵃ[ℝ] ℝ := AffineMap.const ℝ Point 1 - AffineMap.proj 0
    have hx (p : Point) : X p = 1 - p 0 := rfl
    apply Or.inr
    apply CapTriangle.opposite_caps_collapse K hK X (AffineMap.proj 1)
      (fun p hp => ⟨by rw [hx]; constructor <;> linarith [(hbox p hp 0)], hbox p hp 1⟩)
      (by obtain ⟨p, hp, he⟩ := hR; exact ⟨p, hp, by rw [hx, he]; ring⟩)
      (by obtain ⟨p, hp, he⟩ := hL; exact ⟨p, hp, by rw [hx, he]; ring⟩)
      hB hT a b (1 - u₁) (1 - l₁) (1 - u₀) (1 - l₀)
      (by linarith only [hw₁, h₁]) hab (by linarith only [hw₀, h₀])
      (by linarith only [hu₁]) (by linarith only [hl₁])
      (by linarith only [hu₀]) (by linarith only [hl₀])
      (by linarith only [hw₁]) (by linarith only [hw₀]) (by linarith only [hgap])
    · intro p hp hy
      have hh := hbelow p ⟨hp, hy⟩
      rw [hx]
      constructor <;> linarith only [hh.1, hh.2]
    · intro p hp hy
      have hh := habove p ⟨hp, hy⟩
      rw [hx]
      constructor <;> linarith only [hh.1, hh.2]
  · have hdrop := htwo l₁ u₁ h₁.le (fun p hp hy => hbelow p ⟨hp, hy⟩)
      (fun p hp hy => habove p ⟨hp, hy⟩)
    exact False.elim (by linarith only [hdrop, hsum, h₀])

include hK in
private theorem no_collapse (hfull : (interior K).Nonempty)
    (hc : (∀ p ∈ K, p 0 = p 1) ∨ (∀ p ∈ K, 1 - p 0 = p 1)) : False := by
  have hspan := hK.interior_nonempty_iff_affineSpan_eq_top.mp hfull
  rcases hc with hc | hc
  · have he : (AffineMap.proj 0 : Point →ᵃ[ℝ] ℝ) = AffineMap.proj 1 :=
      AffineMap.ext_on hspan (fun p hp => hc p hp)
    have hh := congrArg (fun f : Point →ᵃ[ℝ] ℝ => f ![0, 1]) he
    norm_num at hh
  · have he : (AffineMap.const ℝ Point 1 - AffineMap.proj 0 : Point →ᵃ[ℝ] ℝ) =
        AffineMap.proj 1 := AffineMap.ext_on hspan (fun p hp => hc p hp)
    have hh := congrArg (fun f : Point →ᵃ[ℝ] ℝ => f 0) he
    norm_num at hh

include hK hbox hL hR hB hT in
/-- On a planar convex set with nonempty interior, a tight cover by three
positive windows in exactly these two coordinate directions is obtained
by splitting one window into two adjacent windows. The pair has neither
overlap nor a gap. -/
theorem touching (hfull : (interior K).Nonempty) (l₀ u₀ l₁ u₁ a b : ℝ)
    (h₀ : l₀ < u₀) (h₁ : l₁ < u₁) (hab : a < b)
    (hl₀ : 0 ≤ l₀) (hu₀ : u₀ ≤ 1) (hl₁ : 0 ≤ l₁) (hu₁ : u₁ ≤ 1)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hcover : ∀ p ∈ K, (l₀ ≤ p 0 ∧ p 0 ≤ u₀) ∨
      (l₁ ≤ p 0 ∧ p 0 ≤ u₁) ∨ (a ≤ p 1 ∧ p 1 ≤ b))
    (hsum : (u₀ - l₀) + (u₁ - l₁) + (b - a) = 1) :
    u₀ = l₁ ∨ u₁ = l₀ := by
  rcases disjoint K hK hbox hL hR hB hT l₀ u₀ l₁ u₁ a b h₀ h₁ hab.le ha hb
    hcover hsum with hle | hle
  · left
    apply le_antisymm hle
    by_contra! hgap
    exact no_collapse K hK hfull (separated_collapse K hK hbox hL hR hB hT
      l₀ u₀ l₁ u₁ a b h₀ h₁ hab hl₀ hu₀ hl₁ hu₁ ha hb hgap hcover hsum)
  · right
    apply le_antisymm hle
    by_contra! hgap
    apply no_collapse K hK hfull
    apply separated_collapse K hK hbox hL hR hB hT
      l₁ u₁ l₀ u₀ a b h₁ h₀ hab hl₁ hu₁ hl₀ hu₀ ha hb hgap
    · intro p hp
      rcases hcover p hp with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · linarith only [hsum]

end Plank.Convex.PlanarTight.ParallelPair

/-- info: 'Plank.Convex.PlanarTight.ParallelPair.disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ParallelPair.disjoint

/-- info: 'Plank.Convex.PlanarTight.ParallelPair.separated_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ParallelPair.separated_collapse

/-- info: 'Plank.Convex.PlanarTight.ParallelPair.touching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.ParallelPair.touching
