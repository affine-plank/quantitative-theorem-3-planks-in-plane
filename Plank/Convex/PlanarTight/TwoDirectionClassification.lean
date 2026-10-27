/- Explicit equality families when one of two planar directions is repeated. -/
module
public import Plank.Convex.PlanarTight.ParallelPair
public import Plank.Convex.PlanarTight.TwoPlankClassification
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoDirectionClassification

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Two windows in the first direction and one in the second. -/
def Tight (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l₀ u₀ l₁ u₁ a b : ℝ) : Prop :=
  (u₀ - l₀) + (u₁ - l₁) + (b - a) = 1 ∧
    ∀ p ∈ K, (l₀ ≤ X p ∧ X p ≤ u₀) ∨
      (l₁ ≤ X p ∧ X p ≤ u₁) ∨ (a ≤ Y p ∧ Y p ≤ b)

/-- Joining two adjacent closed windows preserves coverage and total width. -/
theorem split_tight_iff (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l₀ u₀ l₁ u₁ a b : ℝ)
    (h₀ : l₀ ≤ u₀) (h₁ : l₁ ≤ u₁) (htouch : u₀ = l₁) :
    Tight K X Y l₀ u₀ l₁ u₁ a b ↔ TwoPlankClassification.Tight K X Y l₀ u₁ a b := by
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨by linarith only [hs, htouch], ?_⟩
    intro p hp
    rcases hc p hp with h | h | h
    · exact Or.inl ⟨h.1, h.2.trans (htouch ▸ h₁)⟩
    · exact Or.inl ⟨(h₀.trans htouch.le).trans h.1, h.2⟩
    · exact Or.inr h
  · rintro ⟨hs, hc⟩
    refine ⟨by linarith only [hs, htouch], ?_⟩
    intro p hp
    rcases hc p hp with h | h
    · rcases le_total (X p) u₀ with hle | hge
      · exact Or.inl ⟨h.1, hle⟩
      · exact Or.inr (Or.inl ⟨htouch ▸ hge, h.2⟩)
    · exact Or.inr (Or.inr h)

/-- Swapping the two repeated-direction windows preserves tightness. -/
theorem tight_swap (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l₀ u₀ l₁ u₁ a b : ℝ) :
    Tight K X Y l₁ u₁ l₀ u₀ a b ↔ Tight K X Y l₀ u₀ l₁ u₁ a b := by
  simp only [Tight, add_comm (u₁ - l₁) (u₀ - l₀), or_left_comm]

/-- Split a triangular or quadrilateral two-plank normal form at any
strictly interior point of its first window. The two possible orders of
the labeled split windows are explicit. No covering predicate occurs here. -/
def Normal (K : Set E) (X Y : E →ᵃ[ℝ] ℝ) (l₀ u₀ l₁ u₁ a b : ℝ) : Prop :=
  (u₀ = l₁ ∧ TwoPlankClassification.Normal K X Y l₀ u₁ a b) ∨
    (u₁ = l₀ ∧ TwoPlankClassification.Normal K X Y l₁ u₀ a b)

abbrev Point := Fin 2 → ℝ

/-- Complete positive equality classification in two normalized planar
directions. The body has a triangular or quadrilateral enclosure from the
two-plank list, and one of its windows is split into two adjacent parts. -/
theorem tight_iff (K : Set Point) (hK : Convex ℝ K) (hfull : (interior K).Nonempty)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hL : ∃ p ∈ K, p 0 = 0) (hR : ∃ p ∈ K, p 0 = 1)
    (hB : ∃ p ∈ K, p 1 = 0) (hT : ∃ p ∈ K, p 1 = 1)
    (l₀ u₀ l₁ u₁ a b : ℝ) (h₀ : l₀ < u₀) (h₁ : l₁ < u₁) (hab : a < b)
    (hl₀ : 0 ≤ l₀) (hu₀ : u₀ ≤ 1) (hl₁ : 0 ≤ l₁) (hu₁ : u₁ ≤ 1)
    (ha : 0 ≤ a) (hb : b ≤ 1) :
    Tight K (AffineMap.proj 0) (AffineMap.proj 1) l₀ u₀ l₁ u₁ a b ↔
      Normal K (AffineMap.proj 0) (AffineMap.proj 1) l₀ u₀ l₁ u₁ a b := by
  have H : TwoPlankClassification.Ranges K (AffineMap.proj 0) (AffineMap.proj 1) :=
    ⟨fun p hp => ⟨hbox p hp 0, hbox p hp 1⟩, hL, hR, hB, hT⟩
  have hnormal₀ (htouch : u₀ = l₁) :
      Tight K (AffineMap.proj 0) (AffineMap.proj 1) l₀ u₀ l₁ u₁ a b ↔
        TwoPlankClassification.Normal K (AffineMap.proj 0) (AffineMap.proj 1) l₀ u₁ a b :=
    (split_tight_iff K _ _ l₀ u₀ l₁ u₁ a b h₀.le h₁.le htouch).trans
      (TwoPlankClassification.tight_iff K hK _ _ H l₀ u₁ a b hl₀ hu₁ ha hb
        (by linarith only [h₀, h₁, htouch]) hab)
  have hnormal₁ (htouch : u₁ = l₀) :
      Tight K (AffineMap.proj 0) (AffineMap.proj 1) l₀ u₀ l₁ u₁ a b ↔
        TwoPlankClassification.Normal K (AffineMap.proj 0) (AffineMap.proj 1) l₁ u₀ a b :=
    (tight_swap K _ _ l₀ u₀ l₁ u₁ a b).symm.trans
      ((split_tight_iff K _ _ l₁ u₁ l₀ u₀ a b h₁.le h₀.le htouch).trans
        (TwoPlankClassification.tight_iff K hK _ _ H l₁ u₀ a b hl₁ hu₀ ha hb
          (by linarith only [h₀, h₁, htouch]) hab))
  constructor
  · intro ht
    have ht' := ParallelPair.touching K hK hbox hL hR hB hT hfull
      l₀ u₀ l₁ u₁ a b h₀ h₁ hab hl₀ hu₀ hl₁ hu₁ ha hb ht.2 ht.1
    rcases ht' with ht' | ht'
    · exact Or.inl ⟨ht', (hnormal₀ ht').mp ht⟩
    · exact Or.inr ⟨ht', (hnormal₁ ht').mp ht⟩
  · rintro (⟨htouch, hn⟩ | ⟨htouch, hn⟩)
    · exact (hnormal₀ htouch).mpr hn
    · exact (hnormal₁ htouch).mpr hn

end Plank.Convex.PlanarTight.TwoDirectionClassification

/-- info: 'Plank.Convex.PlanarTight.TwoDirectionClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoDirectionClassification.tight_iff
