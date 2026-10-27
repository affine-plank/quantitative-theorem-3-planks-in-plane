/- Exhaustive equality families for three closed affine planks on any planar convex body. -/
module
public import Plank.Convex.PlanarTight.AffineRangeFamilyCompletion
public import Plank.Convex.PlanarTight.AffineRepeatedFamilies
public import Plank.Convex.PlanarTight.DirectionDichotomy
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AffineClassification
open DeficientHeightTilt (rangeWidth)

abbrev E := Fin 2 → ℝ
abbrev P := Fin 3 → ℝ

/-- The exhaustive family list: zero/full and two-plank families, boundary
triangle extensions, oriented common chords, strict triangles, and split
two-direction families. The definitions specify affine range coordinates,
body geometry, and endpoint parameters; no coverage or tightness predicate
is included in this right-hand side. -/
def Normal (K : Set E) (f : Fin 3 → E →ᵃ[ℝ] ℝ) (lo hi : P) : Prop :=
  AffinePlaneFamilies.Normal K f lo hi ∨ AffineRepeatedFamilies.Normal K f lo hi

/-- The complete classification using positive actual directional ranges.
Directions may repeat or all be parallel; endpoints may be arbitrary ordered
reals and zero-width windows are allowed. -/
theorem relative_tight_iff (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hfull : (interior K).Nonempty) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : P) (hW : ∀ i, 0 < rangeWidth K (f i)) (ho : ∀ i, lo i ≤ hi i) :
    ((∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1 ∧
      ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) ↔ Normal K f lo hi := by
  constructor
  · rintro ⟨hs, hc⟩
    have hne : K.Nonempty := hfull.mono interior_subset
    obtain ⟨m, hb, hL, hU⟩ := ExactRangeNormalization.exists_ranges K hK hne f
    by_cases hz : ∃ i, lo i = hi i
    · exact Or.inl (AffineRangeFamilyCompletion.of_zero K hconv f lo hi hW ho hz m hb hL hU hs hc)
    have hw (i : Fin 3) : lo i < hi i := lt_of_le_of_ne (ho i) (fun he => hz ⟨i, he⟩)
    let W : P := fun i => rangeWidth K (f i)
    let g := ExactRangeNormalization.forms f m W
    have hbg : ∀ x ∈ K, ∀ i, 0 ≤ g i x ∧ g i x ≤ 1 := by
      intro x hx i
      exact ExactRangeNormalization.box K f m W hW hb _ ⟨x, hx, rfl⟩ i
    have hLg : ∀ i, ∃ x ∈ K, g i x = 0 := by
      intro i
      obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := ExactRangeNormalization.zero_contacts K f m W hL i
      exact ⟨x, hx, he⟩
    have hUg : ∀ i, ∃ x ∈ K, g i x = 1 := by
      intro i
      obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := ExactRangeNormalization.unit_contacts K f m W hW hU i
      exact ⟨x, hx, he⟩
    rcases DirectionDichotomy.full_or_repeated K g hbg hLg hUg with
      ⟨a, d, ha, hp⟩ | ⟨σ, flip, heq, hind⟩
    · exact Or.inl (AffineRangeFamilyCompletion.of_relation K hconv f lo hi hW ho m hb hL hU
        a d ha (fun x _ => hp x) hs hc)
    · exact Or.inr (AffineRepeatedFamilies.of_tight K hconv hfull f lo hi hW hw m hb hL hU
        σ flip heq hind hs hc)
  · rintro (hn | hn)
    · exact AffinePlaneFamilies.Normal.tight K hconv f lo hi hW ho hn
    · exact AffineRepeatedFamilies.Normal.tight K hconv f lo hi hW hn

/-- Every nonconstant affine direction has positive actual width on a
compact convex body with nonempty interior. -/
theorem positive_ranges (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hfull : (interior K).Nonempty) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hnonzero : ∀ i, (f i).linear ≠ 0) : ∀ i, 0 < rangeWidth K (f i) := by
  obtain ⟨m, hb, _, _⟩ := ExactRangeNormalization.exists_ranges K hK
    (hfull.mono interior_subset) f
  have hspan : affineSpan ℝ K = ⊤ := hconv.interior_nonempty_iff_affineSpan_eq_top.mp hfull
  intro i
  by_contra! hw
  have heq : f i = AffineMap.const ℝ E (m i) := by
    apply AffineMap.ext_on hspan
    intro x hx
    change f i x = m i
    exact le_antisymm ((hb x hx i).2.trans (by linarith only [hw])) (hb x hx i).1
  apply hnonzero i
  simpa only [AffineMap.const_linear] using congrArg (fun g : E →ᵃ[ℝ] ℝ => g.linear) heq

/-- Exhaustive if and only if for all three closed planks on an arbitrary
compact convex planar body with nonempty interior. Each affine linear part
is nonzero, as for a plank direction. No independence, clipping, positivity
of window widths, or extra equality-case assumption is required. -/
theorem tight_iff (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hfull : (interior K).Nonempty) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (hnonzero : ∀ i, (f i).linear ≠ 0) (lo hi : P) (ho : ∀ i, lo i ≤ hi i) :
    ((∑ i, (hi i - lo i) / rangeWidth K (f i)) = 1 ∧
      ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) ↔ Normal K f lo hi :=
  relative_tight_iff K hK hconv hfull f lo hi (positive_ranges K hK hconv hfull f hnonzero) ho

end Plank.Convex.PlanarTight.AffineClassification

/-- info: 'Plank.Convex.PlanarTight.AffineClassification.relative_tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AffineClassification.relative_tight_iff

/-- info: 'Plank.Convex.PlanarTight.AffineClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AffineClassification.tight_iff
