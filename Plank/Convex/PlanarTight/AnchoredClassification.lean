/- Explicit exhaustive families for a positive planar equality cover
whose first lower endpoint is anchored at zero. -/
module
public import Plank.Convex.PlanarTight.AnchoredCapClassification
public import Plank.Convex.PlanarTight.TriangleContraction
public import Plank.Convex.PlanarTight.TwoPlankParameters
public import Plank.Convex.PlanarTight.OrientedCommonChord
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredClassification

abbrev Point := Fin 3 → ℝ

/-- The triangle family: the first coordinate is one at T and zero
on the opposite edge; the first window is `[0,r]`; the remaining windows
are the displayed homothetic images of the explicit two-plank families. -/
def TriangleNormal (K : Set Point) (lo hi : Point) : Prop :=
  ∃ (T : Point) (r l u m v : ℝ), AnchoredCapBody.Has K (AffineMap.proj 0) T ∧
    0 < r ∧ r < 1 ∧ 0 ≤ l ∧ u ≤ 1 ∧ 0 ≤ m ∧ v ≤ 1 ∧ l < u ∧ m < v ∧
    lo = TriangleContraction.lower T r l m ∧ hi = TriangleContraction.upper T r u v ∧
    TwoPlankClassification.Normal K (AffineMap.proj 1) (AffineMap.proj 2) l u m v

/-- The two actual anchored families: a triangle obtained by extending
a two-plank normal form, or the independently oriented common-chord family. -/
def Normal (K : Set Point) (lo hi : Point) : Prop :=
  TriangleNormal K lo hi ∨ OrientedCommonChord.Normal K (fun i => AffineMap.proj i) lo hi

/-- Complete equality classification for positive normalized planar
windows with the first lower endpoint at zero. The right side specifies
body geometry and window parameters, without a coverage or width-sum predicate. -/
theorem tight_iff (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0) :
    ((∑ i, (hi i - lo i)) = 1 ∧ ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i) ↔
      Normal K lo hi := by
  constructor
  · rintro ⟨hsum, hcover⟩
    obtain ⟨T, hT, hT₀⟩ := hU 0
    rcases AnchoredCapClassification.cap_or_opposite_vertices K hK hbox hL hU
        a b c d ha hb hc hplane lo hi hwidth hanchor hcover hsum T hT hT₀ with hcap | hchord
    · apply Or.inl
      let r := hi 0
      have hr : 0 < r := by simpa only [hanchor] using hwidth 0
      have hr₁ : r < 1 := by
        have hs := hsum
        rw [Fin.sum_univ_three, hanchor, sub_zero] at hs
        have h₁ := hwidth 1
        have h₂ := hwidth 2
        change hi 0 < 1
        linarith only [hs, h₁, h₂]
      have hd : 0 < 1 - r := sub_pos.mpr hr₁
      let L := (lo 1 - r * T 1) / (1 - r)
      let U := (hi 1 - r * T 1) / (1 - r)
      let M := (lo 2 - r * T 2) / (1 - r)
      let V := (hi 2 - r * T 2) / (1 - r)
      have hn : TwoPlankClassification.Normal K (AffineMap.proj 1) (AffineMap.proj 2) L U M V :=
        AnchoredReduction.two_plank_normal K hK hbox hL hU lo hi hwidth hanchor hcover hsum T hT hT₀
      obtain ⟨hL₀, hU₁, hM₀, hV₁⟩ := TwoPlankParameters.bounds K _ _ L U M V hn
      have hLU : L < U := (div_lt_div_iff_of_pos_right hd).mpr (sub_lt_sub_right (hwidth 1) _)
      have hMV : M < V := (div_lt_div_iff_of_pos_right hd).mpr (sub_lt_sub_right (hwidth 2) _)
      have restore (q t w : ℝ) (he : (q - r * t) / (1 - r) = w) :
          q = r * t + (1 - r) * w := by
        have he' := (div_eq_iff hd.ne').mp he
        nlinarith only [he']
      refine ⟨T, r, L, U, M, V, hcap, hr, hr₁, hL₀, hU₁, hM₀, hV₁, hLU, hMV, ?_, ?_, hn⟩
      · funext i
        fin_cases i
        · exact hanchor
        · exact restore (lo 1) (T 1) L rfl
        · exact restore (lo 2) (T 2) M rfl
      · funext i
        fin_cases i
        · rfl
        · exact restore (hi 1) (T 1) U rfl
        · exact restore (hi 2) (T 2) V rfl
    · exact Or.inr ((OrientedCommonChord.tight_iff_of_opposite_vertices K hK hchord
        hbox lo hi hlo hhi hwidth).mp ⟨hsum, hcover⟩)
  · rintro (h | h)
    · obtain ⟨T, r, l, u, m, v, hcap, hr, hr₁, hl, hu, hm, hv, hlu, hmv, heL, heU, hn⟩ := h
      obtain ⟨hT₀, A, B, hA₀, hB₀, hbody⟩ := hcap
      rw [heL, heU]
      exact (TriangleContraction.tight_iff K T A B hbody hT₀ hA₀ hB₀ hbox hL hU
        r l u m v hr hr₁ hl hu hm hv hlu hmv).mpr hn
    · exact OrientedCommonChord.Normal.tight K (fun i => AffineMap.proj i) hbox lo hi h

end Plank.Convex.PlanarTight.AnchoredClassification

/-- info: 'Plank.Convex.PlanarTight.AnchoredClassification.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredClassification.tight_iff
