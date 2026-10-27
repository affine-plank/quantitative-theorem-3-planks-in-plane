/- An anchored equality cover has the apex/zero-base triangle geometry
or belongs to the common-extremal-segment branch. -/
module
public import Plank.Convex.PlanarTight.AnchoredLowerSumCap
public import Plank.Convex.PlanarTight.AnchoredMaximum
public import Plank.Convex.PlanarTight.AnchoredUpperSum
public import Plank.Convex.PlanarTight.OppositeVertices
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.AnchoredCapClassification

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

private theorem endpoints (K : Set E) (hK : Convex ℝ K) (W X Y : E →ᵃ[ℝ] ℝ)
    (H : TwoPlankClassification.Ranges K X Y)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, X x = X y → Y x = Y y → x = y)
    (hW : ∀ z ∈ K, 0 ≤ W z ∧ W z ≤ 1)
    (hface : {z | z ∈ K ∧ W z = 1}.Subsingleton)
    (T : E) (hT : T ∈ K) (hWT : W T = 1)
    (r : ℝ) (hr : 0 < r) (hr₁ : r < 1)
    (l u m v : ℝ) (h : TwoPlankClassification.Anchored K X Y l u m v)
    (hcover : ∀ z ∈ K, W z ≤ r ∨
      (r * X T + (1 - r) * l ≤ X z ∧ X z ≤ r * X T + (1 - r) * u) ∨
      (r * Y T + (1 - r) * m ≤ Y z ∧ Y z ≤ r * Y T + (1 - r) * v)) :
    AnchoredCapBody.Has K W T ∨
      l = 0 ∧ 0 < u ∧ u < 1 ∧
        ((m = 0 ∧ v = 1 - u ∧ ∀ z ∈ K, X z + Y z ≤ 1) ∨
          (m = u ∧ v = 1 ∧ ∀ z ∈ K, X z ≤ Y z)) := by
  obtain ⟨hl, hu, hu₁, c, hc, hc₁, hm, hv, hshape⟩ := h
  by_cases he₀ : c = 0
  · refine Or.inr ⟨hl, hu, hu₁, Or.inl ⟨?_, ?_, ?_⟩⟩
    · simpa only [he₀, mul_zero] using hm
    · simpa only [he₀, mul_zero, zero_add] using hv
    · intro z hz
      have hs := (hshape z hz).2
      rw [he₀] at hs
      nlinarith only [hs]
  by_cases he₁ : c = 1
  · refine Or.inr ⟨hl, hu, hu₁, Or.inr ⟨?_, ?_, ?_⟩⟩
    · simpa only [he₁, mul_one] using hm
    · rw [he₁] at hv
      linarith only [hv]
    · intro z hz
      simpa only [he₁, one_mul] using (hshape z hz).1
  apply Or.inl
  apply AnchoredCapBody.of_interior K hK W X Y H hinj hW hface T hT hWT c u r
    (lt_of_le_of_ne hc (Ne.symm he₀)) (lt_of_le_of_ne hc₁ he₁) hu hu₁ hr hr₁ hshape
  intro z hz
  have hv' : v = 1 - u + u * c := by rw [hv]; ring
  simpa only [hl, hm, hv', mul_zero, add_zero] using hcover z hz

private theorem flip_cover (x y z tx ty r l u m v : ℝ)
    (h : x ≤ r ∨ (r * tx + (1 - r) * l ≤ y ∧ y ≤ r * tx + (1 - r) * u) ∨
      (r * ty + (1 - r) * m ≤ z ∧ z ≤ r * ty + (1 - r) * v)) :
    x ≤ r ∨
      (r * (1 - tx) + (1 - r) * (1 - u) ≤ 1 - y ∧
        1 - y ≤ r * (1 - tx) + (1 - r) * (1 - l)) ∨
      (r * ty + (1 - r) * m ≤ z ∧ z ≤ r * ty + (1 - r) * v) := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨by nlinarith only [h.2], by nlinarith only [h.1]⟩)
  · exact Or.inr (Or.inr h)

abbrev Point := Fin 3 → ℝ

/-- Exhaustive apex/zero-base triangle or opposite-vertex reduction for
a positive equality cover with the first lower endpoint anchored at zero. -/
theorem cap_or_opposite_vertices (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hplane : ∀ z ∈ K, a * z 0 + b * z 1 + c * z 2 = d)
    (lo hi : Point) (hwidth : ∀ i, lo i < hi i) (hanchor : lo 0 = 0)
    (hcover : ∀ z ∈ K, ∃ i, lo i ≤ z i ∧ z i ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1)
    (T : Point) (hT : T ∈ K) (hT₀ : T 0 = 1) :
    AnchoredCapBody.Has K (AffineMap.proj 0) T ∨ OppositeVertices.Has K := by
  let X : Point →ᵃ[ℝ] ℝ := AffineMap.proj 1
  let Y : Point →ᵃ[ℝ] ℝ := AffineMap.proj 2
  have H : TwoPlankClassification.Ranges K X Y :=
    ⟨fun z hz => ⟨hbox z hz 1, hbox z hz 2⟩, hL 1, hU 1, hL 2, hU 2⟩
  have hW : ∀ z ∈ K, 0 ≤ (AffineMap.proj 0 : Point →ᵃ[ℝ] ℝ) z ∧
      (AffineMap.proj 0 : Point →ᵃ[ℝ] ℝ) z ≤ 1 := fun z hz => hbox z hz 0
  have hface : {z : Point | z ∈ K ∧ (AffineMap.proj 0 : Point →ᵃ[ℝ] ℝ) z = 1}.Subsingleton :=
    AnchoredMaximum.subsingleton K hK hbox hL hU a b c d ha hb hc hplane
      lo hi hwidth hanchor hcover hsum
  have hinj : ∀ x ∈ K, ∀ y ∈ K, X x = X y → Y x = Y y → x = y := by
    intro x hx y hy h₁ h₂
    change x 1 = y 1 at h₁
    change x 2 = y 2 at h₂
    have hp := hplane x hx
    have hq := hplane y hy
    rw [← h₁, ← h₂] at hq
    have h₀ : x 0 = y 0 := by nlinarith only [hp, hq, ha]
    funext i
    fin_cases i <;> assumption
  have hinjSwap : ∀ x ∈ K, ∀ y ∈ K, Y x = Y y → X x = X y → x = y :=
    fun x hx y hy h₁ h₂ => hinj x hx y hy h₂ h₁
  have hinjReflect : ∀ x ∈ K, ∀ y ∈ K,
      TwoPlankClassification.reflect X x = TwoPlankClassification.reflect X y →
      Y x = Y y → x = y := by
    intro x hx y hy h₁ h₂
    apply hinj x hx y hy _ h₂
    change 1 - X x = 1 - X y at h₁
    linarith only [h₁]
  have hinjSwapReflect : ∀ x ∈ K, ∀ y ∈ K,
      TwoPlankClassification.reflect Y x = TwoPlankClassification.reflect Y y →
      X x = X y → x = y := by
    intro x hx y hy h₁ h₂
    apply hinjSwap x hx y hy _ h₂
    change 1 - Y x = 1 - Y y at h₁
    linarith only [h₁]
  let r := hi 0
  have hr : 0 < r := by simpa only [hanchor] using hwidth 0
  have hr₁ : r < 1 := by
    have hs := hsum
    rw [Fin.sum_univ_three, hanchor, sub_zero] at hs
    have h₁ := hwidth 1
    have h₂ := hwidth 2
    change hi 0 < 1
    linarith only [hs, h₁, h₂]
  let L := (lo 1 - r * T 1) / (1 - r)
  let U := (hi 1 - r * T 1) / (1 - r)
  let M := (lo 2 - r * T 2) / (1 - r)
  let V := (hi 2 - r * T 2) / (1 - r)
  have restore (u t v : ℝ) (he : (u - r * t) / (1 - r) = v) :
      u = r * t + (1 - r) * v := by
    have hh := (div_eq_iff (sub_pos.mpr hr₁).ne').mp he
    nlinarith only [hh]
  have hbackL := restore (lo 1) (T 1) L rfl
  have hbackU := restore (hi 1) (T 1) U rfl
  have hbackM := restore (lo 2) (T 2) M rfl
  have hbackV := restore (hi 2) (T 2) V rfl
  have hcov : ∀ z ∈ K, z 0 ≤ r ∨
      (r * T 1 + (1 - r) * L ≤ z 1 ∧ z 1 ≤ r * T 1 + (1 - r) * U) ∨
      (r * T 2 + (1 - r) * M ≤ z 2 ∧ z 2 ≤ r * T 2 + (1 - r) * V) := by
    intro z hz
    obtain ⟨i, hil, hiu⟩ := hcover z hz
    fin_cases i
    · exact Or.inl hiu
    · change lo 1 ≤ z 1 at hil
      change z 1 ≤ hi 1 at hiu
      rw [hbackL] at hil
      rw [hbackU] at hiu
      exact Or.inr (Or.inl ⟨hil, hiu⟩)
    · change lo 2 ≤ z 2 at hil
      change z 2 ≤ hi 2 at hiu
      rw [hbackM] at hil
      rw [hbackV] at hiu
      exact Or.inr (Or.inr ⟨hil, hiu⟩)
  have lower (g : ℝ) (hg : 0 < g) (hg₁ : g < 1)
      (hs : ∀ z ∈ K, z 1 + z 2 ≤ 1)
      (hcov' : ∀ z ∈ K, z 0 ≤ r ∨
        (r * T 1 ≤ z 1 ∧ z 1 ≤ r * T 1 + (1 - r) * g) ∨
        (r * T 2 ≤ z 2 ∧ z 2 ≤ r * T 2 + (1 - r) * (1 - g))) :
      AnchoredCapBody.Has K (AffineMap.proj 0) T ∨ OppositeVertices.Has K := by
    rcases AnchoredLowerSumCap.cap_or_opposite_vertices K hK hbox hL hU a b c d ha hb hc
        hplane T hT hT₀ r g hr hr₁ hg hg₁ hs hcov' with ht | ⟨R, hR, W, hW, hR₁, hR₂, hW₁, hW₂, he⟩
    · exact Or.inl ht
    · exact Or.inr (OppositeVertices.cross K R W hR hW hR₁ hR₂ hW₁ hW₂ he)
  have upper (g : ℝ) (hg : 0 < g) (hg₁ : g < 1)
      (hs : ∀ z ∈ K, 1 ≤ z 1 + z 2)
      (hcov' : ∀ z ∈ K, z 0 ≤ r ∨
        (r * T 1 + (1 - r) * (1 - g) ≤ z 1 ∧ z 1 ≤ r * T 1 + (1 - r)) ∨
        (r * T 2 + (1 - r) * g ≤ z 2 ∧ z 2 ≤ r * T 2 + (1 - r))) :
      AnchoredCapBody.Has K (AffineMap.proj 0) T ∨ OppositeVertices.Has K := by
    obtain ⟨R, hR, W, hW, hR₁, hR₂, hW₁, hW₂, he⟩ :=
      AnchoredUpperSum.opposite_vertices K hK hbox hL a b c d ha hb hc hplane
        T hT hT₀ r g hr hr₁ hg hg₁ hs hcov'
    exact Or.inr (OppositeVertices.cross K W R hW hR hW₁ hW₂ hR₁ hR₂
      (he.imp And.symm And.symm))
  have ordered (hs : (∀ z ∈ K, z 1 ≤ z 2) ∨ (∀ z ∈ K, z 2 ≤ z 1)) :
      AnchoredCapBody.Has K (AffineMap.proj 0) T ∨ OppositeVertices.Has K :=
    Or.inr (OppositeVertices.of_order K hbox hL hU a b c d ha hb hc hplane hs)
  have hn : AnchoredNoQuadrilateral.Triangular K X Y L U M V :=
    AnchoredNoQuadrilateral.two_plank_triangular K hK hbox hL hU a b c d ha hb hc hplane
      lo hi hwidth hanchor hcover hsum T hT hT₀
  rcases hn with hn | hn | hn | hn
  · rcases endpoints K hK (AffineMap.proj 0) X Y H hinj hW hface T hT hT₀ r hr hr₁
        L U M V hn hcov with ht | ⟨hL₀, hg, hg₁, hs | hs⟩
    · exact Or.inl ht
    · apply lower U hg hg₁ hs.2.2
      intro z hz
      simpa only [hL₀, hs.1, hs.2.1, mul_zero, add_zero] using hcov z hz
    · exact ordered (Or.inl hs.2.2)
  · rcases endpoints K hK (AffineMap.proj 0) (TwoPlankClassification.reflect X) Y
        H.reflect hinjReflect hW hface T hT hT₀ r hr hr₁
        (1 - U) (1 - L) M V hn
        (fun z hz => flip_cover (z 0) (z 1) (z 2) (T 1) (T 2) r L U M V (hcov z hz))
        with ht | ⟨hU₁, hg, hg₁, hs | hs⟩
    · exact Or.inl ht
    · apply ordered ∘ Or.inr
      intro z hz
      have h := hs.2.2 z hz
      change 1 - z 1 + z 2 ≤ 1 at h
      linarith only [h]
    · have hUeq : U = 1 := by linarith only [hU₁]
      apply upper (1 - L) hg hg₁
      · intro z hz
        have h := hs.2.2 z hz
        change 1 - z 1 ≤ z 2 at h
        linarith only [h]
      · intro z hz
        simpa only [hUeq, hs.1, hs.2.1, sub_sub_cancel, mul_one] using hcov z hz
  · rcases endpoints K hK (AffineMap.proj 0) Y X H.swap hinjSwap hW hface T hT hT₀ r hr hr₁
        M V L U hn (fun z hz => (hcov z hz).imp id Or.symm)
        with ht | ⟨hM₀, hg, hg₁, hs | hs⟩
    · exact Or.inl ht
    · apply lower (1 - V) (sub_pos.mpr hg₁) (by linarith only [hg])
      · intro z hz
        have h := hs.2.2 z hz
        change z 2 + z 1 ≤ 1 at h
        linarith only [h]
      · intro z hz
        simpa only [hM₀, hs.1, hs.2.1, mul_zero, add_zero, sub_sub_cancel] using hcov z hz
    · exact ordered (Or.inr hs.2.2)
  · rcases endpoints K hK (AffineMap.proj 0) (TwoPlankClassification.reflect Y) X
        H.swap.reflect hinjSwapReflect hW hface T hT hT₀ r hr hr₁
        (1 - V) (1 - M) L U hn
        (fun z hz => flip_cover (z 0) (z 2) (z 1) (T 2) (T 1) r M V L U
          ((hcov z hz).imp id Or.symm))
        with ht | ⟨hV₁, hg, hg₁, hs | hs⟩
    · exact Or.inl ht
    · apply ordered ∘ Or.inl
      intro z hz
      have h := hs.2.2 z hz
      change 1 - z 2 + z 1 ≤ 1 at h
      linarith only [h]
    · have hVeq : V = 1 := by linarith only [hV₁]
      apply upper M (by linarith only [hg₁]) (by linarith only [hg])
      · intro z hz
        have h := hs.2.2 z hz
        change 1 - z 2 ≤ z 1 at h
        linarith only [h]
      · intro z hz
        simpa only [hVeq, hs.1, hs.2.1, mul_one] using hcov z hz

end Plank.Convex.PlanarTight.AnchoredCapClassification

/-- info: 'Plank.Convex.PlanarTight.AnchoredCapClassification.cap_or_opposite_vertices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.AnchoredCapClassification.cap_or_opposite_vertices
