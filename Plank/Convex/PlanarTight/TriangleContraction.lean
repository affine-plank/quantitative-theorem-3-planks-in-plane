/- A triangle cut parallel to its opposite edge is exactly a homothetic
copy. Tight two-plank windows on that copy give explicit three-plank families. -/
module
public import Mathlib.Analysis.Convex.Join
public import Plank.Convex.PlanarTight.AnchoredReduction
public import Plank.Convex.PlanarTight.AnchoredCorner
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.TriangleContraction

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Every point above a cut parallel to the opposite triangle edge has
a preimage in the original triangle under contraction towards its apex. -/
theorem cap_preimage (K : Set E) (T A B : E) (hK : K = convexHull ℝ {T, A, B})
    (X : E →ᵃ[ℝ] ℝ) (hT : X T = 1) (hA : X A = 0) (hB : X B = 0)
    (r : ℝ) (hr : r < 1) (z : E) (hz : z ∈ K) (hcut : r ≤ X z) :
    ∃ w ∈ K, z = r • T + (1 - r) • w := by
  have hconv : Convex ℝ K := hK.symm ▸ convex_convexHull ℝ _
  have hTK : T ∈ K := by rw [hK]; exact subset_convexHull ℝ _ (by simp)
  have hAK : A ∈ K := by rw [hK]; exact subset_convexHull ℝ _ (by simp)
  have hBK : B ∈ K := by rw [hK]; exact subset_convexHull ℝ _ (by simp)
  have hz' : z ∈ convexJoin ℝ {T} (segment ℝ A B) := by
    rw [convexJoin_singleton_segment, ← hK]
    exact hz
  obtain ⟨T', hT', C, hC, s, t, hs, ht, hst, he⟩ := mem_convexJoin.mp hz'
  have hTeq : T' = T := Set.mem_singleton_iff.mp hT'
  subst T'
  have hCK : C ∈ K := hconv.segment_subset hAK hBK hC
  have hXC : X C = 0 := by
    obtain ⟨u, v, _, _, huv, heC⟩ := hC
    have hv : v = 1 - u := by linarith only [huv]
    rw [← heC, hv, AnchoredCorner.map_contract, hA, hB]
    ring
  have ht' : t = 1 - s := by linarith only [hst]
  have hXz : X z = s := by
    rw [← he, ht', AnchoredCorner.map_contract, hT, hXC]
    ring
  have hsr : 0 ≤ s - r := by rw [hXz] at hcut; exact sub_nonneg.mpr hcut
  let u := (s - r) / (1 - r)
  let v := t / (1 - r)
  have hu : 0 ≤ u := div_nonneg hsr (sub_pos.mpr hr).le
  have hv : 0 ≤ v := div_nonneg ht (sub_pos.mpr hr).le
  have huv : u + v = 1 := by
    dsimp [u, v]
    rw [← add_div, div_eq_one_iff_eq (sub_pos.mpr hr).ne']
    linarith only [hst]
  refine ⟨u • T + v • C, hconv hTK hCK hu hv huv, ?_⟩
  have h₁ : r + (1 - r) * u = s := by
    dsimp [u]
    rw [mul_div_cancel₀ _ (sub_pos.mpr hr).ne']
    ring
  have h₂ : (1 - r) * v = t := by
    dsimp [v]
    exact mul_div_cancel₀ t (sub_pos.mpr hr).ne'
  rw [← he, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul, h₁, h₂]

abbrev Point := Fin 3 → ℝ

def lower (T : Point) (r l m : ℝ) : Point :=
  ![0, r * T 1 + (1 - r) * l, r * T 2 + (1 - r) * m]

def upper (T : Point) (r u v : ℝ) : Point :=
  ![r, r * T 1 + (1 - r) * u, r * T 2 + (1 - r) * v]

/-- Complete window classification for a triangle with the first
coordinate equal to one at its apex and zero on its opposite edge.
The remaining two windows are the displayed homothetic images of any
of the explicit two-plank normal families. -/
theorem tight_iff (K : Set Point) (T A B : Point)
    (hK : K = convexHull ℝ {T, A, B})
    (hT : T 0 = 1) (hA : A 0 = 0) (hB : B 0 = 0)
    (hbox : ∀ z ∈ K, ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hL : ∀ i, ∃ z ∈ K, z i = 0) (hU : ∀ i, ∃ z ∈ K, z i = 1)
    (r l u m v : ℝ) (hr : 0 < r) (hr₁ : r < 1)
    (hl : 0 ≤ l) (hu : u ≤ 1) (hm : 0 ≤ m) (hv : v ≤ 1)
    (hlu : l < u) (hmv : m < v) :
    ((∑ i, (upper T r u v i - lower T r l m i)) = 1 ∧
      ∀ z ∈ K, ∃ i, lower T r l m i ≤ z i ∧ z i ≤ upper T r u v i) ↔
      TwoPlankClassification.Normal K (AffineMap.proj 1) (AffineMap.proj 2) l u m v := by
  have hconv : Convex ℝ K := hK.symm ▸ convex_convexHull ℝ _
  have hTK : T ∈ K := by rw [hK]; exact subset_convexHull ℝ _ (by simp)
  have hd : 0 < 1 - r := sub_pos.mpr hr₁
  have H : TwoPlankClassification.Ranges K (AffineMap.proj 1) (AffineMap.proj 2) :=
    ⟨fun z hz => ⟨hbox z hz 1, hbox z hz 2⟩, hL 1, hU 1, hL 2, hU 2⟩
  constructor
  · rintro ⟨hsum, hcover⟩
    have hwidth : ∀ i, lower T r l m i < upper T r u v i := by
      intro i
      fin_cases i
      · exact hr
      · exact add_lt_add_right (mul_lt_mul_of_pos_left hlu hd) _
      · exact add_lt_add_right (mul_lt_mul_of_pos_left hmv hd) _
    have hn := AnchoredReduction.two_plank_normal K hconv hbox hL hU
      (lower T r l m) (upper T r u v) hwidth rfl hcover hsum T hTK hT
    have pull (q t : ℝ) : (r * t + (1 - r) * q - r * t) / (1 - r) = q := by
      apply (div_eq_iff hd.ne').mpr
      ring
    change TwoPlankClassification.Normal K (AffineMap.proj 1) (AffineMap.proj 2)
      ((r * T 1 + (1 - r) * l - r * T 1) / (1 - r))
      ((r * T 1 + (1 - r) * u - r * T 1) / (1 - r))
      ((r * T 2 + (1 - r) * m - r * T 2) / (1 - r))
      ((r * T 2 + (1 - r) * v - r * T 2) / (1 - r)) at hn
    simpa only [pull] using hn
  · intro hn
    obtain ⟨hsum, hcover⟩ := (TwoPlankClassification.tight_iff K hconv _ _ H
      l u m v hl hu hm hv hlu hmv).mpr hn
    refine ⟨?_, ?_⟩
    · rw [Fin.sum_univ_three]
      change (r - 0) + (r * T 1 + (1 - r) * u - (r * T 1 + (1 - r) * l)) +
        (r * T 2 + (1 - r) * v - (r * T 2 + (1 - r) * m)) = 1
      calc
        _ = r + (1 - r) * ((u - l) + (v - m)) := by ring
        _ = 1 := by rw [hsum]; ring
    · intro z hz
      by_cases hcut : z 0 ≤ r
      · exact ⟨0, (hbox z hz 0).1, hcut⟩
      obtain ⟨w, hw, he⟩ := cap_preimage K T A B hK (AffineMap.proj 0)
        hT hA hB r hr₁ z hz (le_of_not_ge hcut)
      have heval (i : Fin 3) : z i = r * T i + (1 - r) * w i := by
        rw [he]
        rfl
      rcases hcover w hw with h | h
      · refine ⟨1, ?_, ?_⟩
        · change r * T 1 + (1 - r) * l ≤ z 1
          rw [heval]
          exact add_le_add_right (mul_le_mul_of_nonneg_left h.1 hd.le) _
        · change z 1 ≤ r * T 1 + (1 - r) * u
          rw [heval]
          exact add_le_add_right (mul_le_mul_of_nonneg_left h.2 hd.le) _
      · refine ⟨2, ?_, ?_⟩
        · change r * T 2 + (1 - r) * m ≤ z 2
          rw [heval]
          exact add_le_add_right (mul_le_mul_of_nonneg_left h.1 hd.le) _
        · change z 2 ≤ r * T 2 + (1 - r) * v
          rw [heval]
          exact add_le_add_right (mul_le_mul_of_nonneg_left h.2 hd.le) _

end Plank.Convex.PlanarTight.TriangleContraction

/-- info: 'Plank.Convex.PlanarTight.TriangleContraction.cap_preimage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TriangleContraction.cap_preimage

/-- info: 'Plank.Convex.PlanarTight.TriangleContraction.tight_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TriangleContraction.tight_iff
