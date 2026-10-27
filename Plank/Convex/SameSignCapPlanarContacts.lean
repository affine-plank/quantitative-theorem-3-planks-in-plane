/- Six same-sign pair contacts in a positive plane force the central
separator intervals, and hence a strictly positive cycle gap. -/
module
public import Plank.Convex.SameSignCapSingleCorner
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Plank.Convex.SameSignCapAlgebra Plank.Convex.SameSignCapProduct
open Plank.Convex.SameSignCapSingleCorner
namespace Plank.Convex.SameSignCapPlanarContacts

def lowerContact (δ : ℝ) (i : Fin 3) : Point := fun j => if j = i then δ else 0
def upperContact (w : Point) (τ : ℝ) (i : Fin 3) : Point := fun j => w j - lowerContact τ i j

theorem sum_cycle (x : Point) (i : Fin 3) : (∑ j, x j) = x i + x (next i) + x (prev i) := by
  exact SameSignCapAlgebra.sum_cycle x i

theorem L_self (δ : ℝ) (i : Fin 3) : lowerContact δ i i = δ := by simp [lowerContact]
theorem L_next (δ : ℝ) (i : Fin 3) : lowerContact δ i (next i) = 0 := by
  fin_cases i <;> simp [lowerContact, next]
theorem L_prev (δ : ℝ) (i : Fin 3) : lowerContact δ i (prev i) = 0 := by
  fin_cases i <;> simp [lowerContact, prev]
theorem L_prev_next (δ : ℝ) (i : Fin 3) : lowerContact δ (prev i) (next i) = 0 := by
  fin_cases i <;> simp [lowerContact, prev, next]
theorem L_next_prev (δ : ℝ) (i : Fin 3) : lowerContact δ (next i) (prev i) = 0 := by
  fin_cases i <;> simp [lowerContact, prev, next]

theorem slope_one (u v t c : ℝ) (hu : 0 < u) (hv : 0 < v) (ht : u + v ≤ t)
    (h1 : t ≤ u + c * v) (h2 : c * t ≤ u + c * v) : c = 1 := by
  have hc : 1 ≤ c := by nlinarith only [hv, ht, h1]
  have hprod := mul_le_mul_of_nonneg_left ht (zero_le_one.trans hc)
  have hc' : c ≤ 1 := by nlinarith only [hu, hprod, h2]
  exact le_antisymm hc' hc

/-- A noncentral offset would force one pair separator to have slope one,
contradicting a coordinate witness beyond the covering window. -/
theorem offsets_gt_widths (K : Set Point) (w a b : Point) (δ τ : ℝ)
    (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = δ + τ)
    (hplane : ∀ x ∈ K, (∑ i, x i) = δ)
    (hL : ∀ i, lowerContact δ i ∈ K) (hU : ∀ i, upperContact w τ i ∈ K)
    (hlow : ∀ i, ∃ x ∈ K, x i < 0) (hhigh : ∀ i, ∃ x ∈ K, w i < x i)
    (ha : ∀ i, ∀ x ∈ K, x i + a i * x (next i) ≤ w i + a i * w (next i))
    (hb : ∀ i, ∀ x ∈ K, 0 ≤ x i + b i * x (next i)) :
    (∀ i, w i < δ) ∧ (∀ i, w i < τ) := by
  constructor
  · intro i
    by_contra hn
    have hi := le_of_not_gt hn
    have hsum' := hsum
    rw [sum_cycle w i] at hsum'
    have ht : w (next i) + w (prev i) ≤ τ := by linarith only [hsum', hi]
    have h1 := hb (next i) (upperContact w τ (next i)) (hU (next i))
    have h2 := hb (next i) (upperContact w τ (prev i)) (hU (prev i))
    simp only [upperContact, next_next, L_self, L_next_prev, L_prev_next] at h1 h2
    have hone : b (next i) = 1 := slope_one _ _ _ _ (hw _) (hw _) ht
      (by linarith only [h1]) (by nlinarith only [h2])
    obtain ⟨x, hx, hxi⟩ := hhigh i
    have hrow := hb (next i) x hx
    rw [hone, one_mul, next_next] at hrow
    have hxplane := hplane x hx
    rw [sum_cycle x i] at hxplane
    linarith only [hrow, hxplane, hxi, hi]
  · intro i
    by_contra hn
    have hi := le_of_not_gt hn
    have hsum' := hsum
    rw [sum_cycle w i] at hsum'
    have ht : w (next i) + w (prev i) ≤ δ := by linarith only [hsum', hi]
    have h1 := ha (next i) (lowerContact δ (next i)) (hL (next i))
    have h2 := ha (next i) (lowerContact δ (prev i)) (hL (prev i))
    simp only [next_next, L_self, L_next_prev, L_prev_next, mul_zero, add_zero, zero_add] at h1 h2
    have hone : a (next i) = 1 := slope_one _ _ _ _ (hw _) (hw _) ht h1 h2
    obtain ⟨x, hx, hxi⟩ := hlow i
    have hrow := ha (next i) x hx
    rw [hone, one_mul, one_mul, next_next] at hrow
    have hxplane := hplane x hx
    rw [sum_cycle x i] at hxplane
    linarith only [hrow, hxplane, hxi, hi, hsum']


theorem L_next_self (δ : ℝ) (i : Fin 3) : lowerContact δ (next i) i = 0 := by
  fin_cases i <;> simp [lowerContact, next]

/-- Evaluating each supporting row at the two opposite contacts bounds its slope. -/
theorem intervals_of_contacts (K : Set Point) (w a b : Point) (δ τ : ℝ)
    (hw : ∀ i, 0 < w i) (hδ : ∀ i, w i < δ) (hτ : ∀ i, w i < τ)
    (hL : ∀ i, lowerContact δ i ∈ K) (hU : ∀ i, upperContact w τ i ∈ K)
    (ha : ∀ i, ∀ x ∈ K, x i + a i * x (next i) ≤ w i + a i * w (next i))
    (hb : ∀ i, ∀ x ∈ K, 0 ≤ x i + b i * x (next i)) :
    (∀ i, (δ - w i) / w (next i) ≤ a i ∧ a i ≤ w i / (δ - w (next i))) ∧
    (∀ i, (τ - w i) / w (next i) ≤ b i ∧ b i ≤ w i / (τ - w (next i))) := by
  constructor
  · intro i
    have h1 := ha i (lowerContact δ i) (hL i)
    have h2 := ha i (lowerContact δ (next i)) (hL (next i))
    simp only [L_self, L_next, L_next_self, mul_zero, add_zero, zero_add] at h1 h2
    constructor
    · apply (div_le_iff₀ (hw _)).mpr
      linarith only [h1]
    · apply (le_div_iff₀ (sub_pos.mpr (hδ _))).mpr
      nlinarith only [h2]
  · intro i
    have h1 := hb i (upperContact w τ i) (hU i)
    have h2 := hb i (upperContact w τ (next i)) (hU (next i))
    simp only [upperContact, L_self, L_next, L_next_self, sub_zero] at h1 h2
    constructor
    · apply (div_le_iff₀ (hw _)).mpr
      linarith only [h1]
    · apply (le_div_iff₀ (sub_pos.mpr (hτ _))).mpr
      nlinarith only [h2]

theorem cycleGap_pos_of_contacts (K : Set Point) (w a b : Point) (δ τ : ℝ)
    (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = δ + τ)
    (hplane : ∀ x ∈ K, (∑ i, x i) = δ)
    (hL : ∀ i, lowerContact δ i ∈ K) (hU : ∀ i, upperContact w τ i ∈ K)
    (hlow : ∀ i, ∃ x ∈ K, x i < 0) (hhigh : ∀ i, ∃ x ∈ K, w i < x i)
    (ha : ∀ i, ∀ x ∈ K, x i + a i * x (next i) ≤ w i + a i * w (next i))
    (hb : ∀ i, ∀ x ∈ K, 0 ≤ x i + b i * x (next i)) :
    0 < cycleGap a b := by
  obtain ⟨hδ, hτ⟩ := offsets_gt_widths K w a b δ τ hw hsum hplane hL hU hlow hhigh ha hb
  obtain ⟨ha', hb'⟩ := intervals_of_contacts K w a b δ τ hw hδ hτ hL hU ha hb
  exact cycleGap_pos_of_intervals w a b δ τ hsum hδ hτ ha' hb'

theorem cycleGap_nonneg_of_contacts (K : Set Point) (w a b : Point) (δ τ : ℝ)
    (hw : ∀ i, 0 < w i) (hsum : (∑ i, w i) = δ + τ)
    (hplane : ∀ x ∈ K, (∑ i, x i) = δ)
    (hL : ∀ i, lowerContact δ i ∈ K) (hU : ∀ i, upperContact w τ i ∈ K)
    (hlow : ∀ i, ∃ x ∈ K, x i < 0) (hhigh : ∀ i, ∃ x ∈ K, w i < x i)
    (ha : ∀ i, ∀ x ∈ K, x i + a i * x (next i) ≤ w i + a i * w (next i))
    (hb : ∀ i, ∀ x ∈ K, 0 ≤ x i + b i * x (next i)) :
    0 ≤ cycleGap a b :=
  (cycleGap_pos_of_contacts K w a b δ τ hw hsum hplane hL hU hlow hhigh ha hb).le


def scaleSlope (c a : Point) : Point := fun i => c i * a i / c (next i)

/-- Positive diagonal changes of coordinates preserve the cycle gap. -/
theorem cycleGap_scale (c a b : Point) (hc : ∀ i, c i ≠ 0) :
    cycleGap (scaleSlope c a) (scaleSlope c b) = cycleGap a b := by
  simp only [gap_product, ProductGap.gap, scaleSlope, Fin.prod_univ_three, next,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  field_simp [hc 0, hc 1, hc 2]


theorem index_cases (i j : Fin 3) : j = i ∨ j = next i ∨ j = prev i := by
  exact SameSignCapAlgebra.index_cases i j

theorem eq_L (x : Point) (δ : ℝ) (i : Fin 3) (hsum : (∑ j, x j) = δ)
    (hn : x (next i) = 0) (hp : x (prev i) = 0) : x = lowerContact δ i := by
  have hi : x i = δ := by rw [sum_cycle x i, hn, hp, add_zero, add_zero] at hsum; exact hsum
  funext j
  rcases index_cases i j with rfl | rfl | rfl
  · rw [L_self, hi]
  · rw [L_next, hn]
  · rw [L_prev, hp]

theorem eq_U (x w : Point) (δ τ : ℝ) (i : Fin 3) (hsum : (∑ j, x j) = δ)
    (hw : (∑ j, w j) = δ + τ)
    (hn : x (next i) = w (next i)) (hp : x (prev i) = w (prev i)) : x = upperContact w τ i := by
  have hi : x i = w i - τ := by
    rw [sum_cycle x i, hn, hp] at hsum
    rw [sum_cycle w i] at hw
    linarith only [hsum, hw]
  funext j
  rcases index_cases i j with rfl | rfl | rfl
  · simp only [upperContact, L_self, hi]
  · simp only [upperContact, L_next, sub_zero, hn]
  · simp only [upperContact, L_prev, sub_zero, hp]

def rescale (c lo : Point) (x : Point) : Point := fun i => c i * (x i - lo i)

theorem rescale_sum (c lo x : Point) :
    (∑ i, rescale c lo x i) = (∑ i, c i * x i) - ∑ i, c i * lo i := by
  simp [rescale, mul_sub, Finset.sum_sub_distrib]

theorem rescale_pair (c a lo x : Point) (hc : ∀ i, c i ≠ 0) (i : Fin 3) :
    rescale c lo x i + scaleSlope c a i * rescale c lo x (next i) =
      c i * ((x i + a i * x (next i)) - (lo i + a i * lo (next i))) := by
  dsimp [rescale, scaleSlope]
  field_simp [hc (next i)]
  ring

/-- Geometric cycle-gap criterion in the original coordinates. Compactness
and convexity are only needed earlier to obtain the six pair contacts. -/
theorem cycleGap_pos_of_pair_contacts (K : Set Point) (lo hi a b c : Point) (D : ℝ)
    (hc : ∀ i, 0 < c i) (hwidth : ∀ i, lo i < hi i)
    (hplane : ∀ x ∈ K, (∑ i, c i * x i) = D)
    (hL : ∀ i, ∃ x ∈ K, x i = lo i ∧ x (next i) = lo (next i))
    (hU : ∀ i, ∃ x ∈ K, x i = hi i ∧ x (next i) = hi (next i))
    (hlow : ∀ i, ∃ x ∈ K, x i < lo i) (hhigh : ∀ i, ∃ x ∈ K, hi i < x i)
    (ha : UpperSupports K hi a) (hb : LowerSupports K lo b) :
    0 < cycleGap a b := by
  let f := rescale c lo
  let T := f '' K
  let w := f hi
  let δ := D - ∑ i, c i * lo i
  let τ := (∑ i, w i) - δ
  have hsum : (∑ i, w i) = δ + τ := by dsimp [τ]; ring
  have hc0 : ∀ i, c i ≠ 0 := fun i => (hc i).ne'
  have hsumf (x : Point) (hx : x ∈ K) : (∑ i, f x i) = δ := by
    dsimp [f, δ]
    rw [rescale_sum, hplane x hx]
  have hT : ∀ x ∈ T, (∑ i, x i) = δ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsumf x hx
  have hLT : ∀ i, lowerContact δ i ∈ T := by
    intro i
    obtain ⟨x, hx, hn, hp⟩ := hL (next i)
    rw [next_next] at hp
    have he : f x = lowerContact δ i := eq_L (f x) δ i (hsumf x hx)
      (by simp [f, rescale, hn]) (by simp [f, rescale, hp])
    rw [← he]
    exact Set.mem_image_of_mem f hx
  have hUT : ∀ i, upperContact w τ i ∈ T := by
    intro i
    obtain ⟨x, hx, hn, hp⟩ := hU (next i)
    rw [next_next] at hp
    have he : f x = upperContact w τ i := eq_U (f x) w δ τ i (hsumf x hx) hsum
      (by simp [f, w, rescale, hn]) (by simp [f, w, rescale, hp])
    rw [← he]
    exact Set.mem_image_of_mem f hx
  have hlowT : ∀ i, ∃ x ∈ T, x i < 0 := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hlow i
    exact ⟨f x, Set.mem_image_of_mem f hx, mul_neg_of_pos_of_neg (hc i) (sub_neg.mpr hxi)⟩
  have hhighT : ∀ i, ∃ x ∈ T, w i < x i := by
    intro i
    obtain ⟨x, hx, hxi⟩ := hhigh i
    refine ⟨f x, Set.mem_image_of_mem f hx, ?_⟩
    exact mul_lt_mul_of_pos_left (sub_lt_sub_right hxi _) (hc i)
  have haT : ∀ i, ∀ x ∈ T, x i + scaleSlope c a i * x (next i) ≤
      w i + scaleSlope c a i * w (next i) := by
    rintro i _ ⟨x, hx, rfl⟩
    change rescale c lo x i + scaleSlope c a i * rescale c lo x (next i) ≤
      rescale c lo hi i + scaleSlope c a i * rescale c lo hi (next i)
    rw [rescale_pair c a lo x hc0, rescale_pair c a lo hi hc0]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right (ha i x hx) _) (hc i).le
  have hbT : ∀ i, ∀ x ∈ T, 0 ≤ x i + scaleSlope c b i * x (next i) := by
    rintro i _ ⟨x, hx, rfl⟩
    change 0 ≤ rescale c lo x i + scaleSlope c b i * rescale c lo x (next i)
    rw [rescale_pair c b lo x hc0]
    exact mul_nonneg (hc i).le (sub_nonneg.mpr (hb i x hx))
  have hg := cycleGap_pos_of_contacts T w (scaleSlope c a) (scaleSlope c b) δ τ
    (fun i => mul_pos (hc i) (sub_pos.mpr (hwidth i))) hsum hT hLT hUT hlowT hhighT haT hbT
  rwa [cycleGap_scale c a b hc0] at hg

theorem cycleGap_nonneg_of_pair_contacts (K : Set Point) (lo hi a b c : Point) (D : ℝ)
    (hc : ∀ i, 0 < c i) (hwidth : ∀ i, lo i < hi i)
    (hplane : ∀ x ∈ K, (∑ i, c i * x i) = D)
    (hL : ∀ i, ∃ x ∈ K, x i = lo i ∧ x (next i) = lo (next i))
    (hU : ∀ i, ∃ x ∈ K, x i = hi i ∧ x (next i) = hi (next i))
    (hlow : ∀ i, ∃ x ∈ K, x i < lo i) (hhigh : ∀ i, ∃ x ∈ K, hi i < x i)
    (ha : UpperSupports K hi a) (hb : LowerSupports K lo b) :
    0 ≤ cycleGap a b :=
  (cycleGap_pos_of_pair_contacts K lo hi a b c D hc hwidth hplane hL hU hlow hhigh ha hb).le

end Plank.Convex.SameSignCapPlanarContacts

/-- info: 'Plank.Convex.SameSignCapPlanarContacts.cycleGap_pos_of_pair_contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.SameSignCapPlanarContacts.cycleGap_pos_of_pair_contacts
