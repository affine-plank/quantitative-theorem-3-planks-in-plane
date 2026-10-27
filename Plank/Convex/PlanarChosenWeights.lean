/- Ordered finite tangencies imply the six-support width criterion. -/
module
public import Plank.Convex.FinitePairSupports
public import Plank.Convex.PlanarWidthCriterion
@[expose] public section
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Plank.Convex.PlanarChosenSupports

abbrev Point := Fin 3 → ℝ

/-- Adjacent chosen supports have ordered tangencies whenever their slope
inequality is not immediate from comparison with one. -/
theorem chosen_weight {ι : Type*} (x y z : ι → ℝ)
    (lx ly hy hz D a b : ℝ) (horder : ly ≤ hy)
    (hplane : ∀ v, x v + y v + z v = D)
    (ha : Chosen (fun v => y v - hy) (fun v => z v - hz) a)
    (hb : Chosen (fun v => lx - x v) (fun v => ly - y v) b) :
    a * (1 - b) ≤ 1 := by
  by_cases ha₁ : a ≤ 1
  · nlinarith only [ha₁, mul_pos ha.1 hb.1]
  by_cases hb₁ : 1 ≤ b
  · have hm := mul_nonneg ha.1.le (sub_nonneg.mpr hb₁)
    nlinarith only [hm]
  obtain ⟨p, hp, hep⟩ := ha.2.2.1 (lt_of_not_ge ha₁)
  obtain ⟨q, hq, heq⟩ := hb.2.2.2 (lt_of_not_ge hb₁)
  have hu := ha.2.1 q
  have hl := hb.2.1 p
  dsimp at hp hq hep heq hu hl
  apply PlanarWidthCriterion.contact_slope_bound (x p) (y p) (z p)
    (x q) (y q) (z q) a b (by linarith only [hp, hq, horder]) ha.1.le
  · nlinarith only [hu, hep]
  · nlinarith only [hl, heq]
  · linarith only [hplane p, hplane q]

theorem weights_of_chosen {ι : Type*} (X : ι → Point)
    (lo hi a b : Point) (D : ℝ) (horder : ∀ i, lo i ≤ hi i)
    (hplane : ∀ v, ∑ i, X v i = D)
    (ha : ∀ i, Chosen (fun v => X v i - hi i)
      (fun v => X v (i + 1) - hi (i + 1)) (a i))
    (hb : ∀ i, Chosen (fun v => lo i - X v i)
      (fun v => lo (i + 1) - X v (i + 1)) (b i)) :
    (∀ i, a (i + 1) * (1 - b i) ≤ 1) ∧
    (∀ i, b (i + 1) * (1 - a i) ≤ 1) := by
  have hsum (v : ι) (i : Fin 3) : X v i + X v (i + 1) + X v (i + 2) = D := by
    have h := hplane v
    simp only [Fin.sum_univ_three] at h
    fin_cases i <;> dsimp <;> linarith only [h]
  have hn (i : Fin 3) : (i + 1) + 1 = i + 2 := by fin_cases i <;> rfl
  constructor
  · intro i
    apply chosen_weight (fun v => X v i) (fun v => X v (i + 1))
      (fun v => X v (i + 2)) (lo i) (lo (i + 1)) (hi (i + 1)) (hi (i + 2)) D
      (a (i + 1)) (b i) (horder _) (fun v => hsum v i)
    · simpa only [hn] using ha (i + 1)
    · exact hb i
  · intro i
    apply chosen_weight (fun v => -X v i) (fun v => -X v (i + 1))
      (fun v => -X v (i + 2)) (-hi i) (-hi (i + 1)) (-lo (i + 1)) (-lo (i + 2)) (-D)
      (b (i + 1)) (a i) (neg_le_neg (horder _))
      (fun v => by linarith only [hsum v i])
    · simpa only [hn, sub_neg_eq_add, neg_add_eq_sub] using hb (i + 1)
    · simpa only [neg_sub_neg] using ha i

/-- Chosen tangencies give the slope slacks used by the support budgets. -/
theorem width_of_chosen {ι : Type*} (X : ι → Point)
    (lo hi R a b : Point) (D : ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hR : ∀ i, 0 < R i)
    (hplane : ∀ v, ∑ i, X v i = D)
    (hzero : ∀ i, ∃ v, X v i = 0) (hmax : ∀ i, ∃ v, X v i = R i)
    (ha : ∀ i, PlanarChosenSupports.Chosen (fun v => X v i - hi i)
      (fun v => X v (i + 1) - hi (i + 1)) (a i))
    (hb : ∀ i, PlanarChosenSupports.Chosen (fun v => lo i - X v i)
      (fun v => lo (i + 1) - X v (i + 1)) (b i)) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  obtain ⟨hab, hba⟩ := PlanarChosenSupports.weights_of_chosen X lo hi a b D horder hplane ha hb
  apply PlanarWidthCriterion.width_bound X lo hi R a b
    (fun i => (ha i).1.le) (fun i => (hb i).1.le) horder hR hzero hmax
  · intro i v
    have h := (ha i).2.1 v
    dsimp at h
    nlinarith only [h]
  · intro i v
    have h := (hb i).2.1 v
    dsimp at h
    nlinarith only [h]
  · exact hab
  · exact hba

end Plank.Convex.PlanarChosenSupports
