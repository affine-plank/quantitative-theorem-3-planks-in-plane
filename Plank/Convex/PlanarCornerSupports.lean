/- Exact corner contacts give the six-support width bound. -/
module
public import Plank.Convex.PlanarWidthCriterion
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.PlanarSixCellSupports
open PlanarWidthCriterion

/-- A positive pair support turns a weak corner witness into an exact corner. -/
theorem pair_contact {ι : Type*} (X : ι → Triple) (h a : Triple)
    (ha : ∀ i, 0 < a i)
    (hs : ∀ i v, X v i + a i * X v (i+1) ≤ h i + a i * h (i+1))
    (v : ι) (i j : Fin 3) (hij : i ≠ j)
    (hi : h i ≤ X v i) (hj : h j ≤ X v j) :
    X v i = h i ∧ X v j = h j := by
  have adj (k : Fin 3) (hk : h k ≤ X v k) (hl : h (k+1) ≤ X v (k+1)) :
      X v k = h k ∧ X v (k+1) = h (k+1) := by
    have hp := hs k v
    have hh := mul_le_mul_of_nonneg_left hl (ha k).le
    constructor
    · linarith only [hp,hh,hk]
    · apply le_antisymm _ hl
      apply (mul_le_mul_iff_right₀ (ha k)).mp
      linarith only [hp,hk]
  have cyclic : j = i+1 ∨ i = j+1 := by omega
  rcases cyclic with rfl | h
  · exact adj i hi hj
  · subst i
    exact (adj j hj hi).symm

/-- Actual upper and lower corner contacts give the slope inequalities for
arbitrary positive supports. No nearest-one choice or finite extremizer set. -/
theorem width_bound_of_corner_contacts {ι : Type*} (X : ι → Triple)
    (lo hi R a b : Triple) (D : ℝ)
    (ho : ∀ i, lo i < hi i) (hR : ∀ i, 0 < R i)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hp : ∀ v, ∑ i, X v i = D)
    (hzero : ∀ i, ∃ v, X v i = 0) (hmax : ∀ i, ∃ v, X v i = R i)
    (hu : ∀ i v, X v i + a i * X v (i+1) ≤ hi i + a i * hi (i+1))
    (hl : ∀ i v, lo i + b i * lo (i+1) ≤ X v i + b i * X v (i+1))
    (huc : ∀ i, ∃ v, X v i = hi i ∧ X v (i+1) = hi (i+1))
    (hlc : ∀ i, ∃ v, X v i = lo i ∧ X v (i+1) = lo (i+1)) :
    1 ≤ ∑ i, (hi i-lo i)/R i := by
  have weights (Y : ι → Triple) (l u A B : Triple) (d : ℝ)
      (ho : ∀ i, l i < u i) (hA : ∀ i, 0 < A i)
      (hp : ∀ v, ∑ i, Y v i = d)
      (hu : ∀ i v, Y v i + A i * Y v (i+1) ≤ u i + A i * u (i+1))
      (hl : ∀ i v, l i + B i * l (i+1) ≤ Y v i + B i * Y v (i+1))
      (huc : ∀ i, ∃ v, Y v i = u i ∧ Y v (i+1) = u (i+1))
      (hlc : ∀ i, ∃ v, Y v i = l i ∧ Y v (i+1) = l (i+1)) :
      ∀ i, A (i+1)*(1-B i) ≤ 1 := by
    intro i
    obtain ⟨p,hpj,hpk⟩ := huc (i+1)
    obtain ⟨q,hqi,hqj⟩ := hlc i
    have hupper := hu (i+1) q
    have hlower := hl i p
    have hs : Y p i + Y p (i+1) + Y p ((i+1)+1) ≤
        Y q i + Y q (i+1) + Y q ((i+1)+1) := by
      have h := ((hp p).trans (hp q).symm).le
      simp only [Fin.sum_univ_three] at h
      fin_cases i <;> dsimp <;> linarith only [h]
    simp only [hpj,hpk,hqi,hqj] at hs hupper hlower
    exact contact_slope_bound (Y p i) (u (i+1)) (u ((i+1)+1))
      (l i) (l (i+1)) (Y q ((i+1)+1)) (A (i+1)) (B i)
      (ho (i+1)) (hA (i+1)).le hupper hlower hs
  have hab := weights X lo hi a b D ho ha hp hu hl huc hlc
  have hba := weights (fun v i => -X v i) (fun i => -hi i) (fun i => -lo i)
    b a (-D) (fun i => neg_lt_neg (ho i)) hb
    (fun v => by simpa only [Finset.sum_neg_distrib] using congrArg Neg.neg (hp v))
    (fun i v => by nlinarith only [hl i v])
    (fun i v => by nlinarith only [hu i v])
    (fun i => (hlc i).imp fun v hv => ⟨congrArg Neg.neg hv.1,congrArg Neg.neg hv.2⟩)
    (fun i => (huc i).imp fun v hv => ⟨congrArg Neg.neg hv.1,congrArg Neg.neg hv.2⟩)
  exact PlanarWidthCriterion.width_bound X lo hi R a b (fun i => (ha i).le)
    (fun i => (hb i).le) (fun i => (ho i).le) hR hzero hmax hu hl hab hba

end Plank.Convex.PlanarSixCellSupports
