/- A three-factor identity for cyclic reciprocal complements. -/
module
public import Plank.Convex.ProductGap
public import Mathlib.Tactic.FieldSimp
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.ReciprocalCorner

abbrev Triple := Fin 3 → ℝ

/-- Reciprocal complements turn the gap into a product of three differences. -/
theorem factor (a b : Triple) (ha : ∀ i, a i ≠ 0)
    (hb : ∀ i, b i = 1 - (a (i + 1))⁻¹) :
    ProductGap.gap 2 a b = ∏ i, (a i - b i) := by
  have he : b = fun i => 1 - (a (i + 1))⁻¹ := funext hb
  rw [he]
  simp only [ProductGap.gap, Fin.prod_univ_three]
  norm_num only [show (0 : Fin 3) + 1 = 1 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl]
  field_simp [ha 0, ha 1, ha 2]
  ring

/-- Slopes at least one have positive differences from their reciprocal complements. -/
theorem pos (a b : Triple) (ha : ∀ i, 1 ≤ a i)
    (hb : ∀ i, b i = 1 - (a (i + 1))⁻¹) : 0 < ProductGap.gap 2 a b := by
  have hpos (i) : 0 < a i := zero_lt_one.trans_le (ha i)
  rw [factor a b (fun i => (hpos i).ne') hb]
  apply Finset.prod_pos
  intro i _
  rw [hb i]
  linarith [ha i, inv_pos.mpr (hpos (i + 1))]

end Plank.Convex.ReciprocalCorner
