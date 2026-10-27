/- Six boundary overlaps give a nonnegative identity and rigid equality. -/
module
public import Plank.Proofs.TriangleSliding.SideIntervals

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace SixBoundaries

def lowerWeight (d : Coordinates) (i : Fin 3) : ℝ :=
  1 - d (i + 1) + d (i + 1) * d (i + 2)

def upperWeight (d : Coordinates) (i : Fin 3) : ℝ :=
  d (i + 2) + (1 - d (i + 2)) * (1 - d (i + 1))

/-- The width excess is a square plus six positive multiples of the overlaps. -/
theorem bridge_identity (d L G : Coordinates) :
    let P := 1 + d 0 * d 1 * d 2
    let Q := 1 + (1 - d 0) * (1 - d 1) * (1 - d 2)
    P * Q * (∑ i, (1 - L i - G i) - 1) =
      (P - Q) ^ 2 +
      Q * ∑ i, lowerWeight d i * (d i - L i - d i * L (i + 2)) +
      P * ∑ i, upperWeight d i * (1 - d i - G i - (1 - d i) * G (i + 1)) := by
  simp only [Fin.sum_univ_three, lowerWeight, upperWeight]
  dsimp
  ring

/-- Three bridges give the inequality directly because every remainder
in the identity is nonnegative. -/
theorem bridge_width_bound {d L G : Coordinates}
    (hd0 : ∀ i, 0 < d i) (hd1 : ∀ i, d i < 1)
    (hB : ∀ i, bridges d L G i) : 1 ≤ ∑ i, (1 - L i - G i) := by
  let P := 1 + d 0 * d 1 * d 2
  let Q := 1 + (1 - d 0) * (1 - d 1) * (1 - d 2)
  have hP : 0 < P := add_pos zero_lt_one (mul_pos (mul_pos (hd0 0) (hd0 1)) (hd0 2))
  have hQ : 0 < Q := add_pos zero_lt_one
    (mul_pos (mul_pos (sub_pos.mpr (hd1 0)) (sub_pos.mpr (hd1 1)))
      (sub_pos.mpr (hd1 2)))
  have hL (i : Fin 3) : 0 ≤ lowerWeight d i * (d i - L i - d i * L (i + 2)) := by
    apply mul_nonneg (add_nonneg (sub_pos.mpr (hd1 _)).le (mul_pos (hd0 _) (hd0 _)).le)
    have h := (hB (i + 2)).1
    rw [add21] at h
    linarith only [h]
  have hG (i : Fin 3) :
      0 ≤ upperWeight d i * (1 - d i - G i - (1 - d i) * G (i + 1)) := by
    apply mul_nonneg (add_nonneg (hd0 _).le
      (mul_pos (sub_pos.mpr (hd1 _)) (sub_pos.mpr (hd1 _))).le)
    have h := (hB (i + 1)).2
    rw [add12] at h
    linarith only [h]
  have h := bridge_identity d L G
  change P * Q * (∑ i, (1 - L i - G i) - 1) = _ at h
  have hn : 0 ≤ P * Q * (∑ i, (1 - L i - G i) - 1) := by
    rw [h]
    exact add_nonneg (add_nonneg (sq_nonneg (P - Q))
      (mul_nonneg hQ.le (Finset.sum_nonneg (fun i _ => hL i))))
      (mul_nonneg hP.le (Finset.sum_nonneg (fun i _ => hG i)))
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (mul_pos hP hQ)).mp hn)

end SixBoundaries
