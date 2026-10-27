/- Tight positive planks prevent enlargement of any directional width
when the same planks cover an enclosing triangle. -/
module
public import Plank.Convex.PlanarTight.BudgetEquality
public import Plank.Proofs.AffineTriangleCover
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.TriangleEnclosure

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- An affine coordinate on a triangle lies between its vertex extrema. -/
theorem bounds (v : Fin 3 → E) (f : E →ᵃ[ℝ] ℝ)
    (x : E) (hx : x ∈ convexHull ℝ (Set.range v)) :
    min (f (v 0)) (min (f (v 1)) (f (v 2))) ≤ f x ∧
      f x ≤ max (f (v 0)) (max (f (v 1)) (f (v 2))) := by
  let l := min (f (v 0)) (min (f (v 1)) (f (v 2)))
  let u := max (f (v 0)) (max (f (v 1)) (f (v 2)))
  have hh : convexHull ℝ (Set.range v) ⊆ f ⁻¹' Set.Icc l u := by
    apply convexHull_min ?_ ((convex_Icc l u).affine_preimage f)
    rintro _ ⟨i, rfl⟩
    change l ≤ f (v i) ∧ f (v i) ≤ u
    fin_cases i
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
        (le_max_left _ _).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (min_le_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩
  exact hh hx

/-- A triangle covered by the same positive windows as a tight normalized
body has exactly the same three directional ranges. Thus triangle equality
normal forms apply with the original endpoints and relative widths. -/
theorem ranges_of_tight (v : Fin 3 → E) (f : Fin 3 → E →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (hwidth : ∀ i, lo i < hi i)
    (hL : ∀ i, ∃ x ∈ convexHull ℝ (Set.range v), f i x = 0)
    (hU : ∀ i, ∃ x ∈ convexHull ℝ (Set.range v), f i x = 1)
    (hcover : ∀ x ∈ convexHull ℝ (Set.range v), ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i)
    (hsum : ∑ i, (hi i - lo i) = 1) :
    ∀ x ∈ convexHull ℝ (Set.range v), ∀ i, 0 ≤ f i x ∧ f i x ≤ 1 := by
  let m (i : Fin 3) := min (f i (v 0)) (min (f i (v 1)) (f i (v 2)))
  let M (i : Fin 3) := max (f i (v 0)) (max (f i (v 1)) (f i (v 2)))
  let d (i : Fin 3) := Plank.AffineTriangle.vertexSpread v (f i)
  have hm (i : Fin 3) : m i ≤ 0 := by
    obtain ⟨x, hx, hx0⟩ := hL i
    simpa only [hx0] using (bounds v (f i) x hx).1
  have hM (i : Fin 3) : 1 ≤ M i := by
    obtain ⟨x, hx, hx1⟩ := hU i
    simpa only [hx1] using (bounds v (f i) x hx).2
  have hd (i : Fin 3) : 1 ≤ d i := by
    change 1 ≤ M i - m i
    linarith only [hm i, hM i]
  have hdp (i : Fin 3) : 0 < d i := zero_lt_one.trans_le (hd i)
  have ht := Plank.AffineTriangle.sum_relative_width_ge_one v f lo hi hdp
    (fun i => (hwidth i).le) hcover
  change 1 ≤ ∑ i, (hi i - lo i) / d i at ht
  have he := BudgetEquality.bounded_row_eq_one (fun i => hi i - lo i) (fun i => 1 / d i)
    (fun i => sub_pos.mpr (hwidth i)) hsum
    (fun i => (div_le_one (hdp i)).mpr (hd i)) (by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using ht)
  have hde (i : Fin 3) : d i = 1 := by
    have hv := (div_eq_iff (hdp i).ne').mp (he i)
    simpa only [one_mul] using hv.symm
  intro x hx i
  have hb := bounds v (f i) x hx
  have he' : M i - m i = 1 := hde i
  have hm0 : m i = 0 := by linarith only [hm i, hM i, he']
  have hM1 : M i = 1 := by linarith only [hm0, he']
  change m i ≤ f i x ∧ f i x ≤ M i at hb
  simpa only [hm0, hM1] using hb

end Plank.Convex.PlanarTight.TriangleEnclosure

/-- info: 'Plank.Convex.PlanarTight.TriangleEnclosure.ranges_of_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TriangleEnclosure.ranges_of_tight
