/- A finite support-point argument removes compactness from the covering theorem. -/
module

public import QuantitativePlanks.Proof
public import QuantitativePlanks.Extensions.Closure

@[expose] public section
set_option autoImplicit false
noncomputable section

open Set
open scoped BigOperators

namespace Plank.Body

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Any strict fraction of a positive affine range is witnessed by two points.
No extrema, boundedness or topology on the original set are needed. -/
theorem exists_sub_gt_mul_width {K : Set E} (hne : K.Nonempty)
    (f : E →ᵃ[ℝ] ℝ) (hW : 0 < width K f) {q : ℝ} (hq : q < 1) :
    ∃ a ∈ K, ∃ b ∈ K, q * width K f < f a - f b := by
  by_contra! h
  have hup (b : E) (hb : b ∈ K) : sSup (f '' K) ≤ f b + q * width K f := by
    apply csSup_le (hne.image f)
    rintro _ ⟨a, ha, rfl⟩
    linarith [h a ha b hb]
  have hlo : sSup (f '' K) - q * width K f ≤ sInf (f '' K) := by
    apply le_csInf (hne.image f)
    rintro _ ⟨b, hb, rfl⟩
    linarith [hup b hb]
  have hsmall : q * width K f < width K f := by nlinarith
  dsimp only [width] at hlo hsmall
  linarith

end Plank.Body

namespace Plank.ConvexSetCover

open FiniteDimensionalCapWindowScaling FiniteDimensionalEndpointMajorants
  FiniteDimensionalFewCellScaling

/-- Planar APC for an arbitrary convex set: compactness and explicit
nonemptiness are unnecessary. When the directional ranges are bounded,
the denominators are exactly their usual geometric widths. -/
theorem cover_bound {K : Set (Point 1)} (hc : Convex ℝ K)
    (f : Fin 3 → Point 1 →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (p : Endpoints (Fin 3)) (horder : ∀ i, p.1 i ≤ p.2 i)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  classical
  by_contra! hbad
  have hne := Body.nonempty_of_width_pos (hW 0)
  have hR : 0 ≤ budget K f p :=
    Finset.sum_nonneg fun i _ => div_nonneg (sub_nonneg.mpr (horder i)) (hW i).le
  obtain ⟨q, hRq, hq⟩ := exists_between hbad
  have hq0 : 0 < q := hR.trans_lt hRq
  choose a ha b hb hab using fun i => Body.exists_sub_gt_mul_width hne (f i) (hW i) hq
  let S := range a ∪ range b
  let C := convexHull ℝ S
  have hCK : C ⊆ K := by
    apply convexHull_min _ hc
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    exacts [ha i, hb i]
  have hcompact : IsCompact C := ((finite_range a).union (finite_range b)).isCompact_convexHull ℝ
  have haC (i) : a i ∈ C := subset_convexHull ℝ S (Or.inl ⟨i, rfl⟩)
  have hbC (i) : b i ∈ C := subset_convexHull ℝ S (Or.inr ⟨i, rfl⟩)
  have hwidth (i) : q * Body.width K (f i) < Body.width C (f i) :=
    (hab i).trans_le (Body.sub_le_width hcompact (continuous_form (f i)) (haC i) (hbC i))
  have hCW (i) : 0 < Body.width C (f i) :=
    (mul_pos hq0 (hW i)).trans (hwidth i)
  have hbound := CoveringFirstPlanar.cover_bound hcompact (convex_convexHull ℝ S)
    ⟨a 0, haC 0⟩ f hCW p horder (hCK.trans hcover)
  have hcost : budget C f p ≤ budget K f p / q := by
    simp only [budget, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    calc
      (p.2 i-p.1 i) / Body.width C (f i) ≤
          (p.2 i-p.1 i) / (q * Body.width K (f i)) :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr (horder i))
          (mul_pos hq0 (hW i)) (hwidth i).le
      _ = (p.2 i-p.1 i) / Body.width K (f i) / q := by
        rw [mul_comm q, div_mul_eq_div_div]
  exact (hcost.trans_lt ((div_lt_one hq0).mpr hRq)).not_ge hbound

end Plank.ConvexSetCover

#print axioms Plank.ConvexSetCover.cover_bound
