/- Full direction and placement catalogue for a vertical pair and a transverse band. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralReflections
public import Plank.Proofs.Quant.CrossedQuadrilateralOppositeXExclusion

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralVerticalPairCatalogue
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionProfile
open CrossedQuadrilateralPairBudget CrossedQuadrilateralReflections
open CrossedQuadrilateralObliquePhysical CrossedQuadrilateralSectionGeometry
open CrossedQuadrilateralObliqueCatalogue
open scoped BigOperators

theorem budget_eq_total (S : Shape) {k : ℝ} (hk : YSupports S k) (a b c d lo hi : ℝ) :
    budget S k a b c d lo hi = total S a b c d lo hi := by
  unfold budget total
  rw [oblique_range S hk]

theorem zero_supports (S : Shape) : YSupports S 0 := by
  exact ⟨div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr S.hb.le) S.hc.le,
    (div_pos S.hb S.ha).le,
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr S.hd.le) S.ha.le,
    (div_pos S.hd S.hc).le⟩

theorem nonnegative_direction (S : Shape) {k a b c d lo hi : ℝ} (hk0 : 0 ≤ k)
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : budget S k a b c d lo hi < 1)
    (he : gap S k a b c d lo hi = (1-budget S k a b c d lo hi)^2*(volume S.body).toReal) :
    k = 0 := by
  rcases le_total k (S.b/S.a) with hk₁ | hk₁
  · rcases le_total k (S.d/S.c) with hk₂ | hk₂
    · have hY : YSupports S k :=
        ⟨(zero_supports S).1.trans hk0,hk₁,(zero_supports S).2.2.1.trans hk0,hk₂⟩
      rw [budget_eq_total S hY] at hR he
      exact CrossedQuadrilateralObliqueCatalogue.direction_of_equality S hY hab hcd ho hR he
    · exfalso
      have hs : CrossedQuadrilateralAdjacentProfile.Sector (opposite S) k := ⟨hk₂,hk₁⟩
      have hR' : budget (opposite S) k (-b) (-a) (-d) (-c) (-hi) (-lo) < 1 := by
        rwa [budget_antipode]
      have he' : gap (opposite S) k (-b) (-a) (-d) (-c) (-hi) (-lo) =
          (1-budget (opposite S) k (-b) (-a) (-d) (-c) (-hi) (-lo))^2*
            (volume (opposite S).body).toReal := by
        rw [budget_antipode]
        exact (equality_antipode S k a b c d lo hi _).mpr he
      exact (CrossedQuadrilateralAdjacentExclusion.strict (opposite S) hs
        (neg_lt_neg ho) (neg_lt_neg hab) (neg_lt_neg hcd) hR').ne' he'
  · rcases le_total k (S.d/S.c) with hk₂ | hk₂
    · exact False.elim ((CrossedQuadrilateralAdjacentExclusion.strict S ⟨hk₁,hk₂⟩ ho hab hcd hR).ne' he)
    · exact False.elim (CrossedQuadrilateralOppositeXExclusion.not_equality S hk₁ hk₂ hab hcd ho hR he)

/-- Arbitrary slope and placement: every sharp transverse band is horizontal. -/
theorem direction_of_equality (S : Shape) {k a b c d lo hi : ℝ}
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : budget S k a b c d lo hi < 1)
    (he : gap S k a b c d lo hi = (1-budget S k a b c d lo hi)^2*(volume S.body).toReal) :
    k = 0 := by
  rcases le_or_gt 0 k with hk | hk
  · exact nonnegative_direction S hk hab hcd ho hR he
  · have hR' : budget (flippedX S) (-k) (-b) (-a) (-d) (-c) lo hi < 1 := by
      rwa [budget_flipX]
    have he' : gap (flippedX S) (-k) (-b) (-a) (-d) (-c) lo hi =
        (1-budget (flippedX S) (-k) (-b) (-a) (-d) (-c) lo hi)^2*
          (volume (flippedX S).body).toReal := by
      rw [budget_flipX]
      exact (equality_flipX S k a b c d lo hi _).mpr he
    have hh := nonnegative_direction (flippedX S) (neg_pos.mpr hk).le
      (neg_lt_neg hab) (neg_lt_neg hcd) ho hR' he'
    linarith only [hh]

/-- A geometric iff with no support-sector, overlap or label-order hypothesis. -/
theorem equality_iff_catalogue (S : Shape) {k a b c d lo hi : ℝ}
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : budget S k a b c d lo hi < 1) :
    gap S k a b c d lo hi = (1-budget S k a b c d lo hi)^2*(volume S.body).toReal ↔
      Catalogue S k a b c d lo hi := by
  constructor
  · intro he
    have hk := direction_of_equality S hab hcd ho hR he
    refine ⟨hk,?_⟩
    subst k
    rw [budget_eq_total S (zero_supports S)] at hR he
    exact (horizontal_iff S hab hcd ho hR).mp he
  · rintro ⟨rfl,hc⟩
    rw [budget_eq_total S (zero_supports S)] at hR ⊢
    exact (horizontal_iff S hab hcd ho hR).mpr hc

theorem physical_iff (S : Shape) {k a b c d lo hi : ℝ}
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : budget S k a b c d lo hi < 1) :
    (volume (S.body \ ⋃ i, (family k a b c d lo hi hab.le hcd.le ho.le i).set)).toReal =
      (1-∑ i, relativeWidth S (family k a b c d lo hi hab.le hcd.le ho.le i))^2*
        (volume S.body).toReal ↔ Catalogue S k a b c d lo hi := by
  rw [actual_budget,CrossedQuadrilateralObliquePhysical.family_union]
  exact equality_iff_catalogue S hab hcd ho hR

theorem affine_iff (S : Shape) (T : Point ≃ᵃ[ℝ] Point) {k a b c d lo hi : ℝ}
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : budget S k a b c d lo hi < 1) :
    (volume (T '' S.body \ ⋃ i, CrossedQuadrilateralAffine.imagePlank T
      (family k a b c d lo hi hab.le hcd.le ho.le i))).toReal =
      (1-∑ i, CrossedQuadrilateralAffine.imageRelativeWidth S T
        (family k a b c d lo hi hab.le hcd.le ho.le i))^2*(volume (T '' S.body)).toReal ↔
          Catalogue S k a b c d lo hi := by
  rw [CrossedQuadrilateralAffine.family_equality_iff]
  exact physical_iff S hab hcd ho hR

end Quant.CrossedQuadrilateralVerticalPairCatalogue

/-- info: 'Quant.CrossedQuadrilateralVerticalPairCatalogue.affine_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralVerticalPairCatalogue.affine_iff
