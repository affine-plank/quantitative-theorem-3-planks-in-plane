/- Full catalogue for a vertical pair and an initially oblique Y-supported band. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralObliquePair

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralObliqueCatalogue
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralSectionProfile
open CrossedQuadrilateralSectionGeometry UnimodalPlanarMerge

def total (S : Shape) (a b c d lo hi : ℝ) : ℝ :=
  (b-a)/(S.a+S.c)+(d-c)/(S.a+S.c)+(hi-lo)/(S.b+S.d)

theorem direction_of_equality (S : Shape) {k a b c d lo hi : ℝ} (hk : YSupports S k)
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : total S a b c d lo hi < 1)
    (he : (volume (S.body \ ((band a b ∪ band c d) ∪ oblique k lo hi))).toReal =
      (1-total S a b c d lo hi)^2*(volume S.body).toReal) : k = 0 := by
  obtain ⟨l,u,hlu,hw,hm⟩ := CrossedQuadrilateralObliqueMerge.arbitrary_pair S hk ho hab.le hcd.le
  have hpos : l < u := by linarith only [hw,hab,hcd]
  have hb : (u-l)/(S.a+S.c)+(hi-lo)/(S.b+S.d) = total S a b c d lo hi := by
    rw [hw,add_div]
    rfl
  have hsmall : (u-l)/(S.a+S.c)+(hi-lo)/(S.b+S.d) < 1 := by rwa [hb]
  have he' : (volume (S.body \ (band l u ∪ oblique k lo hi))).toReal =
      (1-((u-l)/(S.a+S.c)+(hi-lo)/(S.b+S.d)))^2*(volume S.body).toReal := by
    apply le_antisymm
    · rw [hb]
      exact hm.trans_eq he
    · exact CrossedQuadrilateralObliquePair.lower_bound S hk ho.le hlu hsmall
  exact CrossedQuadrilateralObliquePair.direction_of_equality S hk ho hpos hsmall he'

def Catalogue (S : Shape) (k a b c d lo hi : ℝ) : Prop :=
  k = 0 ∧ ((b = c ∧ d/S.a = -a/S.c) ∨ (d = a ∧ b/S.a = -c/S.c)) ∧
    hi/S.b = -lo/S.d

theorem horizontal_iff (S : Shape) {a b c d lo hi : ℝ}
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : total S a b c d lo hi < 1) :
    (volume (S.body \ ((band a b ∪ band c d) ∪ oblique 0 lo hi))).toReal =
      (1-total S a b c d lo hi)^2*(volume S.body).toReal ↔
      ((b = c ∧ d/S.a = -a/S.c) ∨ (d = a ∧ b/S.a = -c/S.c)) ∧ hi/S.b = -lo/S.d := by
  have hy : oblique 0 lo hi = CrossedQuadrilateralPlacement.band true lo hi := by
    ext z
    simp [oblique,CrossedQuadrilateralPlacement.band,CrossedQuadrilateralPlacement.coord]
  rw [hy]
  change (volume (S.body \ ((CrossedQuadrilateralPlacement.band false a b ∪
    CrossedQuadrilateralPlacement.band false c d) ∪ CrossedQuadrilateralPlacement.band true lo hi))).toReal = _ ↔ _
  unfold total at hR ⊢
  rcases le_total a c with hac | hca
  · rw [CrossedQuadrilateralTwoDirections.equality_iff_adjacent S a b c d lo hi hab hcd hac ho.le hR]
    constructor
    · rintro ⟨ha,hc,ht⟩
      exact ⟨Or.inl ⟨ha,hc⟩,ht.resolve_left ho.ne'⟩
    · rintro ⟨(⟨ha,hc⟩ | ⟨ha,hc⟩),ht⟩
      · exact ⟨ha,hc,Or.inr ht⟩
      · exfalso; linarith only [ha,hac,hcd]
  · have hR' : (d-c)/(S.a+S.c)+(b-a)/(S.a+S.c)+(hi-lo)/(S.b+S.d) < 1 := by
      simpa only [add_comm] using hR
    rw [Set.union_comm (CrossedQuadrilateralPlacement.band false a b),
      add_comm ((b-a)/(S.a+S.c))]
    rw [CrossedQuadrilateralTwoDirections.equality_iff_adjacent S c d a b lo hi hcd hab hca ho.le hR']
    constructor
    · rintro ⟨ha,hc,ht⟩
      exact ⟨Or.inr ⟨ha,hc⟩,ht.resolve_left ho.ne'⟩
    · rintro ⟨(⟨ha,hc⟩ | ⟨ha,hc⟩),ht⟩
      · exfalso; linarith only [ha,hca,hab]
      · exact ⟨ha,hc,Or.inr ht⟩

/-- Exhaustive iff in the mixed opposite-support sector. Both vertical
bands and the third band have positive width; their placements are arbitrary.
Equality forces the third band horizontal and calibrated, and forces the
vertical pair to be adjacent pieces of one calibrated band, in either order. -/
theorem equality_iff_catalogue (S : Shape) {k a b c d lo hi : ℝ} (hk : YSupports S k)
    (hab : a < b) (hcd : c < d) (ho : lo < hi) (hR : total S a b c d lo hi < 1) :
    (volume (S.body \ ((band a b ∪ band c d) ∪ oblique k lo hi))).toReal =
      (1-total S a b c d lo hi)^2*(volume S.body).toReal ↔ Catalogue S k a b c d lo hi := by
  constructor
  · intro he
    have hk0 := direction_of_equality S hk hab hcd ho hR he
    refine ⟨hk0,?_⟩
    rw [hk0] at he
    exact (horizontal_iff S hab hcd ho hR).mp he
  · rintro ⟨rfl,hc⟩
    exact (horizontal_iff S hab hcd ho hR).mpr hc

end Quant.CrossedQuadrilateralObliqueCatalogue

/-- info: 'Quant.CrossedQuadrilateralObliqueCatalogue.equality_iff_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralObliqueCatalogue.equality_iff_catalogue
