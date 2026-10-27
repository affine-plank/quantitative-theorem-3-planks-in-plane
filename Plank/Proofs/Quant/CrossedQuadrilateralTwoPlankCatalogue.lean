/- The two geometric families after diagonal direction rigidity. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralTwoPlankDirections

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralTwoPlankCatalogue
open Set MeasureTheory
open CrossedQuadrilateralAttainment CrossedQuadrilateralPlacement
open Plank.Convex.DeficientHeightTilt

def span (S : Shape) (i : Bool) : ℝ := if i then S.b+S.d else S.a+S.c
def calibrated (S : Shape) (i : Bool) (l u : ℝ) : Prop :=
  if i then u/S.b = -l/S.d else u/S.a = -l/S.c

/-- Distinct diagonal directions give two calibrated bands. A common
diagonal direction gives an adjacent split of one calibrated band, in either
label order. These are the two geometric families. -/
def Families (S : Shape) (i j : Bool) (l u l' u' : ℝ) : Prop :=
  if i = j then
    (u = l' ∧ calibrated S i l u') ∨ (u' = l ∧ calibrated S i l' u)
  else calibrated S i l u ∧ calibrated S j l' u'

private theorem same_x_ordered (S : Shape) (l u l' u' : ℝ)
    (ho : l < u) (ho' : l' < u') (hl : l ≤ l')
    (hR : (u-l)/(S.a+S.c)+(u'-l')/(S.a+S.c) < 1) :
    (volume (S.body \ (band false l u ∪ band false l' u'))).toReal =
      (1-((u-l)/(S.a+S.c)+(u'-l')/(S.a+S.c)))^2*(volume S.body).toReal ↔
      u = l' ∧ u'/S.a = -l/S.c := by
  have hh := CrossedQuadrilateralTwoDirections.equality_iff_adjacent S l u l' u' 0 0
    ho ho' hl le_rfl (by simpa using hR)
  rw [← Set.sdiff_sdiff,measure_sdiff_null (volume_band_null true 0)] at hh
  simpa using hh

private theorem same_x (S : Shape) (l u l' u' : ℝ)
    (ho : l < u) (ho' : l' < u')
    (hR : (u-l)/(S.a+S.c)+(u'-l')/(S.a+S.c) < 1) :
    (volume (S.body \ (band false l u ∪ band false l' u'))).toReal =
      (1-((u-l)/(S.a+S.c)+(u'-l')/(S.a+S.c)))^2*(volume S.body).toReal ↔
      (u = l' ∧ u'/S.a = -l/S.c) ∨ (u' = l ∧ u/S.a = -l'/S.c) := by
  rcases le_total l l' with hl | hl
  · rw [same_x_ordered S l u l' u' ho ho' hl hR]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · have hh := h.1; linarith only [hh,hl,ho']
  · have hh := same_x_ordered S l' u' l u ho' ho hl (by simpa only [add_comm] using hR)
    rw [Set.union_comm,add_comm ((u-l)/(S.a+S.c))]
    rw [hh]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · have hh := h.1; linarith only [hh,hl,ho]
      · exact h

theorem swap_band (i : Bool) (l u : ℝ) :
    CrossedQuadrilateralSupport.swap '' band i l u = band (!i) l u := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    cases i <;> exact hy
  · intro hx
    refine ⟨(x.2,x.1),?_,rfl⟩
    cases i <;> exact hx

theorem swap_equality (S : Shape) (i j : Bool) (l u l' u' R : ℝ) :
    ((volume (S.body \ (band i l u ∪ band j l' u'))).toReal =
      (1-R)^2*(volume S.body).toReal) ↔
    ((volume ((CrossedQuadrilateralSupport.transpose S).body \
      (band (!i) l u ∪ band (!j) l' u'))).toReal =
      (1-R)^2*(volume (CrossedQuadrilateralSupport.transpose S).body).toReal) := by
  have hh := CrossedQuadrilateralAffine.image_equality_iff CrossedQuadrilateralSupport.swap
    S.body (band i l u ∪ band j l' u') ((1-R)^2)
  rw [CrossedQuadrilateralSupport.swap_body,Set.image_union,swap_band,swap_band] at hh
  exact hh.symm

/-- Exact iff for both positive bands, with arbitrary placements and both
axis choices. No overlap, endpoint order or origin-containment condition is
supplied. -/
theorem axis_equality_iff (S : Shape) (i j : Bool) (l u l' u' : ℝ)
    (ho : l < u) (ho' : l' < u')
    (hR : (u-l)/span S i+(u'-l')/span S j < 1) :
    (volume (S.body \ (band i l u ∪ band j l' u'))).toReal =
      (1-((u-l)/span S i+(u'-l')/span S j))^2*(volume S.body).toReal ↔
      Families S i j l u l' u' := by
  cases i <;> cases j
  · simpa only [span,Families,calibrated,if_true,Bool.false_eq_true,if_false] using
      same_x S l u l' u' ho ho' hR
  · have hh := arbitrary_placement_equality_iff S l u l' u' ho.le ho'.le hR
    simpa only [span,Families,calibrated,Bool.false_eq_true,if_false,if_true,
      sub_add_eq_sub_sub,or_iff_right (ne_of_lt ho).symm,or_iff_right (ne_of_lt ho').symm] using hh
  · have hh := arbitrary_placement_equality_iff S l' u' l u ho'.le ho.le
      (by simpa only [span,if_true,Bool.false_eq_true,if_false,add_comm] using hR)
    simp only [or_iff_right (ne_of_lt ho).symm,or_iff_right (ne_of_lt ho').symm] at hh
    simpa only [span,Families,calibrated,Bool.true_eq_false,Bool.false_eq_true,if_false,if_true,
      Set.union_comm,sub_sub,add_comm,and_comm] using hh
  · rw [swap_equality]
    simpa only [span,Families,calibrated,if_true,Bool.not_true,Bool.false_eq_true,if_false,
      CrossedQuadrilateralSupport.transpose] using
      same_x (CrossedQuadrilateralSupport.transpose S) l u l' u' ho ho' hR

end Quant.CrossedQuadrilateralTwoPlankCatalogue
