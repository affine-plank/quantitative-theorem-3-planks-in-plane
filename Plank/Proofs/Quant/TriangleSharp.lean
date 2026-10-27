module
/- The sharp uncovered-area bound for three planks on every triangle. -/
public import Plank.Proofs.Quant.PlanarThreePlank
public import Plank.Proofs.Quant.TrianglePlanarBound
public import Plank.Proofs.Quant.AffineTransport

@[expose] public section
noncomputable section

namespace Quant.TriangleSharp

/-- Every three-plank configuration on the standard triangle satisfies the
positive-part square lower bound on its actual uncovered area. -/
theorem sqPos (C : Config) : Quant.SqPos C := by
  have h := Plank.TrianglePlanarBound.bound_of_planar
    Plank.PlanarThreePlank.sharpPlanarBound_three stdTriangle C.plank
  simpa only [Quant.SqPos,Config.deficit,Config.sumRelW,Config.relW,
    Config.gapArea,Config.uncovered,Proofs.Quant.volume_stdTriangle,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2)] using h

/-- The signed-deficit version when the total relative width is at most one. -/
theorem sqBound (C : Config) (hs : C.sumRelW ≤ 1) : C.SqBound := by
  have hd : 0 ≤ C.deficit := by simp only [Config.deficit]; linarith
  simpa only [Quant.SqPos,Config.SqBound,max_eq_right hd] using sqPos C

/-- The sharp quantitative triangle theorem, using the actual Lebesgue areas
and relative widths of the original triangle and planks. No covering, position,
width-sum, or direction hypotheses are required. -/
theorem uncovered_area_lower_bound (T : Triangle) (p : Fin 3 → Plank) :
    (max 0 (1-∑ i, (p i).relWidth T))^2*(MeasureTheory.volume T.set).toReal ≤
      (MeasureTheory.volume (T.set \ ⋃ i, (p i).set)).toReal :=
  Plank.TrianglePlanarBound.bound_of_planar
    Plank.PlanarThreePlank.sharpPlanarBound_three T p

/-- The qualitative affine plank theorem follows from the quantitative bound. -/
theorem threePlanks : ThreePlanksOnATriangle :=
  Proofs.Transport.threePlanks_of_std (Quant.covers_sum_of_sqPos sqPos)

/-- The existing stacking construction attains the now-proved lower bound.
Thus the coefficient and exponent in the universal inequality are sharp. -/
theorem isLeast_gapValues (c w : Fin 3 → ℝ)
    (hc0 : 0 ≤ c 0) (hc01 : c 0 ≤ c 1) (hc12 : c 1 ≤ c 2)
    (hw : ∀ i, 0 ≤ w i) (ht : w 0+w 1+w 2 ≤ 1) :
    IsLeast (Quant.gapValues (fun i => ((1 : ℝ),-c i)) w)
      ((1-(w 0+w 1+w 2))^2/2) := by
  apply Quant.isLeast_gapValues_of_floor c w hc0 hc01 hc12 hw ht
  rintro g ⟨C,_,hwidth,rfl⟩
  simpa only [Quant.SqPos,Config.deficit,Config.sumRelW,hwidth,Fin.sum_univ_three,
    max_eq_right (sub_nonneg.mpr ht),div_eq_mul_inv,one_mul] using sqPos C

end Quant.TriangleSharp
