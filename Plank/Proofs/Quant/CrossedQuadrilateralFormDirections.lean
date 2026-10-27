/- Affine-form direction rigidity for use in actual equality strata. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralDirections

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralFormDirections
open Set MeasureTheory
open Quant.CrossedQuadrilateralAttainment
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

abbrev Plane := Fin 2 → ℝ
abbrev body (S : Shape) : Set Plane := ParallelProductPlane.coordinates ⁻¹' S.body

def normal (f : Plane →ᵃ[ℝ] ℝ) : Point := (f.linear ![1,0],f.linear ![0,1])

theorem normal_eval (f : Plane →ᵃ[ℝ] ℝ) (x : Plane) :
    f x = dot (normal f) (ParallelProductPlane.coordinates x)+f 0 := by
  have hb₀ : (fun j : Fin 2 => if (0 : Fin 2) = j then (1 : ℝ) else 0) = ![1,0] := by
    funext j; fin_cases j <;> norm_num
  have hb₁ : (fun j : Fin 2 => if (1 : Fin 2) = j then (1 : ℝ) else 0) = ![0,1] := by
    funext j; fin_cases j <;> norm_num
  have hlin : f.linear x = x 0*f.linear ![1,0]+x 1*f.linear ![0,1] := by
    simpa only [Fin.sum_univ_two,hb₀,hb₁,smul_eq_mul] using f.linear.pi_apply_eq_sum_univ x
  rw [Plank.PlanarGapCells.affine_eval,hlin]
  change x 0*f.linear ![1,0]+x 1*f.linear ![0,1]+f 0 =
    f.linear ![1,0]*x 0+f.linear ![0,1]*x 1+f 0
  ring

theorem fourPoint_direction (S : Shape) (f : Plane →ᵃ[ℝ] ℝ) (a b c d : Plane)
    (hmax : ∀ z ∈ body S, f z ≤ f a) (hmin : ∀ z ∈ body S, f b ≤ f z)
    (hlevel : f c = f d) (hs : body S = Plank.PlanarOnePlankVertices.fourPointBody a b c d) :
    (normal f).1 = 0 ∨ (normal f).2 = 0 := by
  have he (z : Plane) : ParallelProductPlane.pullForm (direction (normal f)) z = f z-f 0 := by
    simp only [ParallelProductPlane.pullForm_apply,direction_apply]
    linarith only [normal_eval f z]
  apply CrossedQuadrilateralDirections.direction_of_fourPoint_preimage S (normal f) a b c d
  · intro z hz
    rw [he,he]
    exact sub_le_sub_right (hmax z hz) _
  · intro z hz
    rw [he,he]
    exact sub_le_sub_right (hmin z hz) _
  · rw [he,he,hlevel]
  · exact hs

theorem one_window_direction (S : Shape) (f : Plane →ᵃ[ℝ] ℝ) (lo hi : ℝ)
    (ho : lo < hi) (hW : 0 < rangeWidth (body S) f) (hR : (hi-lo)/rangeWidth (body S) f < 1)
    (he : (volume (body S \ {z | lo ≤ f z ∧ f z ≤ hi})).toReal =
      (1-(hi-lo)/rangeWidth (body S) f)^2*(volume (body S)).toReal) :
    (normal f).1 = 0 ∨ (normal f).2 = 0 := by
  have hK := ParallelProductPlane.compact_preimage (compact_body S)
  have hc := (convex_body S).linear_preimage ParallelProductPlane.coordinates.toLinearMap
  have hne : (body S).Nonempty := ⟨ParallelProductPlane.coordinates.symm 0,by simpa using zero_mem S⟩
  have hV : 0 < (volume (body S)).toReal := by
    rw [ParallelProductPlane.volume_preimage]
    exact area_body_pos S
  obtain ⟨a,_,b,_,hmax,hmin,_,_,c,_,d,_,hfc,hfd,hs⟩ :=
    (Plank.PlanarOnePlankClassification.equality_iff_exists_fourPointBody
      hK hc hne hV f lo hi ho hW hR).mp he
  exact fourPoint_direction S f a b c d hmax hmin (hfc.trans hfd.symm) hs

theorem cross_normal (f g : Plane →ᵃ[ℝ] ℝ) :
    Plank.PlanarDirectionDerivatives.cross f g =
      (normal f).1*(normal g).2-(normal f).2*(normal g).1 := by
  have h₀ : (Pi.single 0 1 : Plane) = ![1,0] := by
    funext j; fin_cases j <;> norm_num [Pi.single_apply]
  have h₁ : (Pi.single 1 1 : Plane) = ![0,1] := by
    funext j; fin_cases j <;> norm_num [Pi.single_apply]
  simp only [Plank.PlanarDirectionDerivatives.cross,h₀,h₁,normal]

private theorem parallel_x (f g : Plane →ᵃ[ℝ] ℝ) (hf : (normal f).1 = 0)
    (hg : (normal g).1 = 0) : Plank.PlanarDirectionDerivatives.cross f g = 0 := by
  rw [cross_normal,hf,hg]
  ring

private theorem parallel_y (f g : Plane →ᵃ[ℝ] ℝ) (hf : (normal f).2 = 0)
    (hg : (normal g).2 = 0) : Plank.PlanarDirectionDerivatives.cross f g = 0 := by
  rw [cross_normal,hf,hg]
  ring

/-- Three positive individually tight windows cannot have three distinct
directions on the genuine quadrilateral. Individual tightness is an explicit
hypothesis here; the mixed-window theorem must supply it from its geometry. -/
theorem three_tight_have_parallel_pair (S : Shape) (f : Fin 3 → Plane →ᵃ[ℝ] ℝ)
    (lo hi : Fin 3 → ℝ) (ho : ∀ i, lo i < hi i)
    (hW : ∀ i, 0 < rangeWidth (body S) (f i))
    (hR : ∀ i, (hi i-lo i)/rangeWidth (body S) (f i) < 1)
    (he : ∀ i, (volume (body S \ {z | lo i ≤ f i z ∧ f i z ≤ hi i})).toReal =
      (1-(hi i-lo i)/rangeWidth (body S) (f i))^2*(volume (body S)).toReal) :
    ∃ i j : Fin 3, i ≠ j ∧ Plank.PlanarDirectionDerivatives.cross (f i) (f j) = 0 := by
  have hh (i) := one_window_direction S (f i) (lo i) (hi i) (ho i) (hW i) (hR i) (he i)
  rcases hh 0 with hx₀ | hy₀
  · rcases hh 1 with hx₁ | hy₁
    · exact ⟨0,1,by decide,parallel_x _ _ hx₀ hx₁⟩
    · rcases hh 2 with hx₂ | hy₂
      · exact ⟨0,2,by decide,parallel_x _ _ hx₀ hx₂⟩
      · exact ⟨1,2,by decide,parallel_y _ _ hy₁ hy₂⟩
  · rcases hh 1 with hx₁ | hy₁
    · rcases hh 2 with hx₂ | hy₂
      · exact ⟨1,2,by decide,parallel_x _ _ hx₁ hx₂⟩
      · exact ⟨0,2,by decide,parallel_y _ _ hy₀ hy₂⟩
    · exact ⟨0,1,by decide,parallel_y _ _ hy₀ hy₁⟩

end Quant.CrossedQuadrilateralFormDirections

/-- info: 'Quant.CrossedQuadrilateralFormDirections.three_tight_have_parallel_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralFormDirections.three_tight_have_parallel_pair
