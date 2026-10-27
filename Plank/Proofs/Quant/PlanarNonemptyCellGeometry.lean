/- Transversality and full-pair consequences retained for auxiliary proofs. -/
module

public import Plank.Proofs.Quant.PlanarNonemptyCellCore
public import Plank.Proofs.Quant.PlanarPairContainment

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSevenNonemptyCells
open Set MeasureTheory PlanarQuantitative PlanarParameterDomain
open PlanarPairContainment PlanarDirectionDerivatives

/-- Four weak corner witnesses for two strict windows rule out parallel
directions. No positive area or persistence of the witnesses is required. -/
theorem cross_ne_zero_of_corners (K : Set Point) (f g : Point →ᵃ[ℝ] ℝ)
    (hf : f.linear ≠ 0) (lo hi lo' hi' : ℝ)
    (ho : lo < hi) (ho' : lo' < hi')
    (hcorners : ∀ b c : Bool, ∃ x ∈ K,
      (if b then hi ≤ f x else f x ≤ lo) ∧
      (if c then hi' ≤ g x else g x ≤ lo')) : cross f g ≠ 0 := by
  let F : Point →ᵃ[ℝ] Point := AffineMap.pi ![f, g]
  have hsurj : Function.Surjective F :=
    ResearchFormalized.OrthantWitnesses.surjective_of_witnesses F ![lo, lo'] ![hi, hi']
      (by intro i; fin_cases i <;> assumption) fun s => by
        obtain ⟨x, _, hxf, hxg⟩ := hcorners (decide ((0 : Fin 2) ∈ s))
          (decide ((1 : Fin 2) ∈ s))
        refine ⟨x, ?_⟩
        intro i
        fin_cases i
        · simpa [F, AffineMap.pi_apply] using hxf
        · simpa [F, AffineMap.pi_apply] using hxg
  intro hz
  have hdet : F.linear.det = 0 := (PlanarPairArea.cross_eq_det f g).symm.trans hz
  have hr := LinearMap.range_lt_top_of_det_eq_zero hdet
  rw [LinearMap.range_eq_top.mpr (F.linear_surjective_iff.mpr hsurj)] at hr
  exact lt_irrefl _ hr

theorem pairwise_transverse_of_seven (K : Set Point) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (p : Endpoints 3)
    (ho : ∀ i, p.1 i < p.2 i) (hcount : 7 ≤ (nonemptyCells K f p).card) :
    ∀ i j, i ≠ j → cross (f i) (f j) ≠ 0 := by
  intro i j hij
  exact cross_ne_zero_of_corners K (f i) (f j) (hf i) _ _ _ _ (ho i) (ho j)
    (corners_of_seven K f p hcount i j hij)

/-- Seven nonempty closed cells contain every full pair overlap in the
body. Nonempty null cells are retained throughout this argument. -/
theorem pair_subset_of_nonempty_seven {K : Set Point} (hclosed : IsClosed K)
    (hconv : Convex ℝ K) (f : Fin 3 → Point →ᵃ[ℝ] ℝ)
    (hf : ∀ i, (f i).linear ≠ 0) (p : Endpoints 3)
    (ho : ∀ i, p.1 i < p.2 i) (hcount : 7 ≤ (nonemptyCells K f p).card) :
    ∀ i j, i ≠ j →
      {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} ∩
        {x | p.1 j ≤ f j x ∧ f j x ≤ p.2 j} ⊆ K := by
  intro i j hij
  exact pair_subset_of_corners hclosed hconv (f i) (f j)
    (pairwise_transverse_of_seven K f hf p ho hcount i j hij) _ _ _ _
    (corners_of_seven K f p hcount i j hij)

end Plank.PlanarSevenNonemptyCells
