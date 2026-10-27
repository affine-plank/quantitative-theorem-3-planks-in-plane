/- The one-positive-width stratum of the three-plank quantitative formula. -/
module

public import Plank.Proofs.Quant.PlanarOnePlankClassification

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarSingleActivePlank

open Set MeasureTheory PlanarQuantitative PlanarGapCells PlanarOnePlankVertices
open Plank.Convex.DeficientHeightTilt

theorem volume_band_zero {K : Set Point} (hne : K.Nonempty)
    (f : Point →ᵃ[ℝ] ℝ) (hW : 0 < rangeWidth K f) (c : ℝ) :
    volume {x | c ≤ f x ∧ f x ≤ c} = 0 := by
  have hs : {x | c ≤ f x ∧ f x ≤ c} = {x | f x = c} := by
    ext x
    exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩
  rw [hs]
  exact measure_level_zero f (linear_ne_zero_of_rangeWidth_pos hne f hW) c

/-- Arbitrary locations and directions of the two null planks have no
effect on the actual uncovered area. -/
theorem gap_eq_single {K : Set Point} (hne : K.Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (h1 : lo 1 = hi 1) (h2 : lo 2 = hi 2) :
    volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i}) =
      volume (K \ {x | lo 0 ≤ f 0 x ∧ f 0 x ≤ hi 0}) := by
  let bad : Set Point := {x | lo 1 ≤ f 1 x ∧ f 1 x ≤ hi 1} ∪
    {x | lo 2 ≤ f 2 x ∧ f 2 x ≤ hi 2}
  have hbad : volume bad = 0 := by
    apply measure_union_null
    · rw [← h1]
      exact volume_band_zero hne (f 1) (hW 1) _
    · rw [← h2]
      exact volume_band_zero hne (f 2) (hW 2) _
  apply measure_congr
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hbad] with x hx
  apply propext
  constructor
  · intro hh
    exact ⟨hh.1,fun hp => hh.2 (mem_iUnion.mpr ⟨0,hp⟩)⟩
  · rintro ⟨hK,hp⟩
    refine ⟨hK,?_⟩
    intro hu
    obtain ⟨i,hi'⟩ := mem_iUnion.mp hu
    fin_cases i
    · exact hp hi'
    · exact hx (Or.inl hi')
    · exact hx (Or.inr hi')

/-- Exhaustive explicit families for the one-positive-plank stratum of the
original three-plank formula. The surviving plank is indexed by zero;
the two null planks are unrestricted apart from positive body ranges. -/
theorem equality_iff_fourPointBody {K : Set Point} (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (hV : 0 < (volume K).toReal)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (lo hi : Fin 3 → ℝ)
    (hW : ∀ i, 0 < rangeWidth K (f i)) (h0 : lo 0 < hi 0)
    (h1 : lo 1 = hi 1) (h2 : lo 2 = hi 2)
    (hR : (∑ i, (hi i-lo i)/rangeWidth K (f i)) < 1) :
    (volume (K \ ⋃ i, {x | lo i ≤ f i x ∧ f i x ≤ hi i})).toReal =
        (max 0 (1-∑ i, (hi i-lo i)/rangeWidth K (f i)))^2*(volume K).toReal ↔
      ∃ a ∈ K, ∃ b ∈ K, (∀ x ∈ K, f 0 x ≤ f 0 a) ∧ (∀ x ∈ K, f 0 b ≤ f 0 x) ∧
        f 0 b ≤ lo 0 ∧ hi 0 ≤ f 0 a ∧ ∃ c ∈ K, ∃ d ∈ K,
          f 0 c = f 0 b+(lo 0-f 0 b)/(1-(hi 0-lo 0)/rangeWidth K (f 0)) ∧
          f 0 d = f 0 b+(lo 0-f 0 b)/(1-(hi 0-lo 0)/rangeWidth K (f 0)) ∧
          K = fourPointBody a b c d := by
  have hsum : (∑ i, (hi i-lo i)/rangeWidth K (f i)) = (hi 0-lo 0)/rangeWidth K (f 0) := by
    simp only [Fin.sum_univ_three,← h1,← h2,sub_self,zero_div,add_zero]
  have hr : (hi 0-lo 0)/rangeWidth K (f 0) < 1 := by rwa [hsum] at hR
  rw [gap_eq_single hne f lo hi hW h1 h2,hsum,max_eq_right (sub_pos.mpr hr).le]
  exact PlanarOnePlankClassification.equality_iff_exists_fourPointBody
    hK hconv hne hV (f 0) (lo 0) (hi 0) h0 (hW 0) hr

end Plank.PlanarSingleActivePlank

/-- info: 'Plank.PlanarSingleActivePlank.equality_iff_fourPointBody' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.PlanarSingleActivePlank.equality_iff_fourPointBody
