/- The selected positive-gap body minimum is itself polygonal.
No replacement of its endpoints, support data or least-active property is needed. -/
module

public import PlanarRuledMinimum
public import FiniteDimensionalPositiveGap
public import FiniteHullHalfspaces
public import Plank.Proofs.Quant.PlanarStatement

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarGlobalPositivePolygon

open Set MeasureTheory PlanarQuantitative PrunedPlankCounterexample GlobalPlankBodyMinimum

/-- Boundary ruling and the uncovered-support count make the original minimum
a finite hull. Convert that hull to halfspaces only after polygonality is known. -/
theorem polygonal_of_positive_gap {m : ℕ} {K : Set Point}
    (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<volume.real K)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ)
    (hW : ∀ i,0<Body.width K (f i)) (ho : ∀ i,lo i≤hi i)
    (d : ℕ) {B : ℝ} (hB : B≤1) (hbudget : budget K f lo hi≤B)
    (hneg : GlobalPlankBodyMinimum.margin volume K f lo hi d B<0)
    (hglobal : IsGlobalMinimum volume K f lo hi d B)
    (hgap : 0<volume.real (K\covered f lo hi)) :
    ∃ (n : ℕ) (F : Fin n → Point →ᵃ[ℝ] ℝ) (c : Fin n → ℝ),
      K={x | ∀ j,F j x≤c j} := by
  obtain ⟨V,_,hull⟩ := PlanarRuledMinimum.eq_convexHull_at_most_eight_mul
    (by simp [Point]) volume hK hc hV f lo hi ho hW d hB hbudget hneg hglobal hgap
  rw [hull]
  exact FiniteHullHalfspaces.convexHull_eq_finite_halfspaces V

/-- Any strict planar failure supplies a polygonal negative global minimum
with positive gap and least-active endpoint selection, for every m.
The final 4m refinement is proved in PlanarFourMReduction. -/
theorem exists_negative_polygonal_minimum_positive_gap {m : ℕ} {K : Set Point}
    (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<volume.real K)
    (f : Fin m → Point →ᵃ[ℝ] ℝ) (lo hi : Fin m → ℝ)
    (hW : ∀ i,0<Body.width K (f i)) (ho : ∀ i,lo i≤hi i) {B : ℝ}
    (hB : B≤1) (hbudget : budget K f lo hi≤B)
    (hneg : GlobalPlankBodyMinimum.margin volume K f lo hi 2 B<0) :
    ∃ (C : Set Point) (g : Fin m → Point →ᵃ[ℝ] ℝ) (a b : Fin m → ℝ),
      IsCompact C ∧ Convex ℝ C ∧ 0<volume.real C ∧
      (∀ i,Body.width C (g i)=1) ∧ (∀ i x,x∈C → 0≤g i x ∧ g i x≤1) ∧
      (∀ i,a i≤b i) ∧ budget C g a b≤B ∧ GlobalPlankBodyMinimum.margin volume C g a b 2 B<0 ∧
      IsGlobalMinimum volume C g a b 2 B ∧
      GlobalPlankMergeMinimum.LeastActive volume C g a b 2 B ∧
      0<volume.real (C\covered g a b) ∧
      ∃ (n : ℕ) (F : Fin n → Point →ᵃ[ℝ] ℝ) (c : Fin n → ℝ),
        C={x | ∀ j,F j x≤c j} := by
  obtain ⟨C,g,a,b,hC,hCc,hCV,hunit,hnorm,hab,hbud,hnegative,hglobal,hactive,hgap⟩ :=
    FiniteDimensionalPositiveGap.exists_negative_minimum_positive_gap volume
      (by decide : 0<2) hK hc hV f lo hi hW ho hB hbudget hneg
  exact ⟨C,g,a,b,hC,hCc,hCV,hunit,hnorm,hab,hbud,hnegative,hglobal,hactive,hgap,
    polygonal_of_positive_gap hC hCc hCV g a b (fun i => by rw [hunit]; norm_num)
      hab 2 hB hbud hnegative hglobal hgap⟩

end Plank.PlanarGlobalPositivePolygon
