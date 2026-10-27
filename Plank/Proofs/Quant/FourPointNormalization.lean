/- Affine normalization of every positive-area hull with at most four vertices. -/
module

public import Plank.Proofs.Quant.FourPointPlacements
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Analysis.Convex.Measure

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FourPointNormalization

open Set MeasureTheory PlanarQuantitative FourPointHalfplanes
open scoped BigOperators

def coords (b : AffineBasis (Fin 3) ℝ Point) : Point →ᵃ[ℝ] Point :=
  AffineMap.pi (fun i : Fin 2 => b.coord i.succ)

theorem coords_bijective (b : AffineBasis (Fin 3) ℝ Point) : Function.Bijective (coords b) := by
  constructor
  · intro x y h
    have h1 : b.coord 1 x = b.coord 1 y := congrFun h 0
    have h2 : b.coord 2 x = b.coord 2 y := congrFun h 1
    apply b.ext_elem
    intro i
    fin_cases i
    · change b.coord 0 x = b.coord 0 y
      have hx := b.sum_coord_apply_eq_one x
      have hy := b.sum_coord_apply_eq_one y
      simp only [Fin.sum_univ_three] at hx hy
      linarith only [hx,hy,h1,h2]
    · exact h1
    · exact h2
  · intro y
    let w : Fin 3 → ℝ := ![1-y 0-y 1,y 0,y 1]
    have hw : ∑ i, w i = 1 := by simp [w,Fin.sum_univ_three]; ring
    refine ⟨Finset.univ.affineCombination ℝ b w,?_⟩
    ext i
    fin_cases i <;>
      exact b.coord_apply_combination_of_mem (Finset.mem_univ _) hw

def chart (b : AffineBasis (Fin 3) ℝ Point) : Point ≃ᵃ[ℝ] Point :=
  AffineEquiv.ofBijective (coords_bijective b)

theorem chart_basis (b : AffineBasis (Fin 3) ℝ Point) (i : Fin 3) :
    chart b (b i) = (![![0,0],![1,0],![0,1]] : Fin 3 → Point) i := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [chart,coords]

theorem image_basis (b : AffineBasis (Fin 3) ℝ Point) :
    chart b '' Set.range b = {![0,0],![1,0],![0,1]} := by
  rw [← Set.range_comp]
  change Set.range (fun i => chart b (b i)) = _
  have he : (fun i => chart b (b i)) = (![![0,0],![1,0],![0,1]] : Fin 3 → Point) :=
    funext (chart_basis b)
  rw [he]
  ext x
  simp [or_comm,or_left_comm]

/-- A spanning set of at most four planar points consists of an affine
basis and at most one additional point; a repeated point handles triangles. -/
theorem basis_and_extra (v : Finset Point) (hv : v.card ≤ 4)
    (hspan : affineSpan ℝ (v : Set Point) = ⊤) :
    ∃ (b : AffineBasis (Fin 3) ℝ Point) (d : Point),
      (v : Set Point) = Set.range b ∪ {d} := by
  classical
  obtain ⟨s,hsv,b,hb⟩ := AffineBasis.exists_affine_subbasis hspan
  lift s to Finset Point using b.finite_set
  have hsub : s ⊆ v := hsv
  have hc : Fintype.card s = Fintype.card (Fin 3) := by
    simpa using b.card_eq_finrank_add_one
  let e : s ≃ Fin 3 := Fintype.equivOfCardEq hc
  let b' := b.reindex e
  have hr : Set.range b' = (s : Set Point) := by
    change Set.range (b ∘ e.symm) = _
    rw [e.symm.surjective.range_comp,hb,Subtype.range_coe]
  have hsc : s.card = 3 := by simpa using hc
  have hrest : (v \ s).card ≤ 1 := by
    have hh := Finset.card_sdiff_add_card_eq_card hsub
    omega
  by_cases hn : (v \ s).Nonempty
  · obtain ⟨d,hd⟩ := hn
    refine ⟨b',d,?_⟩
    rw [hr]
    ext x
    constructor
    · intro hx
      by_cases hs : x ∈ s
      · exact Or.inl hs
      · exact Or.inr ((Finset.card_le_one.mp hrest) x (Finset.mem_sdiff.mpr ⟨hx,hs⟩) d hd)
    · rintro (hx | rfl)
      · exact hsub hx
      · exact (Finset.mem_sdiff.mp hd).1
  · refine ⟨b',b' 0,?_⟩
    have hb0 : b' 0 ∈ s := by
      have hh := Set.mem_range_self (f := b') 0
      rwa [hr] at hh
    rw [hr]
    ext x
    constructor
    · intro hx
      apply Or.inl
      by_contra hs
      exact hn ⟨x,Finset.mem_sdiff.mpr ⟨hx,hs⟩⟩
    · rintro (hx | rfl)
      · exact hsub hx
      · exact hsub hb0

/-- Every positive-area hull of at most four points admits the exact
normalization used by the explicit placement test. No convex-position or
independence hypothesis on the listed vertices is needed. -/
theorem normalize (v : Finset Point) (hv : v.card ≤ 4)
    (hV : 0 < (volume (convexHull ℝ (v : Set Point))).toReal) :
    ∃ (T : Point ≃ᵃ[ℝ] Point) (a b : ℝ), T '' convexHull ℝ (v : Set Point) = body a b := by
  have hspan : affineSpan ℝ (v : Set Point) = ⊤ := by
    by_contra hn
    have hz := measure_mono_null (convexHull_subset_affineSpan (𝕜 := ℝ) (v : Set Point))
      (Measure.addHaar_affineSubspace volume _ hn)
    simp only [hz,ENNReal.toReal_zero,lt_self_iff_false] at hV
  obtain ⟨b,d,hd⟩ := basis_and_extra v hv hspan
  refine ⟨chart b,chart b d 0,chart b d 1,?_⟩
  change (chart b).toAffineMap '' convexHull ℝ (v : Set Point) = _
  rw [(chart b).toAffineMap.image_convexHull,hd,Set.image_union,Set.image_singleton]
  change convexHull ℝ ((chart b '' Set.range b) ∪ {chart b d}) = _
  rw [image_basis]
  have hd' : chart b d = ![chart b d 0,chart b d 1] := by ext i; fin_cases i <;> rfl
  change convexHull ℝ ({![0,0],![1,0],![0,1]} ∪ {chart b d}) =
    convexHull ℝ {![0,0],![1,0],![0,1],![chart b d 0,chart b d 1]}
  congr 1
  rw [← hd']
  ext x
  simp only [mem_union,mem_insert_iff,mem_singleton_iff]
  tauto

end Plank.FourPointNormalization

/-- info: 'Plank.FourPointNormalization.normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.FourPointNormalization.normalize
