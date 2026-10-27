/- Removing redundant affine inequalities gives a strict point on every facet.
This is a geometric adapter, not the planar polygon-count theorem. -/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.IrredundantHalfspaces

open Set

variable {E ι : Type*}

/-- Every finite family of predicates has a subfamily with the same
intersection in which each retained predicate is necessary. -/
theorem exists_irredundant_subfamily (s : Finset ι) (P : ι → E → Prop) :
    ∃ t ⊆ s, (∀ x, (∀ i ∈ t, P i x) ↔ ∀ i ∈ s, P i x) ∧
      ∀ i ∈ t, ∃ z, ¬ P i z ∧ ∀ j ∈ t, j ≠ i → P j z := by
  classical
  let candidates := s.powerset.filter fun t =>
    ∀ x, (∀ i ∈ t, P i x) ↔ ∀ i ∈ s, P i x
  have hne : candidates.Nonempty := ⟨s, by simp [candidates]⟩
  obtain ⟨t, ht, hmin⟩ := candidates.exists_min_image Finset.card hne
  have hts : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
  have heq := (Finset.mem_filter.mp ht).2
  refine ⟨t, hts, heq, ?_⟩
  intro i hi
  by_contra! hn
  have herase : ∀ x, (∀ j ∈ t.erase i, P j x) ↔ ∀ j ∈ s, P j x := by
    intro x
    constructor
    · intro hx
      apply (heq x).mp
      intro j hj
      by_cases hji : j = i
      · subst j
        by_contra hbad
        obtain ⟨k, hk, hki, hfail⟩ := hn x hbad
        exact hfail (hx k (Finset.mem_erase.mpr ⟨hki, hk⟩))
      · exact hx j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    · intro hx j hj
      exact hx j (hts (Finset.mem_of_mem_erase hj))
  have hm := hmin (t.erase i) (Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.erase_subset i t |>.trans hts), herase⟩)
  exact (Finset.card_erase_lt_of_mem hi).not_ge hm

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A nonconstant affine inequality is strict at an interior point of a
set lying in its closed halfspace. -/
theorem strict_at_interior (f : E →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    {K : Set E} {b : ℝ} (hside : ∀ x ∈ K, f x ≤ b)
    {x : E} (hx : x ∈ interior K) : f x < b := by
  have hopen : IsOpenMap f := AffineMap.isOpenMap_linear_iff.mp
    (f.linear.isOpenMap_of_finiteDimensional (LinearMap.surjective_iff_ne_zero.mpr hf))
  have hsub : K ⊆ f ⁻¹' Iic b := hside
  have hmem := interior_mono hsub hx
  rw [← hopen.preimage_interior_eq_interior_preimage
    f.continuous_of_finiteDimensional, interior_Iic] at hmem
  exact hmem

omit [FiniteDimensional ℝ E] in
/-- Move from a strictly feasible point towards a witness to necessity of
one row. Its first contact with that row is strict in every other row. -/
theorem exists_strict_facet_point (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) (x : E) (hx : ∀ j ∈ s, f j x < b j)
    (i : ι) (hi : i ∈ s) (z : E) (hz : b i < f i z)
    (hother : ∀ j ∈ s, j ≠ i → f j z ≤ b j) :
    ∃ p, f i p = b i ∧ ∀ j ∈ s, j ≠ i → f j p < b j := by
  let t := (b i - f i x) / (f i z - f i x)
  have hden : 0 < f i z - f i x := by linarith [hx i hi]
  have ht0 : 0 < t := div_pos (sub_pos.mpr (hx i hi)) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  refine ⟨AffineMap.lineMap x z t, ?_, ?_⟩
  · rw [(f i).apply_lineMap, AffineMap.lineMap_apply_ring']
    dsimp [t]
    rw [div_mul_cancel₀ _ hden.ne']
    ring
  · intro j hj hji
    rw [(f j).apply_lineMap, AffineMap.lineMap_apply_ring]
    have hleft := mul_lt_mul_of_pos_left (hx j hj) (sub_pos.mpr ht1)
    have hright := mul_le_mul_of_nonneg_left (hother j hj hji) ht0.le
    nlinarith

/-- A full-dimensional finite halfspace intersection admits a subpresentation
with a nonconstant row and a strict facet point for every retained inequality.
No cyclic ordering or bound on the number of facets is asserted here. -/
theorem exists_facet_presentation (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) {K : Set E} (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i)
    (hint : (interior K).Nonempty) :
    ∃ t ⊆ s, (∀ x, x ∈ K ↔ ∀ i ∈ t, f i x ≤ b i) ∧
      ∀ i ∈ t, (f i).linear ≠ 0 ∧
        ∃ p, f i p = b i ∧ ∀ j ∈ t, j ≠ i → f j p < b j := by
  obtain ⟨t, hts, heq, hnecess⟩ :=
    exists_irredundant_subfamily s (fun i x => f i x ≤ b i)
  obtain ⟨x, hx⟩ := hint
  have hKx := interior_subset hx
  have hnonzero : ∀ i ∈ t, (f i).linear ≠ 0 := by
    intro i hi hzero
    obtain ⟨z, hz, _⟩ := hnecess i hi
    obtain ⟨c, hc⟩ := ((f i).linear_eq_zero_iff_exists_const).mp hzero
    have hle := (hrep x).mp hKx i (hts hi)
    exact hz (by simpa [hc] using hle)
  have hstrict : ∀ i ∈ t, f i x < b i := by
    intro i hi
    exact strict_at_interior (f i) (hnonzero i hi)
      (fun y hy => (hrep y).mp hy i (hts hi)) hx
  refine ⟨t, hts, fun y => (hrep y).trans (heq y).symm, ?_⟩
  intro i hi
  obtain ⟨z, hz, hother⟩ := hnecess i hi
  exact ⟨hnonzero i hi, exists_strict_facet_point t f b x hstrict i hi z
    (lt_of_not_ge hz) hother⟩

/-- In a finite presentation, a feasible point off the interior activates
at least one defining inequality. -/
theorem exists_active_row (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) {K : Set E} (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i)
    {x : E} (hx : x ∈ K) (hboundary : x ∉ interior K) :
    ∃ i ∈ s, f i x = b i := by
  by_contra! hn
  let U := ⋂ i ∈ s, {y : E | f i y < b i}
  have hU : IsOpen U := isOpen_biInter_finset fun i _ =>
    isOpen_lt (f i).continuous_of_finiteDimensional continuous_const
  have hUK : U ⊆ K := by
    intro y hy
    apply (hrep y).mpr
    intro i hi
    exact (mem_iInter.mp (mem_iInter.mp hy i) hi).le
  apply hboundary
  apply interior_maximal hUK hU
  simp only [U, mem_iInter, mem_ofPred_eq]
  intro i hi
  exact lt_of_le_of_ne ((hrep x).mp hx i hi) (hn i hi)

/-- If the midpoint of a feasible segment is a boundary point, one defining
row is an equality at both endpoints. -/
theorem exists_row_through_endpoints (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ)
    (b : ι → ℝ) {K : Set E} (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i)
    {u v : E} (hu : u ∈ K) (hv : v ∈ K)
    (hboundary : AffineMap.lineMap u v (1/2 : ℝ) ∉ interior K) :
    ∃ i ∈ s, f i u = b i ∧ f i v = b i := by
  have hmid : AffineMap.lineMap u v (1/2 : ℝ) ∈ K := by
    apply (hrep _).mpr
    intro i hi
    rw [(f i).apply_lineMap, AffineMap.lineMap_apply_ring]
    linarith [(hrep u).mp hu i hi, (hrep v).mp hv i hi]
  obtain ⟨i, hi, heq⟩ := exists_active_row s f b hrep hmid hboundary
  rw [(f i).apply_lineMap, AffineMap.lineMap_apply_ring] at heq
  refine ⟨i, hi, ?_, ?_⟩ <;>
    linarith [(hrep u).mp hu i hi, (hrep v).mp hv i hi]

/-- In dimension two, a nonconstant affine level is determined by any two
distinct points on it. Here the second affine function may be constant. -/
theorem level_subset_of_two_points (hdim : Module.finrank ℝ E = 2)
    (g f : E →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0) (b c : ℝ)
    (u v : E) (huv : u ≠ v) (hgu : g u = b) (hgv : g v = b)
    (hfu : f u = c) (hfv : f v = c) :
    {x | g x = b} ⊆ {x | f x = c} := by
  have hker (q : E) (hq : g q = b) : q-u ∈ g.linear.ker := by
    change g.linear (q-u) = 0
    simpa only [vsub_eq_sub, hq, hgu, sub_self] using g.linearMap_vsub q u
  let w : g.linear.ker := ⟨v-u, hker v hgv⟩
  have hw : w ≠ 0 := by
    intro he
    have hh := congrArg Subtype.val he
    change v-u = 0 at hh
    exact huv (sub_eq_zero.mp hh).symm
  have hrank : Module.finrank ℝ g.linear.ker = 1 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hg
    rw [hdim] at h
    omega
  have hspan := (finrank_eq_one_iff_of_nonzero' (K := ℝ) w hw).mp hrank
  intro z hz
  obtain ⟨t, ht⟩ := hspan ⟨z-u, hker z hz⟩
  have ht' : t • (v-u) = z-u := congrArg Subtype.val ht
  have hfzero : f.linear (v-u) = 0 := by
    simpa only [vsub_eq_sub, hfu, hfv, sub_self] using f.linearMap_vsub v u
  have he := f.linearMap_vsub z u
  change f.linear (z-u) = f z - f u at he
  rw [← ht', f.linear.map_smul, hfzero, smul_zero, hfu] at he
  exact (sub_eq_zero.mp he.symm)

/-- Every nondegenerate exposed face of a planar finite halfspace intersection
is the face of a row in any nonconstant presentation. This identifies the
actual supporting line, not just its direction. -/
theorem exists_row_for_planar_face (hdim : Module.finrank ℝ E = 2)
    (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ) (b : ι → ℝ)
    (hf : ∀ i ∈ s, (f i).linear ≠ 0) {K : Set E}
    (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i)
    (g : E →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0) (c : ℝ)
    (hside : ∀ x ∈ K, g x ≤ c) (u v : E) (huv : u ≠ v)
    (hu : u ∈ K) (hv : v ∈ K) (hgu : g u = c) (hgv : g v = c) :
    ∃ i ∈ s, {x | g x = c} = {x | f i x = b i} := by
  have hmid : g (AffineMap.lineMap u v (1/2 : ℝ)) = c := by
    rw [g.apply_lineMap, hgu, hgv, AffineMap.lineMap_same_apply]
  have hboundary : AffineMap.lineMap u v (1/2 : ℝ) ∉ interior K := by
    intro hin
    have hh := strict_at_interior g hg hside hin
    rw [hmid] at hh
    exact lt_irrefl _ hh
  obtain ⟨i, hi, hiu, hiv⟩ := exists_row_through_endpoints s f b hrep hu hv hboundary
  exact ⟨i, hi, Set.Subset.antisymm
    (level_subset_of_two_points hdim g (f i) hg c (b i) u v huv hgu hgv hiu hiv)
    (level_subset_of_two_points hdim (f i) g (hf i hi) (b i) c u v huv hiu hiv hgu hgv)⟩

/-- The finite-halfspace adapter for an actual planar edge: an isolated
defining row on exactly its supporting line, with strict slack in every other
retained row at a point of that edge. -/
theorem exists_planar_edge_description (hdim : Module.finrank ℝ E = 2)
    (s : Finset ι) (f : ι → E →ᵃ[ℝ] ℝ) (b : ι → ℝ)
    {K : Set E} (hrep : ∀ x, x ∈ K ↔ ∀ i ∈ s, f i x ≤ b i)
    (hint : (interior K).Nonempty) (g : E →ᵃ[ℝ] ℝ) (hg : g.linear ≠ 0)
    (c : ℝ) (hside : ∀ x ∈ K, g x ≤ c) (u v : E) (huv : u ≠ v)
    (hu : u ∈ K) (hv : v ∈ K) (hgu : g u = c) (hgv : g v = c) :
    ∃ (t : Finset ι) (i : ι) (p : E), t ⊆ s ∧ i ∈ t ∧
      (∀ x, x ∈ K ↔ f i x ≤ b i ∧ ∀ j ∈ t, j ≠ i → f j x ≤ b j) ∧
      (f i).linear ≠ 0 ∧ {x | g x = c} = {x | f i x = b i} ∧
      f i p = b i ∧ ∀ j ∈ t, j ≠ i → f j p < b j := by
  classical
  obtain ⟨t, hts, hrep', hfacets⟩ := exists_facet_presentation s f b hrep hint
  obtain ⟨i, hi, hlevel⟩ := exists_row_for_planar_face hdim t f b
    (fun i hi => (hfacets i hi).1) hrep' g hg c hside u v huv hu hv hgu hgv
  obtain ⟨hnonzero, p, hp, hstrict⟩ := hfacets i hi
  refine ⟨t, i, p, hts, hi, ?_, hnonzero, hlevel, hp, hstrict⟩
  intro x
  rw [hrep' x]
  constructor
  · intro h
    exact ⟨h i hi, fun j hj _ => h j hj⟩
  · rintro ⟨h, hother⟩ j hj
    by_cases hji : j = i
    · simpa [hji] using h
    · exact hother j hj hji

end Plank.IrredundantHalfspaces
