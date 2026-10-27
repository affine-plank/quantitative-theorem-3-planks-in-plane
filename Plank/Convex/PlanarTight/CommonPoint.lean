/- Positive internal tight covers in three distinct planar directions have
an actual common point. The equality argument retains cap rigidity. -/
module
public import Plank.Convex.PlanarTight.MinimalOppositeCaps
public import Plank.Convex.TwoDirectionThreePlanks
public import Plank.Convex.ThreeSetCoverIntersection
public import Mathlib.Logic.Equiv.Fintype
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.CommonPoint
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

private theorem allocate (K S U V : Set Point) (hSK : S ⊆ K)
    (hS : IsPreconnected S) (hU : IsClosed U) (hV : IsClosed V)
    (hdis : Disjoint (K ∩ U) (K ∩ V)) (hcover : S ⊆ U ∪ V) :
    S ⊆ U ∨ S ⊆ V := by
  classical
  by_cases hleft : S ⊆ U
  · exact Or.inl hleft
  right
  obtain ⟨x, hxS, hxU⟩ := Set.not_subset.mp hleft
  have hxV : x ∈ V := (hcover hxS).resolve_left hxU
  intro y hyS
  by_contra hyV
  have hyU : y ∈ U := (hcover hyS).resolve_right hyV
  obtain ⟨z, hzS, hzU, hzV⟩ := isPreconnected_closed_iff.mp hS U V hU hV
    hcover ⟨y, hyS, hyU⟩ ⟨x, hxS, hxV⟩
  exact Set.disjoint_left.mp hdis ⟨hSK hzS, hzU⟩ ⟨hSK hzS, hzV⟩

private theorem two_plank_bound (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j) (j : Fin 3)
    (hcover : ∀ p ∈ K, (lo j ≤ p j ∧ p j ≤ hi j) ∨
      (lo 1 ≤ p 1 ∧ p 1 ≤ hi 1)) :
    1 ≤ (hi j - lo j) + (hi 1 - lo 1) := by
  exact TwoAffineWindows.width_bound K hconv (AffineMap.proj j) (AffineMap.proj 1)
    (fun p hp => ⟨hbox p hp j, hbox p hp 1⟩)
    (lo j) (hi j) (lo 1) (hi 1) (hordered j) (hordered 1)
    (hmin j) (hmax j) (hmin 1) (hmax 1) hcover

private theorem cover_of_caps (K : Set Point) (lo hi : Fin 3 → ℝ) (j : Fin 3)
    (hlower : ∀ p ∈ K, p 1 < lo 1 → lo j ≤ p j ∧ p j ≤ hi j)
    (hupper : ∀ p ∈ K, hi 1 < p 1 → lo j ≤ p j ∧ p j ≤ hi j) :
    ∀ p ∈ K, (lo j ≤ p j ∧ p j ≤ hi j) ∨ (lo 1 ≤ p 1 ∧ p 1 ≤ hi 1) := by
  intro p hp
  by_cases hlo : p 1 < lo 1
  · exact Or.inl (hlower p hp hlo)
  by_cases hhi : hi 1 < p 1
  · exact Or.inl (hupper p hp hhi)
  exact Or.inr ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩

/-- With three nonzero plane coefficients and positive internal windows,
pair-intersection containment excludes equality. -/
theorem not_tight_of_pair_intersection_subset (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi A : Point) (D : ℝ) (hA : ∀ i, A i ≠ 0)
    (hplane : ∀ p ∈ K, ∑ i, A i * p i = D)
    (hwidth : ∀ j, lo j < hi j) (hlo : ∀ j, 0 < lo j) (hhi : ∀ j, hi j < 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hintersection : ∀ p ∈ K, (lo 0 ≤ p 0 ∧ p 0 ≤ hi 0) →
      (lo 2 ≤ p 2 ∧ p 2 ≤ hi 2) → lo 1 ≤ p 1 ∧ p 1 ≤ hi 1) :
    (∑ j, (hi j - lo j)) ≠ 1 := by
  intro hsum
  let U : Set Point := {p | lo 0 ≤ p 0 ∧ p 0 ≤ hi 0}
  let V : Set Point := {p | lo 2 ≤ p 2 ∧ p 2 ≤ hi 2}
  have hU : IsClosed U := (isClosed_le continuous_const (continuous_apply 0)).inter
    (isClosed_le (continuous_apply 0) continuous_const)
  have hV : IsClosed V := (isClosed_le continuous_const (continuous_apply 2)).inter
    (isClosed_le (continuous_apply 2) continuous_const)
  have hother (p : Point) (hp : p ∈ K) (hnot : ¬(lo 1 ≤ p 1 ∧ p 1 ≤ hi 1)) :
      p ∈ U ∪ V := by
    obtain ⟨j, hj⟩ := hcover p hp
    fin_cases j
    · exact Or.inl hj
    · exact False.elim (hnot hj)
    · exact Or.inr hj
  have hlower := allocate {p | p ∈ K ∧ p 1 < lo 1}
    {p | p ∈ K ∧ p 1 < lo 1} U V (fun _ hp => hp)
    (hconv.inter ((convex_Iio (lo 1)).linear_preimage
      (LinearMap.proj 1 : Point →ₗ[ℝ] ℝ))).isPreconnected hU hV (by
      apply Set.disjoint_left.mpr
      rintro p ⟨hp, h0⟩ ⟨_, h2⟩
      exact not_lt_of_ge (hintersection p hp.1 h0 h2).1 hp.2) (by
      intro p hp
      exact hother p hp.1 (fun h => not_lt_of_ge h.1 hp.2))
  have hupper := allocate {p | p ∈ K ∧ hi 1 < p 1}
    {p | p ∈ K ∧ hi 1 < p 1} U V (fun _ hp => hp)
    (hconv.inter ((convex_Ioi (hi 1)).linear_preimage
      (LinearMap.proj 1 : Point →ₗ[ℝ] ℝ))).isPreconnected hU hV (by
      apply Set.disjoint_left.mpr
      rintro p ⟨hp, h0⟩ ⟨_, h2⟩
      exact not_lt_of_ge (hintersection p hp.1 h0 h2).2 hp.2) (by
      intro p hp
      exact hother p hp.1 (fun h => not_lt_of_ge h.2 hp.2))
  rw [Fin.sum_univ_three] at hsum
  have h0 := hwidth 0
  have h2 := hwidth 2
  rcases hlower with hlower | hlower <;> rcases hupper with hupper | hupper
  · have htwo := two_plank_bound K hconv hbox hmin hmax lo hi (fun i => (hwidth i).le) 0
      (cover_of_caps K lo hi 0 (fun p hp hy => hlower ⟨hp, hy⟩)
        (fun p hp hy => hupper ⟨hp, hy⟩))
    linarith only [htwo, h2, hsum]
  · apply MinimalOppositeCaps.not_tight K hconv
      (AffineMap.proj 0) (AffineMap.proj 1) (AffineMap.proj 2)
      (fun p hp => hbox p hp 0) (fun p hp => hbox p hp 1) (fun p hp => hbox p hp 2)
      (hmin 0) (hmax 0) (hmin 1) (hmax 1) (hmin 2) (hmax 2)
      (lo 1) (hi 1) (lo 0) (hi 0) (lo 2) (hi 2)
      (hlo 1) (hwidth 1).le (hhi 1) (hlo 0) (hhi 0) h0.le (hlo 2).le (hhi 2).le h2.le
      (fun p hp hy => hlower ⟨hp, hy⟩) (fun p hp hy => hupper ⟨hp, hy⟩)
      (A 0) (A 1) (A 2) D (hA 0) (fun p hp => ?_) hsum
    simpa only [Fin.sum_univ_three, AffineMap.proj_apply] using hplane p hp
  · apply MinimalOppositeCaps.not_tight K hconv
      (AffineMap.proj 2) (AffineMap.proj 1) (AffineMap.proj 0)
      (fun p hp => hbox p hp 2) (fun p hp => hbox p hp 1) (fun p hp => hbox p hp 0)
      (hmin 2) (hmax 2) (hmin 1) (hmax 1) (hmin 0) (hmax 0)
      (lo 1) (hi 1) (lo 2) (hi 2) (lo 0) (hi 0)
      (hlo 1) (hwidth 1).le (hhi 1) (hlo 2) (hhi 2) h2.le (hlo 0).le (hhi 0).le h0.le
      (fun p hp hy => hlower ⟨hp, hy⟩) (fun p hp hy => hupper ⟨hp, hy⟩)
      (A 2) (A 1) (A 0) D (hA 2) (fun p hp => ?_) (by linarith only [hsum])
    have he := hplane p hp
    rw [Fin.sum_univ_three] at he
    change A 2 * p 2 + A 1 * p 1 + A 0 * p 0 = D
    linarith only [he]
  · have htwo := two_plank_bound K hconv hbox hmin hmax lo hi (fun i => (hwidth i).le) 2
      (cover_of_caps K lo hi 2 (fun p hp hy => hlower ⟨hp, hy⟩)
        (fun p hp hy => hupper ⟨hp, hy⟩))
    linarith only [htwo, h0, hsum]

/-- The pair-containment obstruction is invariant under coordinate order. -/
theorem not_tight_of_pair_intersection_subset_perm (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (σ : Equiv.Perm (Fin 3)) (lo hi A : Point) (D : ℝ) (hA : ∀ i, A i ≠ 0)
    (hplane : ∀ p ∈ K, ∑ i, A i * p i = D)
    (hwidth : ∀ j, lo j < hi j) (hlo : ∀ j, 0 < lo j) (hhi : ∀ j, hi j < 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hintersection : ∀ p ∈ K, (lo (σ 0) ≤ p (σ 0) ∧ p (σ 0) ≤ hi (σ 0)) →
      (lo (σ 2) ≤ p (σ 2) ∧ p (σ 2) ≤ hi (σ 2)) →
      lo (σ 1) ≤ p (σ 1) ∧ p (σ 1) ≤ hi (σ 1)) :
    (∑ j, (hi j - lo j)) ≠ 1 := by
  let e : Point →ᵃ[ℝ] Point := AffineMap.pi (fun j => AffineMap.proj (σ j))
  have hbox' : ∀ p ∈ e '' K, ∀ j, 0 ≤ p j ∧ p j ≤ 1 := by
    rintro _ ⟨p, hp, rfl⟩ j
    exact hbox p hp (σ j)
  have hmin' : ∀ j, ∃ p ∈ e '' K, p j = 0 := by
    intro j
    obtain ⟨p, hp, heq⟩ := hmin (σ j)
    exact ⟨e p, ⟨p, hp, rfl⟩, heq⟩
  have hmax' : ∀ j, ∃ p ∈ e '' K, p j = 1 := by
    intro j
    obtain ⟨p, hp, heq⟩ := hmax (σ j)
    exact ⟨e p, ⟨p, hp, rfl⟩, heq⟩
  have hplane' : ∀ p ∈ e '' K, ∑ j, A (σ j) * p j = D := by
    rintro _ ⟨p, hp, rfl⟩
    change (∑ j, A (σ j) * p (σ j)) = D
    simpa only [Equiv.sum_comp σ (fun j => A j * p j)] using hplane p hp
  have hbound := not_tight_of_pair_intersection_subset (e '' K) (Convex.affine_image e hconv)
    hbox' hmin' hmax' (fun j => lo (σ j)) (fun j => hi (σ j)) (fun j => A (σ j))
    D (fun j => hA (σ j)) hplane' (fun j => hwidth (σ j)) (fun j => hlo (σ j))
    (fun j => hhi (σ j)) (by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨j, hj⟩ := hcover p hp
      refine ⟨σ.symm j, ?_⟩
      change lo (σ (σ.symm j)) ≤ p (σ (σ.symm j)) ∧
        p (σ (σ.symm j)) ≤ hi (σ (σ.symm j))
      simpa only [σ.apply_symm_apply] using hj) (by
      rintro q ⟨p, hp, rfl⟩ h0 h2
      exact hintersection p hp h0 h2)
  simpa only [Equiv.sum_comp σ (fun j => hi j - lo j)] using hbound

/-- For each plank, the other two meet at a body point outside that plank.
This is stronger than pairwise intersection and includes boundary contacts. -/
theorem exists_pair_outside (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi A : Point) (D : ℝ) (hA : ∀ i, A i ≠ 0)
    (hplane : ∀ p ∈ K, ∑ i, A i * p i = D)
    (hwidth : ∀ j, lo j < hi j) (hlo : ∀ j, 0 < lo j) (hhi : ∀ j, hi j < 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hsum : (∑ j, (hi j - lo j)) = 1) :
    ∀ i, ∃ p ∈ K, (p i < lo i ∨ hi i < p i) ∧
      ∀ j, j ≠ i → lo j ≤ p j ∧ p j ≤ hi j := by
  intro i
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 i
  have hσ : σ 1 = i := Equiv.swap_apply_left 1 i
  by_contra hnone
  have hintersection : ∀ p ∈ K,
      (lo (σ 0) ≤ p (σ 0) ∧ p (σ 0) ≤ hi (σ 0)) →
      (lo (σ 2) ≤ p (σ 2) ∧ p (σ 2) ≤ hi (σ 2)) →
      lo (σ 1) ≤ p (σ 1) ∧ p (σ 1) ≤ hi (σ 1) := by
    intro p hp h0 h2
    rw [hσ]
    by_contra hnot
    have hout : p i < lo i ∨ hi i < p i := by
      simpa only [not_and_or, not_le] using hnot
    apply hnone
    refine ⟨p, hp, hout, ?_⟩
    intro j hji
    have hk : σ.symm j ≠ 1 := by
      intro heq
      apply hji
      calc
        j = σ (σ.symm j) := (σ.apply_symm_apply j).symm
        _ = i := by rw [heq, hσ]
    have hforeign : ∀ k : Fin 3, k ≠ 1 →
        lo (σ k) ≤ p (σ k) ∧ p (σ k) ≤ hi (σ k) := by
      intro k hne
      fin_cases k
      · exact h0
      · exact False.elim (hne rfl)
      · exact h2
    simpa only [σ.apply_symm_apply] using hforeign (σ.symm j) hk
  exact not_tight_of_pair_intersection_subset_perm K hconv hbox hmin hmax
    σ lo hi A D hA hplane hwidth hlo hhi hcover hintersection hsum

/-- Every pair in a positive internal tight planar cover meets inside the
body. Nonzero plane coefficients express the three distinct directions. -/
theorem pairwise_intersect (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi A : Point) (D : ℝ) (hA : ∀ i, A i ≠ 0)
    (hplane : ∀ p ∈ K, ∑ i, A i * p i = D)
    (hwidth : ∀ j, lo j < hi j) (hlo : ∀ j, 0 < lo j) (hhi : ∀ j, hi j < 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hsum : (∑ j, (hi j - lo j)) = 1) :
    ∀ i j, i ≠ j → ∃ p ∈ K,
      (lo i ≤ p i ∧ p i ≤ hi i) ∧ (lo j ≤ p j ∧ p j ≤ hi j) := by
  intro i j hij
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (![0, 2] : Fin 2 → Fin 3) (![i, j] : Fin 2 → Fin 3)
    (by decide) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all)
  have hσ0 : σ 0 = i := hσ 0
  have hσ2 : σ 2 = j := hσ 1
  by_contra hnone
  apply not_tight_of_pair_intersection_subset_perm K hconv hbox hmin hmax σ
    lo hi A D hA hplane hwidth hlo hhi hcover (fun p hp h0 h2 => ?_) hsum
  exact False.elim (hnone ⟨p, hp, by simpa only [hσ0] using h0,
    by simpa only [hσ2] using h2⟩)

/-- A positive internal tight planar cover in three distinct directions
has a point in the body common to all three closed planks. No compactness
or minimum-cover hypothesis is needed. -/
theorem exists_common (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi A : Point) (D : ℝ) (hA : ∀ i, A i ≠ 0)
    (hplane : ∀ p ∈ K, ∑ i, A i * p i = D)
    (hwidth : ∀ j, lo j < hi j) (hlo : ∀ j, 0 < lo j) (hhi : ∀ j, hi j < 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hsum : (∑ j, (hi j - lo j)) = 1) :
    ∃ p ∈ K, ∀ j, lo j ≤ p j ∧ p j ≤ hi j := by
  let P (j : Fin 3) : Set Point := {p | lo j ≤ p j ∧ p j ≤ hi j}
  have hPc (j : Fin 3) : IsClosed (P j) :=
    (isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_le (continuous_apply j) continuous_const)
  have hPv (j : Fin 3) : Convex ℝ (P j) :=
    (convex_Icc (lo j) (hi j)).linear_preimage (LinearMap.proj j : Point →ₗ[ℝ] ℝ)
  have hpair := pairwise_intersect K hconv hbox hmin hmax lo hi A D hA hplane
    hwidth hlo hhi hcover hsum
  have hpair' (i j : Fin 3) (hij : i ≠ j) : (K ∩ P i ∩ P j).Nonempty := by
    obtain ⟨p, hp, hpi, hpj⟩ := hpair i j hij
    exact ⟨p, ⟨hp, hpi⟩, hpj⟩
  have hcov : K ⊆ P 0 ∪ P 1 ∪ P 2 := by
    intro p hp
    obtain ⟨j, hj⟩ := hcover p hp
    fin_cases j
    · exact Or.inl (Or.inl hj)
    · exact Or.inl (Or.inr hj)
    · exact Or.inr hj
  obtain ⟨p, ⟨⟨hp, hp0⟩, hp1⟩, hp2⟩ :=
    ThreeSetCoverIntersection.triple_nonempty K (P 0) (P 1) (P 2) hconv
      (hPv 0) (hPv 1) (hPv 2) (hPc 0) (hPc 1) (hPc 2) hcov
      (hpair' 0 1 (by decide)) (hpair' 0 2 (by decide)) (hpair' 1 2 (by decide))
  refine ⟨p, hp, ?_⟩
  intro j
  fin_cases j
  · exact hp0
  · exact hp1
  · exact hp2

/-- For a positive plane normal, the common point puts the plane between
both window-box corners. These non-strict bounds are valid at equality. -/
theorem plane_box_bounds (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi A : Point) (D : ℝ) (hA : ∀ i, 0 < A i)
    (hplane : ∀ p ∈ K, ∑ i, A i * p i = D)
    (hwidth : ∀ j, lo j < hi j) (hlo : ∀ j, 0 < lo j) (hhi : ∀ j, hi j < 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hsum : (∑ j, (hi j - lo j)) = 1) :
    (∑ i, A i * lo i) ≤ D ∧ D ≤ ∑ i, A i * hi i := by
  obtain ⟨p, hp, hmem⟩ := exists_common K hconv hbox hmin hmax lo hi A D
    (fun i => (hA i).ne') hplane hwidth hlo hhi hcover hsum
  rw [← hplane p hp]
  exact ⟨Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hmem i).1 (hA i).le),
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hmem i).2 (hA i).le)⟩

end Plank.Convex.PlanarTight.CommonPoint

/-- info: 'Plank.Convex.PlanarTight.CommonPoint.not_tight_of_pair_intersection_subset_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CommonPoint.not_tight_of_pair_intersection_subset_perm

/-- info: 'Plank.Convex.PlanarTight.CommonPoint.exists_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CommonPoint.exists_common

/-- info: 'Plank.Convex.PlanarTight.CommonPoint.exists_pair_outside' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CommonPoint.exists_pair_outside

/-- info: 'Plank.Convex.PlanarTight.CommonPoint.plane_box_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.CommonPoint.plane_box_bounds
