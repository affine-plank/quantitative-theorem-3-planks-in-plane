/- If the intersection of two members of a three-coordinate cover lies
inside the third, total width is at least one. Convex open caps allocate
to one closed plank each. A deficit therefore forces a pair-intersection
point outside each third plank. -/
module
public import Plank.Convex.TwoDirectionThreePlanks
public import Mathlib.Logic.Equiv.Fintype
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.DisconnectedPlankCover
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

private theorem lower_cap_bound (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (j : Fin 3) (a l h : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hlh : l ≤ h)
    (hcap : ∀ p ∈ K, p 1 < a → l ≤ p j ∧ p j ≤ h) :
    a ≤ h - l := by
  obtain ⟨pL, hpL, hxL⟩ := hmin j
  obtain ⟨pR, hpR, hxR⟩ := hmax j
  obtain ⟨pB, hpB, hyB⟩ := hmin 1
  exact ConvexCapWidth.cap_bound_lower_coord K hconv j 1 hbox pL pR pB
    hpL hpR hpB hxL hxR hyB a ha0 ha1 l h hlh hcap

private theorem upper_cap_bound (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (j : Fin 3) (b l h : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hlh : l ≤ h)
    (hcap : ∀ p ∈ K, b < p 1 → l ≤ p j ∧ p j ≤ h) :
    1 - b ≤ h - l := by
  obtain ⟨pL, hpL, hxL⟩ := hmin j
  obtain ⟨pR, hpR, hxR⟩ := hmax j
  obtain ⟨pT, hpT, hyT⟩ := hmax 1
  exact ConvexCapWidth.cap_bound_upper_coord K hconv j 1 hbox pL pR pT
    hpL hpR hpT hxL hxR hyT b hb0 hb1 l h hlh hcap

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

/-- If the intersection of the outer two planks inside the body is contained
in the middle plank, total width is at least one. Only the middle window
needs clipping to `[0,1]`; zero-width windows are allowed. -/
theorem sum_ge_one_of_pair_intersection_subset (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : 0 ≤ lo 1) (hhi : hi 1 ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hintersection : ∀ p ∈ K, (lo 0 ≤ p 0 ∧ p 0 ≤ hi 0) →
      (lo 2 ≤ p 2 ∧ p 2 ≤ hi 2) → lo 1 ≤ p 1 ∧ p 1 ≤ hi 1) :
    1 ≤ ∑ j, (hi j - lo j) := by
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
  rw [Fin.sum_univ_three]
  have h0 := hordered 0
  have h2 := hordered 2
  rcases hlower with hlower | hlower <;> rcases hupper with hupper | hupper
  · have htwo := two_plank_bound K hconv hbox hmin hmax lo hi hordered 0
      (cover_of_caps K lo hi 0 (fun p hp hy => hlower ⟨hp, hy⟩)
        (fun p hp hy => hupper ⟨hp, hy⟩))
    linarith only [htwo, h2]
  · have hl := lower_cap_bound K hconv hbox hmin hmax 0 (lo 1) (lo 0) (hi 0)
      hlo ((hordered 1).trans hhi) h0 (fun p hp hy => hlower ⟨hp, hy⟩)
    have hu := upper_cap_bound K hconv hbox hmin hmax 2 (hi 1) (lo 2) (hi 2)
      (hlo.trans (hordered 1)) hhi h2 (fun p hp hy => hupper ⟨hp, hy⟩)
    linarith only [hl, hu]
  · have hl := lower_cap_bound K hconv hbox hmin hmax 2 (lo 1) (lo 2) (hi 2)
      hlo ((hordered 1).trans hhi) h2 (fun p hp hy => hlower ⟨hp, hy⟩)
    have hu := upper_cap_bound K hconv hbox hmin hmax 0 (hi 1) (lo 0) (hi 0)
      (hlo.trans (hordered 1)) hhi h0 (fun p hp hy => hupper ⟨hp, hy⟩)
    linarith only [hl, hu]
  · have htwo := two_plank_bound K hconv hbox hmin hmax lo hi hordered 2
      (cover_of_caps K lo hi 2 (fun p hp hy => hlower ⟨hp, hy⟩)
        (fun p hp hy => hupper ⟨hp, hy⟩))
    linarith only [htwo, h0]

/-- Two disjoint clipped planks in a whole-set coordinate cover force
total width at least one. Only the middle window needs clipping to `[0,1]`;
all three windows may have zero width. -/
theorem sum_ge_one_of_disjoint (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : 0 ≤ lo 1) (hhi : hi 1 ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hdisjoint : Disjoint (K ∩ {p | lo 0 ≤ p 0 ∧ p 0 ≤ hi 0})
      (K ∩ {p | lo 2 ≤ p 2 ∧ p 2 ≤ hi 2})) :
    1 ≤ ∑ j, (hi j - lo j) :=
  sum_ge_one_of_pair_intersection_subset K hconv hbox hmin hmax lo hi hordered
    hlo hhi hcover (fun _p hp h0 h2 =>
      False.elim (Set.disjoint_left.mp hdisjoint ⟨hp, h0⟩ ⟨hp, h2⟩))

/-- The pair-intersection containment bound in any coordinate order. The middle window
`σ 1` is the only one required to lie within the unit interval. -/
theorem sum_ge_one_of_pair_intersection_subset_perm (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (σ : Equiv.Perm (Fin 3)) (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : 0 ≤ lo (σ 1)) (hhi : hi (σ 1) ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hintersection : ∀ p ∈ K, (lo (σ 0) ≤ p (σ 0) ∧ p (σ 0) ≤ hi (σ 0)) →
      (lo (σ 2) ≤ p (σ 2) ∧ p (σ 2) ≤ hi (σ 2)) →
      lo (σ 1) ≤ p (σ 1) ∧ p (σ 1) ≤ hi (σ 1)) :
    1 ≤ ∑ j, (hi j - lo j) := by
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
  have hbound := sum_ge_one_of_pair_intersection_subset (e '' K) (Convex.affine_image e hconv)
    hbox' hmin' hmax' (fun j => lo (σ j)) (fun j => hi (σ j))
    (fun j => hordered (σ j)) hlo hhi (by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨j, hj⟩ := hcover p hp
      refine ⟨σ.symm j, ?_⟩
      change lo (σ (σ.symm j)) ≤ p (σ (σ.symm j)) ∧
        p (σ (σ.symm j)) ≤ hi (σ (σ.symm j))
      simpa only [σ.apply_symm_apply] using hj) (by
      rintro q ⟨p, hp, rfl⟩ h0 h2
      exact hintersection p hp h0 h2)
  simpa only [Equiv.sum_comp σ (fun j => hi j - lo j)] using hbound

/-- The disjoint-plank bound in any coordinate order. The middle window
`σ 1` is the only one required to lie within the unit interval. -/
theorem sum_ge_one_of_disjoint_perm (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (σ : Equiv.Perm (Fin 3)) (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : 0 ≤ lo (σ 1)) (hhi : hi (σ 1) ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hdisjoint : Disjoint (K ∩ {p | lo (σ 0) ≤ p (σ 0) ∧ p (σ 0) ≤ hi (σ 0)})
      (K ∩ {p | lo (σ 2) ≤ p (σ 2) ∧ p (σ 2) ≤ hi (σ 2)})) :
    1 ≤ ∑ j, (hi j - lo j) :=
  sum_ge_one_of_pair_intersection_subset_perm K hconv hbox hmin hmax σ lo hi hordered
    hlo hhi hcover (fun _p hp h0 h2 =>
      False.elim (Set.disjoint_left.mp hdisjoint ⟨hp, h0⟩ ⟨hp, h2⟩))

/-- In a deficient cover, for every plank there is a point of the body
outside that plank but in both others. At least one of each pair of
opposite box faces therefore has an exterior column contact. -/
theorem exists_pair_outside_of_deficit (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : ∀ j, 0 ≤ lo j) (hhi : ∀ j, hi j ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hdef : (∑ j, (hi j - lo j)) < 1) :
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
  exact not_lt_of_ge (sum_ge_one_of_pair_intersection_subset_perm K hconv hbox hmin hmax
    σ lo hi hordered (hlo (σ 1)) (hhi (σ 1)) hcover hintersection) hdef

private theorem pair_permutation (i j : Fin 3) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 2 = j := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (![0, 2] : Fin 2 → Fin 3) (![i, j] : Fin 2 → Fin 3)
    (by decide) (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all)
  exact ⟨σ, hσ 0, hσ 1⟩

/-- In a deficient whole-set cover, every two distinct clipped planks
have an actual common point of `K`. This is set intersection, including
boundary points, and makes no assertion about positive-volume overlap. -/
theorem pairwise_intersect_of_deficit (K : Set Point) (hconv : Convex ℝ K)
    (hbox : ∀ p ∈ K, ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (hmin : ∀ j, ∃ p ∈ K, p j = 0) (hmax : ∀ j, ∃ p ∈ K, p j = 1)
    (lo hi : Fin 3 → ℝ) (hordered : ∀ j, lo j ≤ hi j)
    (hlo : ∀ j, 0 ≤ lo j) (hhi : ∀ j, hi j ≤ 1)
    (hcover : ∀ p ∈ K, ∃ j, lo j ≤ p j ∧ p j ≤ hi j)
    (hdef : (∑ j, (hi j - lo j)) < 1) :
    ∀ i j, i ≠ j → ∃ p ∈ K,
      (lo i ≤ p i ∧ p i ≤ hi i) ∧ (lo j ≤ p j ∧ p j ≤ hi j) := by
  intro i j hij
  obtain ⟨σ, hσ0, hσ2⟩ := pair_permutation i j hij
  by_contra hnone
  have hdis : Disjoint (K ∩ {p | lo i ≤ p i ∧ p i ≤ hi i})
      (K ∩ {p | lo j ≤ p j ∧ p j ≤ hi j}) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact hnone ⟨p, hp.1, hp.2, hq.2⟩
  have hbound := sum_ge_one_of_disjoint_perm K hconv hbox hmin hmax σ lo hi
    hordered (hlo (σ 1)) (hhi (σ 1)) hcover (by
      simpa only [hσ0, hσ2] using hdis)
  exact not_lt_of_ge hbound hdef

end Plank.Convex.DisconnectedPlankCover

/-- info: 'Plank.Convex.DisconnectedPlankCover.sum_ge_one_of_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.DisconnectedPlankCover.sum_ge_one_of_disjoint

/-- info: 'Plank.Convex.DisconnectedPlankCover.sum_ge_one_of_disjoint_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.DisconnectedPlankCover.sum_ge_one_of_disjoint_perm

/-- info: 'Plank.Convex.DisconnectedPlankCover.pairwise_intersect_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.DisconnectedPlankCover.pairwise_intersect_of_deficit

/-- info: 'Plank.Convex.DisconnectedPlankCover.sum_ge_one_of_pair_intersection_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.DisconnectedPlankCover.sum_ge_one_of_pair_intersection_subset

/-- info: 'Plank.Convex.DisconnectedPlankCover.sum_ge_one_of_pair_intersection_subset_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.DisconnectedPlankCover.sum_ge_one_of_pair_intersection_subset_perm

/-- info: 'Plank.Convex.DisconnectedPlankCover.exists_pair_outside_of_deficit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.DisconnectedPlankCover.exists_pair_outside_of_deficit
