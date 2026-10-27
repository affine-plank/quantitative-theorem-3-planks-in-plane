/- In a deficient three-window cover all widths and endpoint margins
are strict. This supplies the open domain for the class-A minimum argument. -/
module
public import Plank.Convex.ClosedCover
public import Plank.Convex.SameSignCapAlgebra
public import Plank.Convex.SameSignCapMinimum
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Plank.Convex.SameSignCapMinimumStrict
open SameSignCapAlgebra

theorem widths_positive_of_deficit (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ K, ∃ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hdef : (∑ i, (hi i - lo i)) < 1) : ∀ i, lo i < hi i := by
  intro k
  by_contra hn
  have he : hi k = lo k := le_antisymm (le_of_not_gt hn) (horder k)
  let C : Set Point := {x | lo (next k) ≤ x (next k) ∧ x (next k) ≤ hi (next k)} ∪
    {x | lo (prev k) ≤ x (prev k) ∧ x (prev k) ≤ hi (prev k)}
  have hclosed (i : Fin 3) : IsClosed {x : Point | lo i ≤ x i ∧ x i ≤ hi i} :=
    (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  obtain ⟨p, hp, hpk⟩ : ∃ p ∈ K, p k ≠ lo k := by
    by_cases hl : lo k = 0
    · obtain ⟨p, hp, hpk⟩ := hU k
      exact ⟨p, hp, by rw [hpk, hl]; norm_num⟩
    · obtain ⟨p, hp, hpk⟩ := hL k
      exact ⟨p, hp, by rw [hpk]; exact Ne.symm hl⟩
  have hcov : K ⊆ C := by
    apply ClosedCover.closed_cover_remove_affine K C hK ((hclosed _).union (hclosed _))
      (AffineMap.proj k) (lo k) p hp hpk
    intro x hx
    obtain ⟨i, hli, hhi⟩ := hcover x hx
    rcases index_cases k i with rfl | rfl | rfl
    · exact Or.inr (by change x i = lo i; rw [he] at hhi; exact le_antisymm hhi hli)
    · exact Or.inl (Or.inl ⟨hli, hhi⟩)
    · exact Or.inl (Or.inr ⟨hli, hhi⟩)
  have htwo := TwoAffineWindows.width_bound K hK
    (AffineMap.proj (next k)) (AffineMap.proj (prev k))
    (fun x hx => ⟨hbox x hx _, hbox x hx _⟩)
    (lo (next k)) (hi (next k)) (lo (prev k)) (hi (prev k)) (horder _) (horder _)
    (hL _) (hU _) (hL _) (hU _) hcov
  rw [sum_cycle (fun i => hi i - lo i) k] at hdef
  simp only [he, sub_self, zero_add] at hdef
  exact (not_le_of_gt hdef) htwo


theorem cover_of_pair_caps (lo hi x : Point)
    (hcap : ∀ i, (x i ≤ hi i ∨ x (next i) ≤ hi (next i)) ∧
      (lo i ≤ x i ∨ lo (next i) ≤ x (next i))) :
    ∃ i, lo i ≤ x i ∧ x i ≤ hi i := by
  by_contra! hout
  have hsign (i : Fin 3) : x i < lo i ∨ hi i < x i := by
    by_cases hl : lo i ≤ x i
    · exact Or.inr (hout i hl)
    · exact Or.inl (lt_of_not_ge hl)
  rcases hsign 0 with h0 | h0 <;> rcases hsign 1 with h1 | h1 <;> rcases hsign 2 with h2 | h2
  · rcases (hcap 0).2 with h | h <;> (try dsimp [next] at h) <;> linarith
  · rcases (hcap 0).2 with h | h <;> (try dsimp [next] at h) <;> linarith
  · rcases (hcap 2).2 with h | h <;> (try dsimp [next] at h) <;> linarith
  · rcases (hcap 1).1 with h | h <;> (try dsimp [next] at h) <;> linarith
  · rcases (hcap 1).2 with h | h <;> (try dsimp [next] at h) <;> linarith
  · rcases (hcap 2).1 with h | h <;> (try dsimp [next] at h) <;> linarith
  · rcases (hcap 0).1 with h | h <;> (try dsimp [next] at h) <;> linarith
  · rcases (hcap 0).1 with h | h <;> (try dsimp [next] at h) <;> linarith

theorem strictWalls_of_deficit (K : Set Point) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : SameSignCapMinimum.Walls)
    (hB : B ∈ SameSignCapMinimum.wallSet K)
    (hdef : SameSignCapMinimum.width B < 1) :
    B ∈ SameSignCapMinimum.strictWalls := by
  have horder : ∀ i, B.1 i ≤ B.2 i := fun i => Set.mem_iInter.mp hB.2.1 i
  have hn (i : Fin 3) : SameSignCapMinimum.next i = next i := by
    fin_cases i <;> rfl
  have hcover : ∀ x ∈ K, ∃ i, B.1 i ≤ x i ∧ x i ≤ B.2 i := by
    intro x hx
    apply cover_of_pair_caps
    intro i
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hB.2.2 x) hx) i
    change (x i ≤ B.2 i ∨ x (SameSignCapMinimum.next i) ≤
      B.2 (SameSignCapMinimum.next i)) ∧
      (B.1 i ≤ x i ∨ B.1 (SameSignCapMinimum.next i) ≤
        x (SameSignCapMinimum.next i)) at h
    simpa only [hn] using h
  rw [SameSignCapMinimum.width_apply] at hdef
  have hends := CommonPointUnclipped.windows_strict_of_deficit
    K hK hbox hL hU B.1 B.2 horder hcover hdef
  have hwidth := widths_positive_of_deficit K hK hbox hL hU B.1 B.2 horder hcover hdef
  apply Set.mem_iInter.mpr
  intro i
  exact ⟨⟨(hends i).1, hwidth i⟩, (hends i).2⟩

end Plank.Convex.SameSignCapMinimumStrict
