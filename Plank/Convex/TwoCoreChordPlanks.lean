/- A triangular family of width-realizing chords with an arbitrary two-coordinate core.
Eliminate the last chord by two endpoint homothets, then apply the general
two-plank theorem to the final pair. No signs, common centers, or inner product
are required. -/
module

public import Plank.Proofs.TwoPlankBody

@[expose] public section
noncomputable section

namespace Plank.Convex

open Plank.Body

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A full-width chord constant in the first `n` coordinates transfers any sharp
covering bound in those coordinates to the family with one additional plank.
The core hypothesis is equivalently a bound on the remaining affine projection. -/
theorem sum_ge_one_of_last_parallel_chord {n : ℕ}
    (K : Set E) (hK : Convex ℝ K) (f : Fin (n+1) → E →ᵃ[ℝ] ℝ)
    (U V : E) (hU : U ∈ K) (hV : V ∈ K)
    (hU0 : f (Fin.last n) U = 0) (hV1 : f (Fin.last n) V = 1)
    (hparallel : ∀ j : Fin n, f j.castSucc U = f j.castSucc V)
    (hcore : ∀ lo hi : Fin n → ℝ, (∀ j, lo j ≤ hi j) →
      (∀ x ∈ K, ∃ j, lo j ≤ f j.castSucc x ∧ f j.castSucc x ≤ hi j) →
      1 ≤ ∑ j, (hi j-lo j))
    (lo hi : Fin (n+1) → ℝ) (hle : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) :
    1 ≤ ∑ j, (hi j-lo j) := by
  by_contra hn
  have hS : (∑ j, (hi j-lo j)) < 1 := lt_of_not_ge hn
  let R := ∑ j : Fin n, (hi j.castSucc-lo j.castSucc)
  let w := hi (Fin.last n)-lo (Fin.last n)
  have hsum : R+w < 1 := by simpa only [R,w,Fin.sum_univ_castSucc] using hS
  have hR : 0 ≤ R := Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hle j.castSucc)
  have hw : 0 ≤ w := sub_nonneg.mpr (hle (Fin.last n))
  let t := (w+1-R)/2
  have ht0 : 0 < t := by dsimp [t]; linarith
  have hwt : w < t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hd : 0 < 1-t := by linarith
  have hsmall : R < 1-t := by dsimp [t]; linarith
  let low (j : Fin n) := (lo j.castSucc-t*f j.castSucc U)/(1-t)
  let high (j : Fin n) := (hi j.castSucc-t*f j.castSucc U)/(1-t)
  have hmap (x v : E) (j : Fin (n+1)) :
      f j (x+t • (v-x)) = (1-t)*f j x+t*f j v := by
    rw [map_add_smul_sub]
    ring
  have hpull : ∀ x ∈ K, ∃ j : Fin n,
      low j ≤ f j.castSucc x ∧ f j.castSucc x ≤ high j := by
    intro x hx
    obtain ⟨v,hv,heq,havoid⟩ : ∃ v ∈ K,
        (∀ j : Fin n, f j.castSucc v = f j.castSucc U) ∧
        (f (Fin.last n) (x+t • (v-x)) < lo (Fin.last n) ∨
          hi (Fin.last n) < f (Fin.last n) (x+t • (v-x))) := by
      by_cases hz : lo (Fin.last n) ≤ (1-t)*f (Fin.last n) x
      · refine ⟨V,hV,fun j => (hparallel j).symm,Or.inr ?_⟩
        rw [hmap,hV1]
        dsimp [w] at hwt
        linarith
      · refine ⟨U,hU,fun _ => rfl,Or.inl ?_⟩
        rw [hmap,hU0]
        linarith
    have hxv : x+t • (v-x) ∈ K := hK.add_smul_sub_mem hx hv ⟨ht0.le,ht1.le⟩
    obtain ⟨r,hr0,hr1⟩ := hcover _ hxv
    have hr : r ≠ Fin.last n := by
      rintro rfl
      rcases havoid with hlt | hlt <;> linarith
    obtain ⟨j,rfl⟩ := Fin.exists_castSucc_eq.mpr hr
    refine ⟨j,?_,?_⟩
    all_goals rw [hmap,heq j] at hr0 hr1
    · exact (div_le_iff₀ hd).mpr (by nlinarith)
    · exact (le_div_iff₀ hd).mpr (by nlinarith)
  have hb := hcore low high (fun j =>
    div_le_div_of_nonneg_right (by linarith [hle j.castSucc]) hd.le) hpull
  have hterm (j : Fin n) : high j-low j = (hi j.castSucc-lo j.castSucc)/(1-t) := by
    dsimp [high,low]
    ring
  simp_rw [hterm] at hb
  rw [← Finset.sum_div] at hb
  have hbound : 1-t ≤ R := by simpa [R] using (le_div_iff₀ hd).mp hb
  linarith

/-- An arbitrary two-coordinate core can precede triangular unit chords.
Chords with index at least two leave every earlier coordinate unchanged.
The two core chords and all forward increments have unrestricted signs. -/
theorem sum_ge_one_of_two_core_chord_cover {m : ℕ}
    (K : Set E) (hK : Convex ℝ K) (f : Fin (m+2) → E →ᵃ[ℝ] ℝ)
    (hbounds : ∀ x ∈ K, ∀ j, 0 ≤ f j x ∧ f j x ≤ 1)
    (pm pp : Fin (m+2) → E) (hm : ∀ j, pm j ∈ K) (hp : ∀ j, pp j ∈ K)
    (hpm : ∀ j, f j (pm j) = 0) (hpp : ∀ j, f j (pp j) = 1)
    (htri : ∀ i, 2 ≤ i.val → ∀ j, j < i → f j (pm i) = f j (pp i))
    (lo hi : Fin (m+2) → ℝ) (hle : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) :
    1 ≤ ∑ j, (hi j-lo j) := by
  induction m with
  | zero =>
    let C : Plank.TwoPlankBody.Coords E :=
      { T := K
        X := f 0
        Y := f 1
        seg := by
          intro x hx y hy t ht0 ht1
          refine ⟨x+t • (y-x),hK.add_smul_sub_mem hx hy ⟨ht0,ht1⟩,?_,?_⟩
          all_goals exact map_add_smul_sub _ _ _ _
        range := fun x hx => ⟨hbounds x hx 0,hbounds x hx 1⟩
        l1 := lo 0
        h1 := hi 0
        l2 := lo 1
        h2 := hi 1
        le1 := hle 0
        le2 := hle 1
        cov := by
          intro x hx
          obtain ⟨j,hj⟩ := hcover x hx
          fin_cases j
          · exact Or.inl hj
          · exact Or.inr hj
        pL := ⟨pm 0,hm 0,hpm 0⟩
        pR := ⟨pp 0,hp 0,hpp 0⟩
        qD := ⟨pm 1,hm 1,hpm 1⟩
        qU := ⟨pp 1,hp 1,hpp 1⟩ }
    change 1 ≤ ∑ j : Fin 2, (hi j-lo j)
    rw [Fin.sum_univ_two]
    exact Plank.TwoPlankBody.twoplank_normalised C
  | succ m ih =>
    apply sum_ge_one_of_last_parallel_chord K hK f
      (pm (Fin.last (m+2))) (pp (Fin.last (m+2)))
      (hm _) (hp _) (hpm _) (hpp _) ?_ ?_ lo hi hle hcover
    · intro j
      exact htri _ (by simp) j.castSucc (Fin.castSucc_lt_last j)
    · intro low high hlow hpull
      apply ih (fun j => f j.castSucc) (fun x hx j => hbounds x hx j.castSucc)
        (fun j => pm j.castSucc) (fun j => pp j.castSucc)
        (fun j => hm j.castSucc) (fun j => hp j.castSucc)
        (fun j => hpm j.castSucc) (fun j => hpp j.castSucc) ?_ low high hlow hpull
      intro i hi j hji
      exact htri i.castSucc hi j.castSucc hji

/-- In particular, all but two width-realizing chords may be axis-parallel in
the normalized coordinates; the remaining two chords are completely arbitrary. -/
theorem sum_ge_one_of_parallel_chords_except_two {m : ℕ}
    (K : Set E) (hK : Convex ℝ K) (f : Fin (m+2) → E →ᵃ[ℝ] ℝ)
    (hbounds : ∀ x ∈ K, ∀ j, 0 ≤ f j x ∧ f j x ≤ 1)
    (pm pp : Fin (m+2) → E) (hm : ∀ j, pm j ∈ K) (hp : ∀ j, pp j ∈ K)
    (hpm : ∀ j, f j (pm j) = 0) (hpp : ∀ j, f j (pp j) = 1)
    (hparallel : ∀ i, 2 ≤ i.val → ∀ j, j ≠ i → f j (pm i) = f j (pp i))
    (lo hi : Fin (m+2) → ℝ) (hle : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ f j x ∧ f j x ≤ hi j) :
    1 ≤ ∑ j, (hi j-lo j) :=
  sum_ge_one_of_two_core_chord_cover K hK f hbounds pm pp hm hp hpm hpp
    (fun i hi j hji => hparallel i hi j (ne_of_lt hji)) lo hi hle hcover

end Plank.Convex

/-- info: 'Plank.Convex.sum_ge_one_of_last_parallel_chord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.sum_ge_one_of_last_parallel_chord
/-- info: 'Plank.Convex.sum_ge_one_of_two_core_chord_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.sum_ge_one_of_two_core_chord_cover
/-- info: 'Plank.Convex.sum_ge_one_of_parallel_chords_except_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.sum_ge_one_of_parallel_chords_except_two

end
