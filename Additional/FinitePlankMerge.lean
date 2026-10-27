/- Exact merging for arbitrary finite physical plank families.
The collapsed window stays inside the old union, so coverage is unchanged. -/
module

public import GlobalPlankBodyMinimum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FinitePlankMerge

open Set PrunedPlankCounterexample

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- Positive-width windows; collapsed windows are retained in the index type. -/
def active (lo hi : ι → ℝ) : Finset ι := Finset.univ.filter fun i => lo i<hi i

theorem interval_union {a b c d : ℝ} (hcb : c≤b) (had : a≤d) :
    {x : ℝ | a≤x ∧ x≤b} ∪ {x | c≤x ∧ x≤d}={x | min a c≤x ∧ x≤max b d} := by
  ext x
  simp only [mem_union,mem_ofPred_eq,min_le_iff,le_max_iff]
  constructor
  · rintro (⟨h1,h2⟩|⟨h1,h2⟩)
    · exact ⟨Or.inl h1,Or.inl h2⟩
    · exact ⟨Or.inr h1,Or.inr h2⟩
  · rintro ⟨h1,h2⟩
    rcases h1 with h1|h1 <;> rcases h2 with h2|h2
    · exact Or.inl ⟨h1,h2⟩
    · by_cases hxb : x≤b
      · exact Or.inl ⟨h1,hxb⟩
      · exact Or.inr ⟨hcb.trans (le_of_not_ge hxb),h2⟩
    · by_cases hxd : x≤d
      · exact Or.inr ⟨h1,hxd⟩
      · exact Or.inl ⟨had.trans (le_of_not_ge hxd),h2⟩
    · exact Or.inr ⟨h1,h2⟩

theorem interval_width_le {a b c d : ℝ} (hab : a≤b) (hcd : c≤d)
    (hcb : c≤b) (had : a≤d) : max b d-min a c≤(b-a)+(d-c) := by
  rcases le_total a c with hac|hca <;> rcases le_total b d with hbd|hdb
  · rw [min_eq_left hac,max_eq_right hbd]; linarith only [hcb]
  · rw [min_eq_left hac,max_eq_left hdb]; linarith only [hcd]
  · rw [min_eq_right hca,max_eq_right hbd]; linarith only [hab]
  · rw [min_eq_right hca,max_eq_left hdb]; linarith only [had]

/-- Merge two active overlapping or touching bands. The second band is
expressed in the first form's coordinates, with the actual relative width.
The body, forms, index type and exact covered set are preserved. -/
theorem exists_merged [DecidableEq ι] (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (horder : ∀ k,lo k≤hi k) (i j : ι) (hij : i≠j)
    (hiPos : lo i<hi i) (hWi : 0<Body.width K (f i)) (c d : ℝ)
    (hcd : c≤d) (hcb : c≤hi i) (had : lo i≤d)
    (hband : {x | lo j≤f j x ∧ f j x≤hi j}={x | c≤f i x ∧ f i x≤d})
    (hcost : (d-c)/Body.width K (f i)=(hi j-lo j)/Body.width K (f j)) :
    ∃ a b : ι → ℝ, (∀ k,a k≤b k) ∧ budget K f a b≤budget K f lo hi ∧
      covered f a b=covered f lo hi ∧ active a b=(active lo hi).erase j := by
  classical
  let L := min (lo i) c
  let H := max (hi i) d
  let a := Function.update lo i L
  let b := Function.update (Function.update hi i H) j (lo j)
  have hei : a i=L ∧ b i=H := by simp [a,b,hij]
  have hej : a j=lo j ∧ b j=lo j := by simp [a,b,hij.symm]
  have heother (k : ι) (hki : k≠i) (hkj : k≠j) : a k=lo k ∧ b k=hi k := by
    simp [a,b,hki,hkj]
  have hLH : L<H := (min_le_left _ _).trans_lt (hiPos.trans_le (le_max_left _ _))
  have hmerge : {x | L≤f i x ∧ f i x≤H}=
      {x | lo i≤f i x ∧ f i x≤hi i} ∪ {x | lo j≤f j x ∧ f j x≤hi j} := by
    rw [hband]
    exact (congrArg (fun S : Set ℝ => f i ⁻¹' S) (interval_union hcb had)).symm
  refine ⟨a,b,?_,?_,?_,?_⟩
  · intro k
    by_cases hki : k=i
    · subst k; rw [hei.1,hei.2]; exact hLH.le
    · by_cases hkj : k=j
      · subst k; rw [hej.1,hej.2]
      · rw [(heother k hki hkj).1,(heother k hki hkj).2]; exact horder k
  · let r : ι → ℝ := fun k => (hi k-lo k)/Body.width K (f k)
    have he : (fun k => (b k-a k)/Body.width K (f k))=
        Function.update (Function.update r i ((H-L)/Body.width K (f i))) j 0 := by
      funext k
      by_cases hki : k=i
      · subst k; simp [hei,Function.update_of_ne hij]
      · by_cases hkj : k=j
        · subst k; simp [hej]
        · simp [(heother k hki hkj).1,(heother k hki hkj).2,hki,hkj,r]
    have hsum (v : ι → ℝ) (k : ι) (t : ℝ) :
        ∑ x,Function.update v k t x=(∑ x,v x)-v k+t := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ k),Finset.sdiff_singleton_eq_erase]
      have hh := Finset.sum_erase_add Finset.univ v (Finset.mem_univ k)
      linarith only [hh]
    unfold budget
    rw [he,hsum,hsum,Function.update_of_ne hij.symm]
    have hw := div_le_div_of_nonneg_right
      (interval_width_le (horder i) hcd hcb had) hWi.le
    rw [add_div,hcost] at hw
    change (H-L)/Body.width K (f i)≤r i+r j at hw
    change (∑ k,r k)-r i+(H-L)/Body.width K (f i)-r j+0≤∑ k,r k
    linarith only [hw]
  · ext x
    simp only [covered,mem_iUnion]
    constructor
    · rintro ⟨k,hk⟩
      by_cases hki : k=i
      · subst k
        rw [hei.1,hei.2] at hk
        rcases (show x∈_∪_ from hmerge ▸ hk) with h|h
        · exact ⟨i,h⟩
        · exact ⟨j,h⟩
      · by_cases hkj : k=j
        · subst k
          rw [hej.1,hej.2] at hk
          exact ⟨j,hk.1,hk.2.trans (horder j)⟩
        · rw [(heother k hki hkj).1,(heother k hki hkj).2] at hk
          exact ⟨k,hk⟩
    · rintro ⟨k,hk⟩
      by_cases hki : k=i
      · subst k
        refine ⟨i,?_⟩
        rw [hei.1,hei.2]
        exact hmerge.symm ▸ Or.inl hk
      · by_cases hkj : k=j
        · subst k
          refine ⟨i,?_⟩
          rw [hei.1,hei.2]
          exact hmerge.symm ▸ Or.inr hk
        · refine ⟨k,?_⟩
          rw [(heother k hki hkj).1,(heother k hki hkj).2]
          exact hk
  · ext k
    by_cases hki : k=i
    · subst k; simp [active,hei,hiPos,hLH,hij]
    · by_cases hkj : k=j
      · subst k; simp [active,hej]
      · simp [active,(heother k hki hkj).1,(heother k hki hkj).2,hkj]

end Plank.FinitePlankMerge
