module
/-
# Finite escape assignments from an ordinal potential

An auxiliary symmetric interaction matrix need only preserve the ordering
of each row's finitely many subset sums. Its thresholds may then be chosen
to reproduce the original side decisions.
-/
public import Plank.Proofs.Quant.SymmetricTranslations

@[expose] public section

noncomputable section

namespace Quant.OrdinalTranslations

open Set MeasureTheory Function CommonVertex SymmetricTranslations

variable {ι α : Type*}

/-- A threshold can be transferred between two finite ordered lists, even
when the original list has ties. -/
theorem exists_threshold [Fintype α] [Nonempty α] (f g : α → ℝ)
    (hmono : ∀ x y, g x ≤ g y → f x ≤ f y) (c : ℝ) :
    ∃ d : ℝ, (∀ x, g x ≤ d → f x ≤ c) ∧ (∀ x, d ≤ g x → c ≤ f x) := by
  classical
  let L : Finset α := Finset.univ.filter fun x => f x ≤ c
  let R : Finset α := Finset.univ.filter fun x => c < f x
  by_cases hL : L.Nonempty
  · by_cases hR : R.Nonempty
    · obtain ⟨l, hl, hmax⟩ := Finset.exists_max_image L g hL
      obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image R g hR
      have hfl : f l ≤ c := (Finset.mem_filter.mp hl).2
      have hfr : c < f r := (Finset.mem_filter.mp hr).2
      have hgap : g l < g r := by
        by_contra h
        have hle := hmono r l (le_of_not_gt h)
        linarith
      refine ⟨(g l + g r) / 2, ?_, ?_⟩
      · intro x hx
        by_contra hf
        have hxr : x ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hf⟩
        have h := hmin x hxr
        linarith
      · intro x hx
        by_contra hf
        have hxl : x ∈ L :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_of_not_ge hf).le⟩
        have h := hmax x hxl
        linarith
    · obtain ⟨l, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset α) g
        Finset.univ_nonempty
      refine ⟨g l + 1, ?_, ?_⟩
      · intro x _
        by_contra hf
        exact hR ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hf⟩⟩
      · intro x hx
        have h := hmax x (Finset.mem_univ _)
        linarith
  · obtain ⟨r, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset α) g
      Finset.univ_nonempty
    refine ⟨g r - 1, ?_, ?_⟩
    · intro x hx
      have h := hmin x (Finset.mem_univ _)
      linarith
    · intro x _
      by_contra hf
      exact hL ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lt_of_not_ge hf).le⟩⟩

def interaction (p : ι → Plank) (v : ι → ℝ × ℝ) (i j : ι) : ℝ := by
  classical
  exact if i = j then 0 else dot (p i).u (v j)

/-- A symmetric matrix preserving each row's subset-sum order is sufficient
for the actual plank inequalities. It need not equal a rescaling of the
original interactions. -/
theorem exists_side_assignment [Fintype ι] (p : ι → Plank) (v : ι → ℝ × ℝ)
    (b : ι → ι → ℝ) (hsym : ∀ i j, b i j = b j i) (hdiag : ∀ i, b i i = 0)
    (hself : ∀ i, dot (p i).u (v i) = (p i).hi - (p i).lo)
    (horder : ∀ (i : ι) (s t : Finset ι), s.sum (b i) ≤ t.sum (b i) →
      s.sum (interaction p v i) ≤ t.sum (interaction p v i)) (t : ℝ × ℝ) :
    ∃ s : Finset ι,
      (∀ i ∈ s, (p i).hi ≤ dot (p i).u (t + shift v s)) ∧
      (∀ i ∉ s, dot (p i).u (t + shift v s) ≤ (p i).lo) := by
  classical
  have hthreshold : ∀ i, ∃ d : ℝ,
      (∀ s : Finset ι, s.sum (b i) ≤ d →
        s.sum (interaction p v i) ≤ (p i).lo - dot (p i).u t) ∧
      (∀ s : Finset ι, d ≤ s.sum (b i) →
        (p i).lo - dot (p i).u t ≤ s.sum (interaction p v i)) := by
    intro i
    exact exists_threshold (fun s : Finset ι => s.sum (interaction p v i))
      (fun s : Finset ι => s.sum (b i)) (horder i) ((p i).lo - dot (p i).u t)
  choose d hd using hthreshold
  let a : ι → ℝ := fun i => -d i
  obtain ⟨s, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset ι)) (score a b) Finset.univ_nonempty
  have hrow : ∀ (s : Finset ι) (i : ι), i ∉ s →
      s.sum (interaction p v i) = dot (p i).u (shift v s) := by
    intro s i hi
    rw [dot_shift]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    simp only [interaction, hij, ↓reduceIte]
  refine ⟨s, ?_, ?_⟩
  · intro i hi
    have hm := hmax (s.erase i) (Finset.mem_univ _)
    have he : insert i (s.erase i) = s := Finset.insert_erase hi
    have hdif := score_insert a b hsym hdiag (s.erase i) i (Finset.notMem_erase i s)
    rw [he] at hdif
    have hfake : d i ≤ (s.erase i).sum (b i) := by dsimp [a] at hdif; linarith
    have hreal := (hd i).2 (s.erase i) hfake
    rw [hrow _ _ (Finset.notMem_erase i s)] at hreal
    have hshift : shift v s = v i + shift v (s.erase i) := by
      conv_lhs => rw [← he]
      exact Finset.sum_insert (Finset.notMem_erase i s)
    have hx : dot (p i).u (t + shift v s) =
        dot (p i).u t + dot (p i).u (shift v (s.erase i)) + dot (p i).u (v i) := by
      rw [hshift]
      simp only [dot, Prod.fst_add, Prod.snd_add]
      ring
    rw [hx, hself]
    linarith
  · intro i hi
    have hm := hmax (insert i s) (Finset.mem_univ _)
    rw [score_insert a b hsym hdiag s i hi] at hm
    have hfake : s.sum (b i) ≤ d i := by dsimp [a] at hm; linarith
    have hreal := (hd i).1 s hfake
    rw [hrow _ _ hi] at hreal
    have hx : dot (p i).u (t + shift v s) =
        dot (p i).u t + dot (p i).u (shift v s) := by
      simp only [dot, Prod.fst_add, Prod.snd_add]
      ring
    rw [hx]
    linarith

/-- Ordered positive two-bit sums have the same weak order when the smaller
and larger weights are replaced by any strictly ordered positive weights. -/
theorem two_bit_monotone {a b A B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hA : 0 < A) (hAB : A < B) (s₀ s₁ t₀ t₁ : Bool)
    (h : (if s₀ then A else 0) + (if s₁ then B else 0) ≤
      (if t₀ then A else 0) + (if t₁ then B else 0)) :
    (if s₀ then a else 0) + (if s₁ then b else 0) ≤
      (if t₀ then a else 0) + (if t₁ then b else 0) := by
  cases s₀ <;> cases s₁ <;> cases t₀ <;> cases t₁ <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> linarith

end Quant.OrdinalTranslations
