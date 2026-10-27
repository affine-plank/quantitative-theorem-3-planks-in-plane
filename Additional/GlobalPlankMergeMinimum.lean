/- A finite secondary minimization removes every mergeable active pair.
The index type and all-body minimum are preserved; no induction is used. -/
module

public import FinitePlankMerge
public import AffineLevelCoincidence
public import FinitePlankNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.GlobalPlankMergeMinimum

open Set MeasureTheory PrunedPlankCounterexample GlobalPlankBodyMinimum
open FinitePlankMerge (active)

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

/-- Among endpoint competitors with no greater margin, this family has the
fewest positive-width windows. Body and forms remain fixed. -/
def LeastActive (μ : Measure E) (K : Set E) (f : ι → E →ᵃ[ℝ] ℝ)
    (lo hi : ι → ℝ) (d : ℕ) (B : ℝ) : Prop :=
  ∀ a b : ι → ℝ, (∀ i,a i≤b i) → budget K f a b≤B →
    margin μ K f a b d B≤margin μ K f lo hi d B →
    (active lo hi).card≤(active a b).card

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Secondary minimization is over natural numbers, so no new compactness
argument is needed. It preserves the actual global margin and minimum. -/
theorem exists_least_active (μ : Measure E) {K : Set E}
    (hK : IsCompact K) (hc : Convex ℝ K) (hV : 0<μ.real K)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hW : ∀ i,0<Body.width K (f i)) (ho : ∀ i,lo i≤hi i)
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hglobal : IsGlobalMinimum μ K f lo hi d B) :
    ∃ a b : ι → ℝ, (∀ i,a i≤b i) ∧ budget K f a b≤B ∧
      margin μ K f a b d B=margin μ K f lo hi d B ∧
      IsGlobalMinimum μ K f a b d B ∧ LeastActive μ K f a b d B := by
  classical
  let P (k : ℕ) := ∃ a b : ι → ℝ, (∀ i,a i≤b i) ∧ budget K f a b≤B ∧
    margin μ K f a b d B≤margin μ K f lo hi d B ∧ (active a b).card=k
  have hex : ∃ k,P k := ⟨(active lo hi).card,lo,hi,ho,hbudget,le_rfl,rfl⟩
  obtain ⟨a,b,hab,hbud,hle,hcard⟩ := Nat.find_spec hex
  have heq := le_antisymm hle (hglobal K f a b hK hc hV hW hab hbud)
  refine ⟨a,b,hab,hbud,heq,?_,?_⟩
  · intro C g c e hC hCc hCV hCW hce hcb
    rw [heq]
    exact hglobal C g c e hC hCc hCV hCW hce hcb
  · intro c e hce hcb hm
    rw [hcard]
    exact Nat.find_min' hex ⟨c,e,hce,hcb,hm.trans hle,rfl⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Exact coverage and a smaller budget cannot increase the margin. -/
theorem margin_le_of_merge (μ : Measure E) (K : Set E)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi a b : ι → ℝ) (d : ℕ) {B : ℝ}
    (hbudget : budget K f lo hi≤B) (hle : budget K f a b≤budget K f lo hi)
    (hcover : covered f a b=covered f lo hi) :
    margin μ K f a b d B≤margin μ K f lo hi d B := by
  unfold margin
  rw [hcover]
  exact sub_le_sub_left
    (pow_le_pow_left₀ (sub_nonneg.mpr hbudget) (sub_le_sub_left hle B) d) _

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A least-active minimum has no overlapping or touching parallel positive
windows. The band identity and relative-width identity make parallelism
explicit and accommodate arbitrary scaling and orientation of the forms. -/
theorem no_mergeable_pair (μ : Measure E) (K : Set E)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ) (ho : ∀ k,lo k≤hi k)
    (d : ℕ) {B : ℝ} (hbudget : budget K f lo hi≤B)
    (hminimal : LeastActive μ K f lo hi d B)
    (i j : ι) (hij : i≠j) (hipos : lo i<hi i) (hjpos : lo j<hi j)
    (hWi : 0<Body.width K (f i)) (c e : ℝ)
    (hce : c≤e) (hcb : c≤hi i) (hae : lo i≤e)
    (hband : {x | lo j≤f j x ∧ f j x≤hi j}={x | c≤f i x ∧ f i x≤e})
    (hcost : (e-c)/Body.width K (f i)=(hi j-lo j)/Body.width K (f j)) : False := by
  classical
  obtain ⟨a,b,hab,hle,hcover,hactive⟩ := FinitePlankMerge.exists_merged K f lo hi ho
    i j hij hipos hWi c e hce hcb hae hband hcost
  have hh := hminimal a b hab (hle.trans hbudget)
    (margin_le_of_merge μ K f lo hi a b d hbudget hle hcover)
  rw [hactive] at hh
  exact (not_lt_of_ge hh) (Finset.card_lt_card (Finset.erase_ssubset
    (by simpa [active] using hjpos)))

omit [BorelSpace E] in
/-- Support normalization preserves the entire covered set and exact margin;
it does not clip endpoints or invoke a bound for fewer planks. -/
theorem exists_unit_minimum (μ : Measure E) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty)
    (f : ι → E →ᵃ[ℝ] ℝ) (lo hi : ι → ℝ)
    (hW : ∀ i,0<Body.width K (f i)) (ho : ∀ i,lo i≤hi i)
    (d : ℕ) (B : ℝ) (hglobal : IsGlobalMinimum μ K f lo hi d B) :
    ∃ (g : ι → E →ᵃ[ℝ] ℝ) (a b : ι → ℝ),
      (∀ i,Body.width K (g i)=1) ∧ (∀ i x,x∈K → 0≤g i x ∧ g i x≤1) ∧
      (∀ i,a i≤b i) ∧ budget K g a b=budget K f lo hi ∧
      margin μ K g a b d B=margin μ K f lo hi d B ∧
      IsGlobalMinimum μ K g a b d B := by
  choose g c happly hnorm hunit _ using fun i =>
    FinitePlankNormalization.exists_unit_form hK hne (f i) (hW i)
  let a := fun i => (lo i-c i)/Body.width K (f i)
  let b := fun i => (hi i-c i)/Body.width K (f i)
  have hcost : budget K g a b=budget K f lo hi := by
    unfold budget
    apply Finset.sum_congr rfl
    intro i _
    rw [hunit i,div_one]
    dsimp only [a,b]
    ring
  have hset : covered g a b=covered f lo hi := by
    ext x
    simp only [covered,mem_iUnion,mem_ofPred_eq]
    apply exists_congr
    intro i
    rw [happly]
    dsimp only [a,b]
    simp only [div_le_div_iff_of_pos_right (hW i),sub_le_sub_iff_right]
  have hm : margin μ K g a b d B=margin μ K f lo hi d B := by
    unfold margin; rw [hset,hcost]
  refine ⟨g,a,b,hunit,hnorm,?_,hcost,hm,?_⟩
  · intro i
    exact (div_le_div_iff_of_pos_right (hW i)).mpr (sub_le_sub_right (ho i) _)
  · intro C h aa bb hC hCc hCV hCW hab hbudget
    rw [hm]
    exact hglobal C h aa bb hC hCc hCV hCW hab hbudget

omit [BorelSpace E] in
/-- Distinct active windows at a least-active minimum cannot share a
boundary hyperplane. Positive widths, unit support normalization and least
active count replace every smaller-plank theorem used in the older proof. -/
theorem not_level_subset (μ : Measure E) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (f : ι → E →ᵃ[ℝ] ℝ)
    (hunit : ∀ k,Body.width K (f k)=1)
    (hnorm : ∀ k x,x∈K → 0≤f k x ∧ f k x≤1)
    (lo hi : ι → ℝ) (ho : ∀ k,lo k≤hi k) (d : ℕ) {B : ℝ}
    (hbudget : budget K f lo hi≤B) (hminimal : LeastActive μ K f lo hi d B)
    (i j : ι) (hij : i≠j) (hipos : lo i<hi i) (hjpos : lo j<hi j)
    (a b : ℝ) (ha : a=lo i ∨ a=hi i) (hb : b=lo j ∨ b=hi j) :
    ¬∀ x,f i x=a → f j x=b := by
  intro hlevel
  have hWi : 0<Body.width K (f i) := by rw [hunit]; norm_num
  have hf := AffineLevelCoincidence.linear_ne_zero_of_width_pos hK hne (f i) hWi
  have hsurj : Function.Surjective (f i) := (f i).linear_surjective_iff.mp
    (surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (by simp) hf)
  obtain ⟨x,hx⟩ := hsurj a
  have hy := hlevel x hx
  have hai : lo i≤a ∧ a≤hi i := by
    rcases ha with rfl|rfl <;> exact ⟨by linarith only [ho i],by linarith only [ho i]⟩
  have hbj : lo j≤b ∧ b≤hi j := by
    rcases hb with rfl|rfl <;> exact ⟨by linarith only [ho j],by linarith only [ho j]⟩
  rcases AffineLevelCoincidence.normalized_of_level hK hne (f i) (f j)
    (hunit i) (hunit j) (hnorm i) (hnorm j) a b hlevel with hsame|hreverse
  · have hab : a=b := by rw [hsame,hx] at hy; exact hy
    apply no_mergeable_pair μ K f lo hi ho d hbudget hminimal i j hij hipos hjpos
      hWi (lo j) (hi j) (ho j)
      (by linarith only [hai.2,hbj.1,hab]) (by linarith only [hai.1,hbj.2,hab])
    · ext y; simp only [hsame]
    · simp only [hunit]
  · have hab : 1-a=b := by rw [hreverse,hx] at hy; exact hy
    apply no_mergeable_pair μ K f lo hi ho d hbudget hminimal i j hij hipos hjpos
      hWi (1-hi j) (1-lo j) (by linarith only [ho j])
      (by linarith only [hai.2,hbj.2,hab]) (by linarith only [hai.1,hbj.1,hab])
    · ext y
      change (lo j≤f j y ∧ f j y≤hi j) ↔ (1-hi j≤f i y ∧ f i y≤1-lo j)
      rw [hreverse]
      constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith only [h1,h2]
    · rw [hunit,hunit]; ring

end Plank.GlobalPlankMergeMinimum
