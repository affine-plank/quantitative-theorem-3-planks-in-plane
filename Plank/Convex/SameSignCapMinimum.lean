/- Six pair contacts at an extreme class-A covering box.
The feasible domain is closed: other empty caps are allowed.
No relation among the three coordinates is assumed. -/
module
public import Plank.Convex.ExtremeMinimum
public import Plank.Convex.ExtremeMinimumRank
public import Plank.Convex.CompactPairSeparation
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
namespace Plank.Convex.SameSignCapMinimum

open scoped BigOperators

abbrev Point := Fin 3 → ℝ
abbrev Walls := Point × Point
def next (i : Fin 3) : Fin 3 := i + 1

def capSet (K : Set Point) : Set Walls :=
  ⋂ x ∈ K, ⋂ i : Fin 3,
    ({B | x i ≤ B.2 i} ∪ {B | x (next i) ≤ B.2 (next i)}) ∩
    ({B | B.1 i ≤ x i} ∪ {B | B.1 (next i) ≤ x (next i)})

/-- Ordered normalized windows with all six open same-sign pair caps empty. -/
def wallSet (K : Set Point) : Set Walls :=
  Icc 0 1 ∩ ((⋂ i : Fin 3, {B | B.1 i ≤ B.2 i}) ∩ capSet K)

theorem compact_wallSet (K : Set Point) : IsCompact (wallSet K) := by
  apply isCompact_Icc.inter_right
  refine (isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)).inter ?_
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iInter fun i =>
    ((isClosed_le continuous_const (by fun_prop)).union
      (isClosed_le continuous_const (by fun_prop))).inter
    ((isClosed_le (by fun_prop) continuous_const).union
      (isClosed_le (by fun_prop) continuous_const))

def width : Walls →L[ℝ] ℝ :=
  ∑ i : Fin 3, ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ Point Point) -
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ Point Point))

theorem width_apply (B : Walls) : width B = ∑ i, (B.2 i - B.1 i) := by
  simp [width]

theorem exists_extreme_minimizer (K : Set Point) (B : Walls) (hB : B ∈ wallSet K) :
    ∃ C ∈ (wallSet K).extremePoints ℝ, IsMinOn width (wallSet K) C ∧ width C ≤ width B := by
  obtain ⟨C, hC, hmin⟩ := ExtremeMinimum.exists_extreme_minimizer
    (wallSet K) (compact_wallSet K) ⟨B, hB⟩ width
  exact ⟨C, hC, hmin, hmin hB⟩

def strictWalls : Set Walls :=
  ⋂ i : Fin 3, {B | 0 < B.1 i} ∩ {B | B.1 i < B.2 i} ∩ {B | B.2 i < 1}

theorem open_strictWalls : IsOpen strictWalls := by
  exact isOpen_iInter_of_finite fun i =>
    ((isOpen_lt continuous_const (by fun_prop)).inter
      (isOpen_lt (by fun_prop) (by fun_prop))).inter
    (isOpen_lt (by fun_prop) continuous_const)

def row (a b : Point) (j : Bool × Fin 3) : Walls →L[ℝ] ℝ :=
  if j.1 then
    (ContinuousLinearMap.proj j.2).comp (ContinuousLinearMap.snd ℝ Point Point) +
      a j.2 • (ContinuousLinearMap.proj (next j.2)).comp (ContinuousLinearMap.snd ℝ Point Point)
  else
    -((ContinuousLinearMap.proj j.2).comp (ContinuousLinearMap.fst ℝ Point Point) +
      b j.2 • (ContinuousLinearMap.proj (next j.2)).comp (ContinuousLinearMap.fst ℝ Point Point))

@[simp] theorem row_upper (a b : Point) (i : Fin 3) (B : Walls) :
    row a b (true, i) B = B.2 i + a i * B.2 (next i) := rfl

@[simp] theorem row_lower (a b : Point) (i : Fin 3) (B : Walls) :
    row a b (false, i) B = -(B.1 i + b i * B.1 (next i)) := rfl

def direction (a : Point) (i : Fin 3) : Point :=
  fun j => if j = i then 1 else if j = next i then a (next i) * a (next (next i))
    else -a (next (next i))

@[simp] theorem direction_self (a : Point) (i : Fin 3) : direction a i i = 1 := by
  simp [direction]

theorem direction_other (a : Point) (i j : Fin 3) (hne : j ≠ i) :
    direction a i j + a j * direction a i (next j) = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [direction, next]

def motion (a b : Point) (j : Bool × Fin 3) : Walls :=
  if j.1 then (0, direction a j.2) else (direction b j.2, 0)

theorem motion_ne_zero (a b : Point) (j : Bool × Fin 3) : motion a b j ≠ 0 := by
  rcases j with ⟨s, i⟩
  cases s
  · intro he
    have := congrArg (fun B : Walls => B.1 i) he
    simp [motion] at this
  · intro he
    have := congrArg (fun B : Walls => B.2 i) he
    simp [motion] at this

theorem row_motion_other (a b : Point) (j k : Bool × Fin 3) (hne : k ≠ j) :
    row a b k (motion a b j) = 0 := by
  rcases j with ⟨s, i⟩
  rcases k with ⟨t, k⟩
  cases s <;> cases t
  · have hki : k ≠ i := by intro he; exact hne (by simp [he])
    simp only [motion, Bool.false_eq_true, ↓reduceIte, row_lower]
    rw [direction_other b i k hki, neg_zero]
  · simp [motion]
  · simp [motion]
  · have hki : k ≠ i := by intro he; exact hne (by simp [he])
    simpa only [motion, ↓reduceIte, row_upper] using direction_other a i k hki

theorem row_constraints_suffice (K : Set Point) (a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (c : Bool × Fin 3 → ℝ)
    (hs : ∀ x ∈ K, ∀ j, row a b j (x, x) ≤ c j)
    (B : Walls) (hB : B ∈ strictWalls) (hc : ∀ j, c j ≤ row a b j B) :
    B ∈ wallSet K := by
  have ht (i : Fin 3) : 0 < B.1 i ∧ B.1 i < B.2 i ∧ B.2 i < 1 := by
    have h := mem_iInter.mp hB i
    exact ⟨h.1.1, h.1.2, h.2⟩
  refine ⟨⟨⟨fun i => (ht i).1.le, fun i => ((ht i).1.trans (ht i).2.1).le⟩,
      ⟨fun i => ((ht i).2.1.trans (ht i).2.2).le, fun i => (ht i).2.2.le⟩⟩,
    mem_iInter.mpr (fun i => (ht i).2.1.le), ?_⟩
  refine mem_iInter.mpr fun x => mem_iInter.mpr fun hx => mem_iInter.mpr fun i => ⟨?_, ?_⟩
  · by_contra hn
    have hi : B.2 i < x i := lt_of_not_ge fun hi => hn (Or.inl hi)
    have hj : B.2 (next i) < x (next i) := lt_of_not_ge fun hj => hn (Or.inr hj)
    have h := (hs x hx (true, i)).trans (hc (true, i))
    simp only [row_upper] at h
    linarith only [h, hi, mul_lt_mul_of_pos_left hj (ha i)]
  · by_contra hn
    have hi : x i < B.1 i := lt_of_not_ge fun hi => hn (Or.inl hi)
    have hj : x (next i) < B.1 (next i) := lt_of_not_ge fun hj => hn (Or.inr hj)
    have h := (hs x hx (false, i)).trans (hc (false, i))
    simp only [row_lower] at h
    linarith only [h, hi, mul_lt_mul_of_pos_left hj (hb i)]

/-- Every positive supporting row is tight at an extreme cover with strict
wall inequalities: six rows in six dimensions must all be active. -/
theorem rows_tight_of_extreme (K : Set Point) (B : Walls)
    (hB : B ∈ (wallSet K).extremePoints ℝ) (hstrict : B ∈ strictWalls)
    (a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (c : Bool × Fin 3 → ℝ) (hs : ∀ x ∈ K, ∀ j, row a b j (x, x) ≤ c j)
    (hc : ∀ j, c j ≤ row a b j B) : ∀ j, c j = row a b j B := by
  apply ExtremeMinimumRank.all_active_of_card_le_finrank (wallSet K) strictWalls B
    hB open_strictWalls hstrict (row a b) c hc (row_constraints_suffice K a b ha hb c hs)
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    Module.finrank_prod, Module.finrank_pi]
  norm_num

def cut (j : Bool × Fin 3) : Point →ᵃ[ℝ] ℝ :=
  if j.1 then AffineMap.proj j.2 else -AffineMap.proj j.2

def wall (B : Walls) (j : Bool × Fin 3) : ℝ := if j.1 then B.2 j.2 else -B.1 j.2

def succ (j : Bool × Fin 3) : Bool × Fin 3 := (j.1, next j.2)

theorem cut_continuous (j : Bool × Fin 3) : Continuous (cut j) := by
  rcases j with ⟨s, i⟩
  cases s
  · change Continuous (fun x : Point => -x i)
    fun_prop
  · change Continuous (fun x : Point => x i)
    fun_prop

@[simp] theorem wall_diagonal (x : Point) (j : Bool × Fin 3) : wall (x, x) j = cut j x := by
  rcases j with ⟨s, i⟩; cases s <;> rfl

theorem row_eq (r : Bool × Fin 3 → ℝ) (j : Bool × Fin 3) (B : Walls) :
    row (fun i => r (true, i)) (fun i => r (false, i)) j B =
      wall B j + r j * wall B (succ j) := by
  rcases j with ⟨s, i⟩
  cases s
  · change -(B.1 i + r (false, i) * B.1 (next i)) =
      -B.1 i + r (false, i) * -B.1 (next i)
    ring
  · rfl

theorem cap_empty (K : Set Point) (B : Walls) (hB : B ∈ wallSet K) (j : Bool × Fin 3) :
    ¬ ∃ x ∈ K, wall B j < cut j x ∧ wall B (succ j) < cut (succ j) x := by
  rintro ⟨x, hx, h1, h2⟩
  have hc : (x j.2 ≤ B.2 j.2 ∨ x (next j.2) ≤ B.2 (next j.2)) ∧
      (B.1 j.2 ≤ x j.2 ∨ B.1 (next j.2) ≤ x (next j.2)) :=
    mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hB.2.2 x) hx) j.2
  rcases j with ⟨s, i⟩
  cases s
  · change -B.1 i < -x i at h1
    change -B.1 (next i) < -x (next i) at h2
    rcases hc.2 with h | h <;> linarith only [h, h1, h2]
  · change B.2 i < x i at h1
    change B.2 (next i) < x (next i) at h2
    rcases hc.1 with h | h <;> linarith only [h, h1, h2]

theorem cut_witness (K : Set Point) (B : Walls) (hB : B ∈ strictWalls)
    (hmin : ∀ i, ∃ x ∈ K, x i = 0) (hmax : ∀ i, ∃ x ∈ K, x i = 1)
    (j : Bool × Fin 3) : ∃ x ∈ K, wall B j < cut j x := by
  have hs : (0 < B.1 j.2 ∧ B.1 j.2 < B.2 j.2) ∧ B.2 j.2 < 1 := mem_iInter.mp hB j.2
  rcases j with ⟨s, i⟩
  cases s
  · obtain ⟨x, hx, hx0⟩ := hmin i
    refine ⟨x, hx, ?_⟩
    change -B.1 i < -x i
    rw [hx0]
    linarith only [hs.1.1]
  · obtain ⟨x, hx, hx1⟩ := hmax i
    refine ⟨x, hx, ?_⟩
    change B.2 i < x i
    rw [hx1]
    exact hs.2

theorem pair_contacts_of_extreme (K : Set Point) (hc : IsCompact K) (hv : Convex ℝ K)
    (B : Walls) (hB : B ∈ (wallSet K).extremePoints ℝ) (hstrict : B ∈ strictWalls)
    (hmin : ∀ i, ∃ x ∈ K, x i = 0) (hmax : ∀ i, ∃ x ∈ K, x i = 1) :
    ∀ j, ∃ x ∈ K, cut j x = wall B j ∧ cut (succ j) x = wall B (succ j) := by
  have hw := cut_witness K B hstrict hmin hmax
  have hsep (j : Bool × Fin 3) := CompactPairSeparation.support_with_contact K hc hv
    (cut j) (cut (succ j)) (cut_continuous j) (cut_continuous (succ j))
    (wall B j) (wall B (succ j)) (hw j) (hw (succ j)) (cap_empty K B hB.1 j)
  choose r hr c hc' hcontact hs using hsep
  have ht := rows_tight_of_extreme K B hB hstrict (fun i => r (true, i))
    (fun i => r (false, i)) (fun i => hr (true, i)) (fun i => hr (false, i)) c
    (fun x hx k => by simpa only [row_eq, wall_diagonal] using hs k x hx)
    (fun k => by simpa only [row_eq] using hc' k)
  intro j
  exact (hcontact j).mp (by simpa only [row_eq] using ht j)

/-- All six lower and upper pair corners meet the body. Strict positivity of
widths and both endpoint margins is explicit; minimality itself is unnecessary. -/
theorem upper_lower_contacts_of_extreme (K : Set Point) (hc : IsCompact K) (hv : Convex ℝ K)
    (B : Walls) (hB : B ∈ (wallSet K).extremePoints ℝ) (hstrict : B ∈ strictWalls)
    (hmin : ∀ i, ∃ x ∈ K, x i = 0) (hmax : ∀ i, ∃ x ∈ K, x i = 1) :
    ∀ i, (∃ x ∈ K, x i = B.1 i ∧ x (next i) = B.1 (next i)) ∧
      (∃ x ∈ K, x i = B.2 i ∧ x (next i) = B.2 (next i)) := by
  have hs := pair_contacts_of_extreme K hc hv B hB hstrict hmin hmax
  intro i
  constructor
  · obtain ⟨x, hx, h1, h2⟩ := hs (false, i)
    exact ⟨x, hx, neg_inj.mp h1, neg_inj.mp h2⟩
  · exact hs (true, i)

end Plank.Convex.SameSignCapMinimum
