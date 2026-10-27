/- Coordinate windows, escape signs, and strict endpoints. -/
module
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp
@[expose] public section
set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators Topology

namespace Plank.Convex.PlanarCoverSpace

abbrev Point (n : ℕ) := Fin n → ℝ
abbrev Walls (n : ℕ) := Point n × Point n

def cut {n : ℕ} (side : Bool) (i : Fin n) : Point n →L[ℝ] ℝ :=
  if side then ContinuousLinearMap.proj i else -ContinuousLinearMap.proj i

def wall {n : ℕ} (side : Bool) (i : Fin n) : Walls n →L[ℝ] ℝ :=
  if side then (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)
  else -(ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

def Covers {n : ℕ} (K : Set (Point n)) (B : Walls n) : Prop :=
  ∀ x ∈ K, ∃ i, B.1 i ≤ x i ∧ x i ≤ B.2 i

def Escapes {n : ℕ} (B : Walls n) (s : Fin n → Bool) (x : Point n) : Prop :=
  ∀ i, wall (s i) i B < cut (s i) i x

theorem covers_iff_no_escape {n : ℕ} (K : Set (Point n)) (B : Walls n) :
    Covers K B ↔ ∀ s, ¬ ∃ x ∈ K, Escapes B s x := by
  classical
  constructor
  · intro hc s ⟨x, hx, he⟩
    obtain ⟨i, hl, hu⟩ := hc x hx
    have hi := he i
    cases hs : s i <;> simp [wall, cut, hs] at hi <;> linarith
  · intro he x hx
    by_contra hn
    let s : Fin n → Bool := fun i => decide (B.2 i < x i)
    apply he s
    refine ⟨x, hx, ?_⟩
    intro i
    by_cases hh : B.2 i < x i
    · simp [s, wall, cut, hh]
    · have hl : x i < B.1 i := lt_of_not_ge (fun h => hn ⟨i, h, le_of_not_gt hh⟩)
      simp [s, wall, cut, hh, hl]

def coverSet {n : ℕ} (K : Set (Point n)) : Set (Walls n) := {B | Covers K B}

/-- Ordered covering windows with all endpoints in the unit interval. -/
def unitCovers {n : ℕ} (K : Set (Point n)) : Set (Walls n) :=
  (Icc (0, 0) (1, 1) ∩ {B | ∀ i, B.1 i ≤ B.2 i}) ∩ coverSet K

def strictWindows {n : ℕ} : Set (Walls n) :=
  {B | ∀ i, 0 < B.1 i ∧ B.1 i < B.2 i ∧ B.2 i < 1}

theorem open_strictWindows {n : ℕ} : IsOpen (strictWindows (n := n)) := by
  simp only [strictWindows, ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (by fun_prop : Continuous (fun B : Walls n => B.1 i))).inter
    ((isOpen_lt (by fun_prop : Continuous (fun B : Walls n => B.1 i))
      (by fun_prop : Continuous (fun B : Walls n => B.2 i))).inter
      (isOpen_lt (by fun_prop : Continuous (fun B : Walls n => B.2 i)) continuous_const))

theorem unitCovers_of_strict_cover {n : ℕ} (K : Set (Point n))
    (Y : Walls n) (hY : Y ∈ strictWindows) (hc : Covers K Y) : Y ∈ unitCovers K := by
  refine ⟨⟨?_, fun i => (hY i).2.1.le⟩, hc⟩
  constructor
  · exact ⟨fun i => (hY i).1.le, fun i => (hY i).1.le.trans (hY i).2.1.le⟩
  · exact ⟨fun i => (hY i).2.1.le.trans (hY i).2.2.le, fun i => (hY i).2.2.le⟩

theorem closed_coverSet {n : ℕ} (K : Set (Point n)) : IsClosed (coverSet K) := by
  have he : coverSet K = ⋂ x ∈ K, ⋃ i : Fin n,
      {B : Walls n | B.1 i ≤ x i} ∩ {B : Walls n | x i ≤ B.2 i} := by
    ext B
    simp [coverSet, Covers]
  rw [he]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iUnion_of_finite fun i =>
    (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le continuous_const (by fun_prop))

theorem compact_unitCovers {n : ℕ} (K : Set (Point n)) : IsCompact (unitCovers K) := by
  apply IsCompact.inter_right
  · apply isCompact_Icc.inter_right
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)
  · exact closed_coverSet K

end Plank.Convex.PlanarCoverSpace
