/- Finite cases for the six mixed escape patterns.

At node i of a six-cycle, an empty same-sign pair cap covers node i alone;
an empty mixed pair cap covers the endpoints of edge i. A cover by such
caps contains one of the 39 labelled minimal patterns below. Those patterns
form eight dihedral classes. This file proves the finite combinatorics only;
it asserts no width bound and no closure of the eight geometric cases.
-/
module
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option autoImplicit false

namespace Plank.Convex.PlanarCapPatterns

structure Pattern where
  singles : Nat
  edges : Nat
  deriving DecidableEq, Repr

/-- A bit in singles covers one node; a bit in edges covers its two endpoints. -/
def covers (p : Pattern) : Bool :=
  (List.finRange 6).all fun i => p.singles.testBit i.val ||
    p.edges.testBit i.val || p.edges.testBit ((i.val + 5) % 6)

def contained (p q : Pattern) : Bool :=
  (Nat.land p.singles q.singles == p.singles) &&
    (Nat.land p.edges q.edges == p.edges)

def prev (i : Fin 6) : Fin 6 := ⟨(i.val + 5) % 6, Nat.mod_lt _ (by decide)⟩

/-- The caps selected by a pattern are empty, as expressed by the supplied predicates. -/
def Holds (single edge : Fin 6 → Prop) (p : Pattern) : Prop :=
  (∀ i, p.singles.testBit i.val = true → single i) ∧
  (∀ i, p.edges.testBit i.val = true → edge i)

def minimal (p : Pattern) : Bool := covers p &&
  (List.finRange 6).all (fun i =>
    (!p.singles.testBit i.val || !covers ⟨p.singles - 2^i.val, p.edges⟩) &&
    (!p.edges.testBit i.val || !covers ⟨p.singles, p.edges - 2^i.val⟩))

/-- Exhaustive labelled cases, encoded by the six singleton bits and six edge bits. -/
def patterns : List Pattern := [
  ⟨63,0⟩, ⟨60,1⟩, ⟨57,2⟩, ⟨56,3⟩, ⟨51,4⟩, ⟨48,5⟩, ⟨49,6⟩,
  ⟨39,8⟩, ⟨36,9⟩, ⟨33,10⟩, ⟨32,11⟩, ⟨35,12⟩, ⟨32,13⟩,
  ⟨15,16⟩, ⟨12,17⟩, ⟨9,18⟩, ⟨8,19⟩, ⟨3,20⟩, ⟨0,21⟩,
  ⟨1,22⟩, ⟨7,24⟩, ⟨4,25⟩, ⟨1,26⟩, ⟨0,27⟩,
  ⟨30,32⟩, ⟨28,33⟩, ⟨24,34⟩, ⟨18,36⟩, ⟨16,37⟩, ⟨16,38⟩,
  ⟨6,40⟩, ⟨4,41⟩, ⟨0,42⟩, ⟨2,44⟩, ⟨0,45⟩,
  ⟨14,48⟩, ⟨8,50⟩, ⟨2,52⟩, ⟨0,54⟩]

def representatives : List Pattern := [
  ⟨63,0⟩, ⟨60,1⟩, ⟨56,3⟩, ⟨48,5⟩,
  ⟨36,9⟩, ⟨32,11⟩, ⟨0,21⟩, ⟨0,27⟩]

def transformBits (mask : Nat) (rotation : Fin 6) (flip edge : Bool) : Nat :=
  ((List.finRange 6).map fun i =>
    if mask.testBit i.val then
      2 ^ ((if flip then rotation.val + (if edge then 11 else 6) - i.val
            else rotation.val + i.val) % 6)
    else 0).sum

def transform (p : Pattern) (rotation : Fin 6) (flip : Bool) : Pattern :=
  ⟨transformBits p.singles rotation flip false,
   transformBits p.edges rotation flip true⟩

def sameOrbit (p q : Pattern) : Bool :=
  (List.finRange 6).any fun r =>
    transform p r false == q || transform p r true == q

-- Small kernel-checked batches keep both compilation and replay bounded.
private def censusBlock (q : Nat) : Bool :=
  (List.finRange 8).all fun r => (List.finRange 64).all fun e =>
    !covers ⟨8*q + r.val, e.val⟩ ||
      patterns.any (fun p => contained p ⟨8*q + r.val, e.val⟩)

private theorem census0 : censusBlock 0 = true := by decide +kernel
private theorem census1 : censusBlock 1 = true := by decide +kernel
private theorem census2 : censusBlock 2 = true := by decide +kernel
private theorem census3 : censusBlock 3 = true := by decide +kernel
private theorem census4 : censusBlock 4 = true := by decide +kernel
private theorem census5 : censusBlock 5 = true := by decide +kernel
private theorem census6 : censusBlock 6 = true := by decide +kernel
private theorem census7 : censusBlock 7 = true := by decide +kernel

private theorem exhaustive_census :
    ∀ s e : Fin 64, covers ⟨s.val,e.val⟩ = true →
      (patterns.any fun p => contained p ⟨s.val,e.val⟩) = true := by
  have census (q : Fin 8) : censusBlock q.val = true := by
    fin_cases q
    · exact census0
    · exact census1
    · exact census2
    · exact census3
    · exact census4
    · exact census5
    · exact census6
    · exact census7
  intro s e h
  let q : Fin 8 := ⟨s.val / 8, by omega⟩
  let r : Fin 8 := ⟨s.val % 8, Nat.mod_lt _ (by decide)⟩
  have heq : 8*q.val + r.val = s.val := by dsimp [q, r]; omega
  have hr := List.all_eq_true.mp (census q) r (List.mem_finRange r)
  have hc := List.all_eq_true.mp hr e (List.mem_finRange e)
  change (!covers ⟨8*q.val + r.val, e.val⟩ ||
    patterns.any (fun p => contained p ⟨8*q.val + r.val, e.val⟩)) = true at hc
  rw [heq] at hc
  simpa only [h, Bool.not_true, Bool.false_or] using hc

/-- Every assignment of empty caps covering all six nodes contains a listed pattern. -/
theorem exists_pattern (s e : Fin 64) (h : covers ⟨s.val,e.val⟩ = true) :
    ∃ p ∈ patterns, contained p ⟨s.val,e.val⟩ = true := by
  exact List.any_eq_true.mp (exhaustive_census s e h)

theorem patterns_minimal : patterns.all minimal = true := by decide

theorem patterns_distinct : patterns.Nodup := by decide

theorem patterns_count : patterns.length = 39 := rfl

private theorem orbit_census :
    patterns.all (fun p => representatives.any (fun q => sameOrbit q p)) = true := by
  decide

/-- The 39 listed patterns reduce to the eight representatives by six-cycle symmetries. -/
theorem exists_representative (p : Pattern) (hp : p ∈ patterns) :
    ∃ q ∈ representatives, sameOrbit q p = true := by
  exact List.any_eq_true.mp (List.all_eq_true.mp orbit_census p hp)

theorem representatives_count : representatives.length = 8 := rfl

/-- No two representatives lie in the same dihedral orbit. -/
theorem representatives_separate :
    representatives.Pairwise (fun p q => sameOrbit p q = false) := by decide

theorem orbit_sizes :
    representatives.map (fun p => (patterns.filter (fun q => sameOrbit p q)).length) =
      [1, 6, 6, 6, 3, 12, 2, 3] := by decide +kernel

private theorem encode_bits :
    ∀ g : Fin 6 → Bool, ∃ s : Fin 64, ∀ i : Fin 6, s.val.testBit i.val = g i := by
  have enc : ∀ b0 b1 b2 b3 b4 b5 : Bool, ∃ s : Fin 64,
      s.val.testBit 0 = b0 ∧ s.val.testBit 1 = b1 ∧
      s.val.testBit 2 = b2 ∧ s.val.testBit 3 = b3 ∧
      s.val.testBit 4 = b4 ∧ s.val.testBit 5 = b5 := by
    intro b0 b1 b2 b3 b4 b5
    refine ⟨⟨b0.toNat + 2*b1.toNat + 4*b2.toNat + 8*b3.toNat +
      16*b4.toNat + 32*b5.toNat, ?_⟩, ?_⟩
    · cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide
    · cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide
  intro g
  obtain ⟨s, h0, h1, h2, h3, h4, h5⟩ := enc (g 0) (g 1) (g 2) (g 3) (g 4) (g 5)
  refine ⟨s, ?_⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

private theorem contained_bits {p q : Pattern} (h : contained p q = true) (i : Fin 6) :
    (p.singles.testBit i.val = true → q.singles.testBit i.val = true) ∧
    (p.edges.testBit i.val = true → q.edges.testBit i.val = true) := by
  simp only [contained, Bool.and_eq_true, beq_iff_eq] at h
  constructor
  · intro hb
    have ht := congrArg (fun n => n.testBit i.val) h.1
    simpa only [Nat.land_eq, Nat.testBit_land, hb, Bool.true_and] using ht
  · intro hb
    have ht := congrArg (fun n => n.testBit i.val) h.2
    simpa only [Nat.land_eq, Nat.testBit_land, hb, Bool.true_and] using ht

/-- An arbitrary geometric cap assignment covering the six nodes contains a
listed minimal pattern. No decidability hypothesis on cap emptiness is needed. -/
theorem exists_holding_pattern (single edge : Fin 6 → Prop)
    (h : ∀ i, single i ∨ edge i ∨ edge (prev i)) :
    ∃ p ∈ patterns, Holds single edge p := by
  classical
  obtain ⟨s, hs⟩ := encode_bits (fun i => decide (single i))
  obtain ⟨e, he⟩ := encode_bits (fun i => decide (edge i))
  have hc : covers ⟨s.val, e.val⟩ = true := by
    apply List.all_eq_true.mpr
    intro i _
    change (s.val.testBit i.val || e.val.testBit i.val ||
      e.val.testBit (prev i).val) = true
    rw [hs i, he i, he (prev i)]
    rcases h i with hi | hi | hi <;> simp [hi]
  obtain ⟨p, hp, hpq⟩ := exists_pattern s e hc
  refine ⟨p, hp, ?_, ?_⟩
  · intro i hi
    have ht := (contained_bits hpq i).1 hi
    simpa only [hs i, decide_eq_true_eq] using ht
  · intro i hi
    have ht := (contained_bits hpq i).2 hi
    simpa only [he i, decide_eq_true_eq] using ht

/-- Every listed pattern covers all nodes, so its selected cap predicates
supply the three-way alternative at each node. -/
theorem nodes_of_holding_pattern (single edge : Fin 6 → Prop)
    (p : Pattern) (hp : p ∈ patterns) (hh : Holds single edge p) (i : Fin 6) :
    single i ∨ edge i ∨ edge (prev i) := by
  have hm := List.all_eq_true.mp patterns_minimal p hp
  simp only [minimal, Bool.and_eq_true] at hm
  have hc : covers p = true := hm.1
  have hi := List.all_eq_true.mp hc i (List.mem_finRange i)
  change (p.singles.testBit i.val || p.edges.testBit i.val ||
    p.edges.testBit (prev i).val) = true at hi
  simp only [Bool.or_eq_true] at hi
  rcases hi with hi | hi
  · rcases hi with hi | hi
    · exact Or.inl (hh.1 i hi)
    · exact Or.inr (Or.inl (hh.2 i hi))
  · exact Or.inr (Or.inr (hh.2 (prev i) hi))

end Plank.Convex.PlanarCapPatterns

/-- info: 'Plank.Convex.PlanarCapPatterns.exists_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapPatterns.exists_pattern

/-- info: 'Plank.Convex.PlanarCapPatterns.patterns_minimal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapPatterns.patterns_minimal

/-- info: 'Plank.Convex.PlanarCapPatterns.exists_representative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapPatterns.exists_representative

/-- info: 'Plank.Convex.PlanarCapPatterns.exists_holding_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapPatterns.exists_holding_pattern

/-- info: 'Plank.Convex.PlanarCapPatterns.representatives_separate' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarCapPatterns.representatives_separate
