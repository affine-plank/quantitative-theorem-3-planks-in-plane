/- Balanced support slopes at positive-width equality force every transfer
to be one and saturate the opposite-coordinate support inequalities. -/
module
public import Plank.Convex.PlanarTight.ProductBudgetEquality
public import Plank.Convex.SameSignCapTightRigidity
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Plank.Convex.PlanarTight.SameSignEquality

open SameSignCapAlgebra SameSignCapTransfer SameSignCapProduct

/-- Unit budgets and reciprocal transfers around a balanced cycle force
all six directed transfers to equal one. -/
theorem transfers_eq_one (w f r : Point) (hf : ∀ i, 0 < f i)
    (hpair : ∀ i, f i * r (next i) = 1) (hprod : ∏ i, f i = 1)
    (hbudget : ∀ i, budget w f r i = 1) : ∀ i, f i = 1 ∧ r i = 1 := by
  have hreverse (i : Fin 3) : f i * f (next i) = r i := by
    have hcycle : f i * f (next i) * f (prev i) = 1 := by
      calc
        _ = ∏ j, f j := by
          fin_cases i <;> simp [Fin.prod_univ_three, next, prev] <;> ring
        _ = 1 := hprod
    have hp := hpair (prev i)
    rw [next_prev] at hp
    have hz : f (prev i) * (f i * f (next i) - r i) = 0 := by
      nlinarith only [hcycle, hp]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (hf _).ne')
  have hforward (i : Fin 3) : f i = 1 := by
    have heq : f i * budget w f r (next i) = budget w f r i := by
      calc
        _ = f i * w (next i) + (f i * f (next i)) * w (prev i) +
            (f i * r (next i)) * w i := by
          simp only [budget, next_next, prev_next]
          ring
        _ = budget w f r i := by rw [hreverse, hpair]; dsimp [budget]; ring
    simpa only [hbudget, mul_one] using heq
  intro i
  refine ⟨hforward i, ?_⟩
  have h := hpair (prev i)
  simpa only [hforward, next_prev, one_mul] using h

/-- The balanced-slope equality case has no nontrivial transfer weights. -/
theorem balanced_transfers (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (hw : ∀ i, lo i < hi i)
    (hsum : ∑ i, (hi i - lo i) = 1) (hp : slopeProduct a b = 1) :
    ∀ i, forward a b i = 1 ∧ reverse a b i = 1 := by
  have hf (i : Fin 3) : 0 < forward a b i :=
    add_pos (div_pos (hb i) (lowerDen_pos a b ha hb i))
      (div_pos (ha i) (upperDen_pos a b ha hb i))
  have hr (i : Fin 3) : 0 ≤ reverse a b i :=
    add_nonneg
      (div_nonneg (mul_pos (hb i) (ha _)).le (lowerDen_pos a b ha hb i).le)
      (div_nonneg (mul_pos (ha i) (hb _)).le (upperDen_pos a b ha hb i).le)
  have hprodF : ∏ i, forward a b i = 1 := by
    have h := forward_product_gap a b ha hb
    rw [hp, sub_self, zero_mul, zero_div] at h
    linarith only [h]
  have hprodR : ∏ i, reverse a b i = 1 := by
    have h := reverse_product_gap a b ha hb
    rw [hp, sub_self, zero_mul, zero_div] at h
    linarith only [h]
  have hcycle : (∏ i, forward a b i) + (∏ i, reverse a b i) ≤ 2 := by
    rw [hprodF, hprodR]
    norm_num
  have hpairs := SameSignCapTightRigidity.pair_eq_one_of_tight
    (fun i => hi i - lo i) (forward a b) (reverse a b)
    (fun i => sub_pos.mpr (hw i)) hf hr (pair_le_one a b ha hb) hcycle
    (transfer_bound lo hi a b ha hb hrows) hsum
  have hbudgets := ProductBudgetEquality.budgets_eq_one
    (fun i => hi i - lo i) (forward a b) (reverse a b)
    (fun i => sub_pos.mpr (hw i)) (fun i => (hf i).le) hr
    (pair_le_one a b ha hb) hcycle (transfer_bound lo hi a b ha hb hrows) hsum
  exact transfers_eq_one _ _ _ hf hpairs hprodF hbudgets

/-- Both opposite-coordinate inequalities are equalities at every index. -/
theorem balanced_rows (lo hi a b : Point)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hrows : NumericRows lo hi a b) (hw : ∀ i, lo i < hi i)
    (hsum : ∑ i, (hi i - lo i) = 1) (hp : slopeProduct a b = 1) :
    ∀ i,
      lo i * lowerDen a b i =
        b i * (hi (next i) - lo (next i)) + b i * a (next i) * (hi (prev i) - lo (prev i)) ∧
      (1 - hi i) * upperDen a b i =
        a i * (hi (next i) - lo (next i)) + a i * b (next i) * (hi (prev i) - lo (prev i)) := by
  have htrans := balanced_transfers lo hi a b ha hb hrows hw hsum hp
  intro i
  let L := (b i * (hi (next i) - lo (next i)) +
    b i * a (next i) * (hi (prev i) - lo (prev i))) / lowerDen a b i
  let U := (a i * (hi (next i) - lo (next i)) +
    a i * b (next i) * (hi (prev i) - lo (prev i))) / upperDen a b i
  have hl : lo i ≤ L := (le_div_iff₀ (lowerDen_pos a b ha hb i)).mpr (hrows i).2.2.2.2.1
  have hu : 1 - hi i ≤ U := (le_div_iff₀ (upperDen_pos a b ha hb i)).mpr (hrows i).2.2.2.2.2
  have hLU : L + U = lo i + (1 - hi i) := by
    calc
      L + U = forward a b i * (hi (next i) - lo (next i)) +
          reverse a b i * (hi (prev i) - lo (prev i)) := by
        dsimp [L, U, forward, reverse]
        ring
      _ = (hi (next i) - lo (next i)) + (hi (prev i) - lo (prev i)) := by
        rw [(htrans i).1, (htrans i).2, one_mul, one_mul]
      _ = lo i + (1 - hi i) := by
        have h := sum_cycle (fun j => hi j - lo j) i
        rw [hsum] at h
        linarith only [h]
  have heL : lo i = L := by linarith only [hl, hu, hLU]
  have heU : 1 - hi i = U := by linarith only [hl, hu, hLU]
  exact ⟨(eq_div_iff (lowerDen_pos a b ha hb i).ne').mp heL,
    (eq_div_iff (upperDen_pos a b ha hb i).ne').mp heU⟩

private theorem three_slacks (s t u a b : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (ha : 0 < a) (hb : 0 < b) (heq : s + a * t + b * u = 0) :
    s = 0 ∧ t = 0 ∧ u = 0 := by
  have hta := mul_nonneg ha.le ht
  have hub := mul_nonneg hb.le hu
  have hs0 : s = 0 := by linarith only [heq, hs, hta, hub]
  have ht0 : a * t = 0 := by linarith only [heq, hs, hta, hub]
  have hu0 : b * u = 0 := by linarith only [heq, hs, hta, hub]
  exact ⟨hs0, (mul_eq_zero.mp ht0).resolve_left ha.ne',
    (mul_eq_zero.mp hu0).resolve_left hb.ne'⟩

/-- Every actual coordinate maximum lies on the two adjacent upper support
lines and on the remaining lower support line. These are contacts of the
original body, without any movement of the supplied endpoints. -/
theorem upper_contacts (K : Set Point)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (lo hi a b : Point) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hwidth : ∀ i, lo i < hi i) (hsum : ∑ i, (hi i - lo i) = 1)
    (hupper : UpperSupports K hi a) (hlower : LowerSupports K lo b)
    (hbalanced : slopeProduct a b = 1) :
    ∀ i, ∀ x ∈ K, x i = 1 →
      x i + a i * x (next i) = hi i + a i * hi (next i) ∧
      x (prev i) + a (prev i) * x i = hi (prev i) + a (prev i) * hi i ∧
      lo (next i) + b (next i) * lo (prev i) = x (next i) + b (next i) * x (prev i) := by
  have hrows := numeric_rows_of_supports K hbox hL hU lo hi a b ha hb hupper hlower
  have heqs := balanced_rows lo hi a b ha hb hrows hwidth hsum hbalanced
  intro i x hx hxi
  have h₀ := hupper i x hx
  have h₁ := hlower (next i) x hx
  have h₂ := hupper (prev i) x hx
  rw [hxi] at h₀
  rw [next_next] at h₁
  rw [next_prev, hxi, mul_one] at h₂
  let s := (hi i + a i * hi (next i)) - (1 + a i * x (next i))
  let t := (x (next i) + b (next i) * x (prev i)) -
    (lo (next i) + b (next i) * lo (prev i))
  let u := (hi (prev i) + a (prev i) * hi i) - (x (prev i) + a (prev i))
  have hs : 0 ≤ s := sub_nonneg.mpr h₀
  have ht : 0 ≤ t := sub_nonneg.mpr h₁
  have hu : 0 ≤ u := sub_nonneg.mpr h₂
  have heq : s + a i * t + (a i * b (next i)) * u = 0 := by
    have he := (heqs i).2
    dsimp [upperDen] at he
    dsimp [s, t, u]
    linear_combination -he
  obtain ⟨hs0, ht0, hu0⟩ := three_slacks s t u (a i) (a i * b (next i)) hs ht hu
    (ha i) (mul_pos (ha i) (hb _)) heq
  dsimp [s] at hs0
  dsimp [t] at ht0
  dsimp [u] at hu0
  rw [hxi, mul_one]
  exact ⟨by linarith only [hs0], by linarith only [hu0], by linarith only [ht0]⟩

end Plank.Convex.PlanarTight.SameSignEquality

/-- info: 'Plank.Convex.PlanarTight.SameSignEquality.transfers_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.SameSignEquality.transfers_eq_one

/-- info: 'Plank.Convex.PlanarTight.SameSignEquality.balanced_transfers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.SameSignEquality.balanced_transfers

/-- info: 'Plank.Convex.PlanarTight.SameSignEquality.balanced_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.SameSignEquality.balanced_rows

/-- info: 'Plank.Convex.PlanarTight.SameSignEquality.upper_contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.SameSignEquality.upper_contacts
