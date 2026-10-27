/- Closure of actual sharp configurations cannot lose all non-diagonal width. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralBoundaryModel

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralBoundaryClosure
open Set MeasureTheory Filter CrossedQuadrilateralAttainment CrossedQuadrilateralInnerPacking
open CrossedQuadrilateralBoundaryModel CrossedQuadrilateralBoundaryNeighborhood
open CrossedQuadrilateralThinExtension
open scoped Topology

def envelope (S : Shape) (k : Fin 2 → ℝ) : Set State :=
  {p | Ordered p} ∩ {p | fullBudget S k p ≤ 1} ∩ {p | Tight S k p}

/-- Actual equality with positive total non-diagonal width. Up to four bands are
represented, so the later three-band applications can insert null slots. -/
def sharp (S : Shape) (k : Fin 2 → ℝ) : Set State :=
  envelope S k ∩ {p | 0 < badBudget S k p}

theorem isClosed_envelope (S : Shape) (k : Fin 2 → ℝ) : IsClosed (envelope S k) := by
  have ho : IsClosed {p : State | Ordered p} := by
    simp only [Ordered,Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le (by fun_prop) (by fun_prop))
  exact (ho.inter (isClosed_le (continuous_fullBudget S k) continuous_const)).inter
    (isClosed_eq (continuous_area S k)
      (((continuous_const.sub (continuous_fullBudget S k)).pow 2).mul_const _))

theorem closure_subset (S : Shape) (k : Fin 2 → ℝ) :
    closure (sharp S k) ⊆ envelope S k :=
  closure_minimal inter_subset_left (isClosed_envelope S k)

theorem bad_le_full (S : Shape) (k : Fin 2 → ℝ) {p : State} (hp : Ordered p) :
    badBudget S k p ≤ fullBudget S k p := by
  have hx := div_nonneg (sub_nonneg.mpr (hp 0)) (add_pos S.ha S.hc).le
  have hy := div_nonneg (sub_nonneg.mpr (hp 1)) (add_pos S.hb S.hd).le
  dsimp only [fullBudget,budget]
  linarith only [hx,hy]

/-- The closure is taken in all physical endpoints. At every subcritical point
of that closure, the total actual width in the non-diagonal directions remains
strictly positive. This includes and excludes a putative zero-budget limit. -/
theorem positive_bad_in_closure (S : Shape) (k : Fin 2 → ℝ) (hk : ∀ i, k i ≠ 0)
    {p : State} (hp : p ∈ closure (sharp S k)) (hR : fullBudget S k p < 1) :
    0 < badBudget S k p := by
  have he := closure_subset S k hp
  have hpO : Ordered p := he.1.1
  have hpT : Tight S k p := he.2
  by_contra hn
  have hz : badBudget S k p = 0 := le_antisymm (le_of_not_gt hn)
    (badBudget_nonneg S k hpO)
  obtain ⟨hbx,hby⟩ := balanced_of_null_tight S k hpO hz hR hpT
  have hcx := calibrated_of_balanced S.ha S.hc hbx
  have hcy := calibrated_of_balanced S.hb S.hd hby
  have hr := div_nonneg (sub_nonneg.mpr (hpO 0)) (add_pos S.ha S.hc).le
  have hs := div_nonneg (sub_nonneg.mpr (hpO 1)) (add_pos S.hb S.hd).le
  have hrs : (p.2 0-p.1 0)/(S.a+S.c)+(p.2 1-p.1 1)/(S.b+S.d) < 1 := by
    simpa only [fullBudget,hz,add_zero,budget] using hR
  let F := 𝓝[sharp S k] p
  have : NeBot F := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hlo (i : Fin 4) : Tendsto (fun q : State => q.1 i) F (𝓝 (p.1 i)) :=
    ((show Continuous (fun q : State => q.1 i) from by fun_prop).tendsto p).mono_left
      nhdsWithin_le_nhds
  have hhi (i : Fin 4) : Tendsto (fun q : State => q.2 i) F (𝓝 (p.2 i)) :=
    ((show Continuous (fun q : State => q.2 i) from by fun_prop).tendsto p).mono_left
      nhdsWithin_le_nhds
  have ht : Tendsto (fun q => total S k (badLo q) (badHi q)) F (𝓝 0) := by
    have hh := (continuous_badBudget S k).tendsto p
    rw [hz] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have hstrict := eventually_strict S k hk hr hs hrs hcx hcy
    (fun q : State => q.1 0) (fun q => q.2 0) (fun q => q.1 1) (fun q => q.2 1)
    badLo badHi (hlo 0) (hhi 0) (hlo 1) (hhi 1) ht
  have hmem : ∀ᶠ q in F, q ∈ sharp S k := self_mem_nhdsWithin
  obtain ⟨q,hqstrict,hq⟩ := (hstrict.and hmem).exists
  have hqO : Ordered q := hq.1.1.1
  have hh := hqstrict (hqO 0) (hqO 1) (bad_ordered hqO) hq.2
  change (1-budget S (q.1 0) (q.2 0) (q.1 1) (q.2 1)-total S k (badLo q) (badHi q))^2*
    (volume S.body).toReal < CrossedQuadrilateralBoundaryModel.area S k q at hh
  have htarget : 1-budget S (q.1 0) (q.2 0) (q.1 1) (q.2 1)-total S k (badLo q) (badHi q) =
      1-fullBudget S k q := by unfold fullBudget badBudget; ring
  have heq : CrossedQuadrilateralBoundaryModel.area S k q = (1-fullBudget S k q)^2*(volume S.body).toReal := hq.1.2
  rw [htarget,heq] at hh
  exact (lt_irrefl _) hh

theorem positive_budget_in_closure (S : Shape) (k : Fin 2 → ℝ) (hk : ∀ i, k i ≠ 0)
    {p : State} (hp : p ∈ closure (sharp S k)) (hR : fullBudget S k p < 1) :
    0 < fullBudget S k p :=
  (positive_bad_in_closure S k hk hp hR).trans_le
    (bad_le_full S k (closure_subset S k hp).1.1)

end Quant.CrossedQuadrilateralBoundaryClosure

/-- info: 'Quant.CrossedQuadrilateralBoundaryClosure.positive_bad_in_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralBoundaryClosure.positive_bad_in_closure
