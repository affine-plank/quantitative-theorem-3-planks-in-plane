/- Finite point hulls: continuity, approximation and the open-set sampling step.
These are exact topological statements. No finite-precision random generator
or numerical volume computation is certified here. -/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteHullSampling

open Set TopologicalSpace Metric MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed nonempty finite anchor together with finitely many free points. -/
def sampleHull (A : Finset E) (hA : A.Nonempty) {n : ℕ} (x : Fin n → E) :
    NonemptyCompacts E where
  carrier := convexHull ℝ ((A : Set E) ∪ range x)
  isCompact' := (A.finite_toSet.union (finite_range x)).isCompact_convexHull ℝ
  nonempty' := (hA.to_set.mono subset_union_left).convexHull

theorem convex_sampleHull (A : Finset E) (hA : A.Nonempty) {n : ℕ} (x : Fin n → E) :
    Convex ℝ (sampleHull A hA x : Set E) := convex_convexHull ℝ _

theorem anchor_subset_sampleHull (A : Finset E) (hA : A.Nonempty)
    {n : ℕ} (x : Fin n → E) : (A : Set E) ⊆ sampleHull A hA x :=
  subset_union_left.trans (subset_convexHull ℝ _)

theorem range_subset_sampleHull (A : Finset E) (hA : A.Nonempty)
    {n : ℕ} (x : Fin n → E) : range x ⊆ sampleHull A hA x :=
  subset_union_right.trans (subset_convexHull ℝ _)

/-- Moving each free point by at most r moves the whole hull by at most r. -/
theorem dist_sampleHull_le (A : Finset E) (hA : A.Nonempty) {n : ℕ}
    (x y : Fin n → E) {r : ℝ} (hr : 0 ≤ r) (hxy : ∀ i, dist (x i) (y i) ≤ r) :
    dist (sampleHull A hA x) (sampleHull A hA y) ≤ r := by
  have hsub (f g : Fin n → E) (hfg : ∀ i, dist (f i) (g i) ≤ r) :
      (sampleHull A hA f : Set E) ⊆ cthickening r (sampleHull A hA g : Set E) := by
    apply convexHull_min _ ((convex_sampleHull A hA g).cthickening r)
    intro z hz
    rcases hz with hz | ⟨i,rfl⟩
    · exact mem_cthickening_of_dist_le z z r _ (anchor_subset_sampleHull A hA g hz)
        (by simpa only [dist_self] using hr)
    · exact mem_cthickening_of_dist_le (f i) (g i) r _
        (range_subset_sampleHull A hA g (mem_range_self i)) (hfg i)
  apply hausdorffDist_le_of_infDist hr
  · intro z hz
    exact ENNReal.toReal_le_of_le_ofReal hr (hsub x y hxy hz)
  · intro z hz
    exact ENNReal.toReal_le_of_le_ofReal hr
      (hsub y x (fun i => (dist_comm (y i) (x i)) ▸ hxy i) hz)

theorem lipschitz_sampleHull (A : Finset E) (hA : A.Nonempty) (n : ℕ) :
    LipschitzWith 1 (sampleHull A hA (n := n)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul] using
    dist_sampleHull_le A hA x y dist_nonneg (fun i => dist_le_pi_dist x y i)

theorem continuous_sampleHull (A : Finset E) (hA : A.Nonempty) (n : ℕ) :
    Continuous (sampleHull A hA (n := n)) :=
  (lipschitz_sampleHull A hA n).continuous

/-- Every compact convex body containing the anchor can be approximated by
such hulls using free points of that very body. No vertex-count bound is used. -/
theorem exists_sampleHull_approx (A : Finset E) (hA : A.Nonempty)
    (K : NonemptyCompacts E) (hK : Convex ℝ (K : Set E)) (hAK : (A : Set E) ⊆ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∃ x : Fin n → E, range x ⊆ K ∧ dist (sampleHull A hA x) K < ε := by
  classical
  obtain ⟨t,htK,htfin,htcover⟩ :=
    finite_approx_of_totallyBounded K.isCompact.totallyBounded (ε/2) (half_pos hε)
  let := htfin.fintype
  let e := Fintype.equivFin t
  let x : Fin (Fintype.card t) → E := fun i => (e.symm i).1
  have hx : range x = t := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      exact (e.symm i).2
    · intro hz
      refine ⟨e ⟨z,hz⟩,?_⟩
      simp only [x, Equiv.symm_apply_apply]
  have hsub : (sampleHull A hA x : Set E) ⊆ K :=
    convexHull_min (union_subset hAK (hx.symm ▸ htK)) hK
  refine ⟨Fintype.card t,x,hx.symm ▸ htK,?_⟩
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply hausdorffDist_le_of_mem_dist (half_pos hε).le
  · intro z hz
    exact ⟨z,hsub hz,by simpa only [dist_self] using (half_pos hε).le⟩
  · intro z hz
    obtain ⟨y,hy,hzy⟩ := mem_iUnion₂.mp (htcover hz)
    exact ⟨y,range_subset_sampleHull A hA x (hx.symm ▸ hy),(mem_ball.mp hzy).le⟩

/-- The normalized body domain keeps the same anchor and outer convex set. -/
abbrev AnchoredBody (A : Finset E) (H : Set E) :=
  {K : NonemptyCompacts E | Convex ℝ (K : Set E) ∧ (A : Set E) ⊆ K ∧ (K : Set E) ⊆ H}

def anchoredHull (A : Finset E) (hA : A.Nonempty) (H : Set E)
    (hH : Convex ℝ H) (hAH : (A : Set E) ⊆ H) {n : ℕ} (x : Fin n → H) :
    AnchoredBody A H :=
  ⟨sampleHull A hA (fun i => (x i).1), convex_sampleHull A hA _,
    anchor_subset_sampleHull A hA _,
    convexHull_min (union_subset hAH (by rintro z ⟨i,rfl⟩; exact (x i).2)) hH⟩

theorem continuous_anchoredHull (A : Finset E) (hA : A.Nonempty) (H : Set E)
    (hH : Convex ℝ H) (hAH : (A : Set E) ⊆ H) (n : ℕ) :
    Continuous (anchoredHull A hA H hH hAH (n := n)) := by
  apply Continuous.subtype_mk
  exact (continuous_sampleHull A hA n).comp (by fun_prop)

theorem exists_anchoredHull_approx (A : Finset E) (hA : A.Nonempty) (H : Set E)
    (hH : Convex ℝ H) (hAH : (A : Set E) ⊆ H) (K : AnchoredBody A H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n, ∃ x : Fin n → H, dist (anchoredHull A hA H hH hAH x) K < ε := by
  obtain ⟨n,x,hx,hd⟩ := exists_sampleHull_approx A hA K.1 K.2.1 K.2.2.1 hε
  let y : Fin n → H := fun i => ⟨x i,K.2.2.2 (hx (mem_range_self i))⟩
  exact ⟨n,y,hd⟩

section Parameter

variable {P : Type*} [TopologicalSpace P]

/-- A negative value of a continuous geometric functional persists on a
finite point hull, with all other parameters fixed. Continuity is an explicit
hypothesis; this theorem does not replace a proof of volume continuity. -/
theorem exists_negative_sample (A : Finset E) (hA : A.Nonempty) (H : Set E)
    (hH : Convex ℝ H) (hAH : (A : Set E) ⊆ H)
    (F : AnchoredBody A H × P → ℝ) (hF : Continuous F)
    {K : AnchoredBody A H} {p : P} (hbad : F (K,p) < 0) :
    ∃ n, ∃ x : Fin n → H, F (anchoredHull A hA H hH hAH x,p) < 0 := by
  have hc : Continuous (fun L : AnchoredBody A H => F (L,p)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have ho : IsOpen {L : AnchoredBody A H | F (L,p) < 0} :=
    isOpen_lt hc continuous_const
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp ho K hbad
  obtain ⟨n,x,hx⟩ := exists_anchoredHull_approx A hA H hH hAH K hε
  exact ⟨n,x,hball hx⟩

theorem isOpen_negative_samples (A : Finset E) (hA : A.Nonempty) (H : Set E)
    (hH : Convex ℝ H) (hAH : (A : Set E) ⊆ H) (n : ℕ)
    (F : AnchoredBody A H × P → ℝ) (hF : Continuous F) :
    IsOpen {q : (Fin n → H) × P | F (anchoredHull A hA H hH hAH q.1,q.2) < 0} :=
  isOpen_lt (hF.comp (((continuous_anchoredHull A hA H hH hAH n).comp
    continuous_fst).prodMk continuous_snd)) continuous_const

/-- Conditional on full support of the parameter law at each finite point
count, a strict negative value has positive measure at some count. The law
and continuity hypotheses are explicit; no software randomness is assumed. -/
theorem exists_positive_measure_negative_samples [MeasurableSpace E] [MeasurableSpace P]
    (A : Finset E) (hA : A.Nonempty) (H : Set E) (hH : Convex ℝ H)
    (hAH : (A : Set E) ⊆ H) (F : AnchoredBody A H × P → ℝ) (hF : Continuous F)
    (ν : ∀ n, Measure ((Fin n → H) × P)) [∀ n, (ν n).IsOpenPosMeasure]
    {K : AnchoredBody A H} {p : P} (hbad : F (K,p) < 0) :
    ∃ n, 0 < ν n {q | F (anchoredHull A hA H hH hAH q.1,q.2) < 0} := by
  obtain ⟨n,x,hx⟩ := exists_negative_sample A hA H hH hAH F hF hbad
  exact ⟨n,(isOpen_negative_samples A hA H hH hAH n F hF).measure_pos (ν n)
    ⟨(x,p),hx⟩⟩

end Parameter

end Plank.FiniteHullSampling
