/- A compact domain of actual convex bodies and continuity of their support values.
No bound on the number of vertices, or even polygonality, is needed. -/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Closeds
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.CompactConvexBodyDomain

open Set TopologicalSpace

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace P]

omit [NormedSpace ℝ E] in
/-- Inclusion of two continuously varying nonempty compact sets is closed. -/
theorem isClosed_le {f g : P → NonemptyCompacts E}
    (hf : Continuous f) (hg : Continuous g) : IsClosed {p | f p ≤ g p} := by
  simpa only [sup_eq_right] using isClosed_eq (hf.sup hg) hg

def mix (a b : ℝ) (K : NonemptyCompacts E) : NonemptyCompacts E :=
  (K ×ˢ K).map (fun p : E × E => a • p.1 + b • p.2) (by fun_prop)

theorem continuous_mix (a b : ℝ) : Continuous (mix (E := E) a b) := by
  have hc : Continuous (fun p : E × E => a • p.1 + b • p.2) := by fun_prop
  exact hc.nonemptyCompacts_map.comp (NonemptyCompacts.continuous_prod.comp
      (continuous_id.prodMk continuous_id))

theorem convex_iff_mix_le (K : NonemptyCompacts E) :
    Convex ℝ (K : Set E) ↔
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → mix a b K ≤ K := by
  constructor
  · intro hc a b ha hb hab z hz
    obtain ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩ := hz
    exact hc hx hy ha hb hab
  · intro h x hx y hy a b ha hb hab
    exact h a b ha hb hab ⟨(x,y), ⟨hx,hy⟩, rfl⟩

theorem isClosed_convex :
    IsClosed {K : NonemptyCompacts E | Convex ℝ (K : Set E)} := by
  simp only [convex_iff_mix_le, Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_le (continuous_mix a b) continuous_id

/-- Convex bodies lying between fixed inner and outer sets form a compact
Hausdorff family whenever the outer set is compact. This works in any real
normed space; positivity and a normalization theorem are separate inputs. -/
theorem isCompact_sandwich (T H : Set E) (hH : IsCompact H) :
    IsCompact {K : NonemptyCompacts E |
      Convex ℝ (K : Set E) ∧ T ⊆ K ∧ (K : Set E) ⊆ H} := by
  have hinner : IsClosed {K : NonemptyCompacts E | T ⊆ K} := by
    have heq : {K : NonemptyCompacts E | T ⊆ K} =
        ⋂ x ∈ T, {K : NonemptyCompacts E | ({x} : NonemptyCompacts E) ≤ K} := by
      ext K
      simp only [mem_iInter, mem_ofPred_eq]
      change T ⊆ (K : Set E) ↔ ∀ x ∈ T, ({x} : Set E) ⊆ (K : Set E)
      simp only [singleton_subset_iff]
      rfl
    rw [heq]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_le continuous_const continuous_id
  apply (NonemptyCompacts.isCompact_subsets_of_isCompact hH).of_isClosed_subset
    (isClosed_convex.inter (hinner.inter
      (NonemptyCompacts.isClosed_subsets_of_isClosed hH.isClosed)))
  exact fun _ h => h.2.2

private theorem sup_le_sup_add_dist (K L : NonemptyCompacts ℝ) :
    sSup (K : Set ℝ) ≤ sSup (L : Set ℝ) + dist K L := by
  have hx := K.isCompact.sSup_mem K.nonempty
  obtain ⟨y,hy,hxy⟩ := L.isCompact.exists_infDist_eq_dist L.nonempty (sSup (K : Set ℝ))
  have hd : Metric.infDist (sSup (K : Set ℝ)) (L : Set ℝ) ≤ dist K L :=
    Metric.infDist_le_hausdorffDist_of_mem hx (edist_ne_top K L)
  have hys := le_csSup L.isCompact.bddAbove hy
  rw [hxy, Real.dist_eq] at hd
  have hab := (le_abs_self (sSup (K : Set ℝ)-y)).trans hd
  linarith only [hys,hab]

theorem lipschitz_sSup :
    LipschitzWith 1 (fun K : NonemptyCompacts ℝ => sSup (K : Set ℝ)) := by
  apply LipschitzWith.of_le_add
  intro K L
  simpa only [NNReal.coe_one, one_mul] using sup_le_sup_add_dist K L

omit [NormedSpace ℝ E] in
/-- Joint continuity of the true maximum when both the body and observable vary. -/
theorem continuous_support {K : P → NonemptyCompacts E} {f : P → E → ℝ}
    (hK : Continuous K) (hf : Continuous f.uncurry) :
    Continuous (fun p => sSup (f p '' (K p : Set E))) :=
  lipschitz_sSup.continuous.comp (hK.nonemptyCompacts_map' hf)

private theorem inf_le_inf_add_dist (K L : NonemptyCompacts ℝ) :
    sInf (K : Set ℝ) ≤ sInf (L : Set ℝ) + dist K L := by
  have hy := L.isCompact.sInf_mem L.nonempty
  obtain ⟨x,hx,hxy⟩ := K.isCompact.exists_infDist_eq_dist K.nonempty (sInf (L : Set ℝ))
  have hd : Metric.infDist (sInf (L : Set ℝ)) (K : Set ℝ) ≤ dist L K :=
    Metric.infDist_le_hausdorffDist_of_mem hy (edist_ne_top L K)
  have hxs := csInf_le K.isCompact.bddBelow hx
  rw [hxy, Real.dist_eq, dist_comm L K] at hd
  have hab := (neg_le_abs (sInf (L : Set ℝ)-x)).trans hd
  linarith only [hxs,hab]

theorem lipschitz_sInf :
    LipschitzWith 1 (fun K : NonemptyCompacts ℝ => sInf (K : Set ℝ)) := by
  apply LipschitzWith.of_le_add
  intro K L
  simpa only [NNReal.coe_one, one_mul] using inf_le_inf_add_dist K L

omit [NormedSpace ℝ E] in
/-- Joint continuity of the true minimum when both the body and observable vary. -/
theorem continuous_lower_support {K : P → NonemptyCompacts E} {f : P → E → ℝ}
    (hK : Continuous K) (hf : Continuous f.uncurry) :
    Continuous (fun p => sInf (f p '' (K p : Set E))) :=
  lipschitz_sInf.continuous.comp (hK.nonemptyCompacts_map' hf)

end Plank.CompactConvexBodyDomain
