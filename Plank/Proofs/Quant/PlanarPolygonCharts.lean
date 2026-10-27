/- A finite affine comparison arrangement gives actual polygon area formulas. -/
module

public import Plank.Proofs.Quant.PlanarPolygonHalfplanes
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Choose

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarPolygonCharts

open Set MeasureTheory PlanarPolygonSlabs PlanarPolygonPartition PlanarPolygonHalfplanes

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A finite sum of products of affine functions, hence a polynomial of
degree at most two. The representation will also provide its derivatives. -/
structure QuadraticFormula (E : Type*) [AddCommGroup E] [Module ℝ E] where
  size : ℕ
  left : ℕ → E →ᵃ[ℝ] ℝ
  right : ℕ → E →ᵃ[ℝ] ℝ

def QuadraticFormula.eval (q : QuadraticFormula E) (x : E) : ℝ :=
  ∑ k ∈ Finset.range q.size, q.left k x*q.right k x

def QuadraticFormula.zero : QuadraticFormula E := ⟨0, fun _ => 0, fun _ => 0⟩

abbrev CutIndex (ι κ : Type*) := Bool ⊕ ((ι ⊕ κ) × (ι ⊕ κ))

/-- Candidate positions include both endpoints and every boundary-line
intersection. Parallel pairs harmlessly contribute the zero affine map. -/
def cut {ι κ : Type*} (a b : E →ᵃ[ℝ] ℝ)
    (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) : CutIndex ι κ → E →ᵃ[ℝ] ℝ
  | Sum.inl false => a
  | Sum.inl true => b
  | Sum.inr (p, q) => (Sum.elim ls us p-Sum.elim ls us q)⁻¹ •
      (Sum.elim lc uc q-Sum.elim lc uc p)

abbrev WallIndex (ι κ : Type*) :=
  (CutIndex ι κ × CutIndex ι κ) ⊕ (CutIndex ι κ × ((ι ⊕ κ) × (ι ⊕ κ)))

/-- All ordering tests needed for the partition and its active facets are
affine functions of the parameters. Their zero sets are the chart walls. -/
def wall {ι κ : Type*} (a b : E →ᵃ[ℝ] ℝ)
    (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) : WallIndex ι κ → E →ᵃ[ℝ] ℝ
  | Sum.inl (p, q) => cut a b ls lc us uc p-cut a b ls lc us uc q
  | Sum.inr (r, p, q) =>
      (Sum.elim ls us p-Sum.elim ls us q) • cut a b ls lc us uc r +
        (Sum.elim lc uc p-Sum.elim lc uc q)

/-- Record every weak comparison. Both orders are included in the wall
family, so this also distinguishes equality from either strict inequality. -/
def profile {ι κ : Type*} (a b : E →ᵃ[ℝ] ℝ)
    (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) (x : E) : WallIndex ι κ → Bool := by
  classical
  exact fun w => decide (wall a b ls lc us uc w x ≤ 0)

theorem cut_le_iff_of_profile_eq {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (h : profile a b ls lc us uc x = profile a b ls lc us uc y)
    (p q : CutIndex ι κ) :
    cut a b ls lc us uc p x ≤ cut a b ls lc us uc q x ↔
      cut a b ls lc us uc p y ≤ cut a b ls lc us uc q y := by
  have heq := congrFun h (Sum.inl (p, q))
  simpa only [profile, wall, AffineMap.coe_sub, Pi.sub_apply, sub_nonpos,
    decide_eq_decide] using heq

theorem graph_le_iff_of_profile_eq {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (h : profile a b ls lc us uc x = profile a b ls lc us uc y)
    (r : CutIndex ι κ) (p q : ι ⊕ κ) :
    Sum.elim ls us p*cut a b ls lc us uc r x+Sum.elim lc uc p x ≤
      Sum.elim ls us q*cut a b ls lc us uc r x+Sum.elim lc uc q x ↔
    Sum.elim ls us p*cut a b ls lc us uc r y+Sum.elim lc uc p y ≤
      Sum.elim ls us q*cut a b ls lc us uc r y+Sum.elim lc uc q y := by
  have heq : wall a b ls lc us uc (Sum.inr (r, p, q)) x ≤ 0 ↔
      wall a b ls lc us uc (Sum.inr (r, p, q)) y ≤ 0 :=
    decide_eq_decide.mp (congrFun h (Sum.inr (r, p, q)))
  change ((Sum.elim ls us p-Sum.elim ls us q)*cut a b ls lc us uc r x+
      (Sum.elim lc uc p x-Sum.elim lc uc q x) ≤ 0 ↔
    (Sum.elim ls us p-Sum.elim ls us q)*cut a b ls lc us uc r y+
      (Sum.elim lc uc p y-Sum.elim lc uc q y) ≤ 0) at heq
  constructor <;> intro hle
  · have hnonpos : (Sum.elim ls us p-Sum.elim ls us q)*cut a b ls lc us uc r x+
        (Sum.elim lc uc p x-Sum.elim lc uc q x) ≤ 0 := by nlinarith only [hle]
    have := heq.mp hnonpos
    nlinarith only [this]
  · have hnonpos : (Sum.elim ls us p-Sum.elim ls us q)*cut a b ls lc us uc r y+
        (Sum.elim lc uc p y-Sum.elim lc uc q y) ≤ 0 := by nlinarith only [hle]
    have := heq.mpr hnonpos
    nlinarith only [this]

/-- Every static cut used by the constructed partition is the value of one
of the fixed finite affine candidate maps. -/
theorem exists_cut_index {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) (x : E) (r : ℝ)
    (hr : r ∈ insert (a x) (insert (b x)
      (crossingSet ls (fun i => lc i x) us (fun j => uc j x)))) :
    ∃ p : CutIndex ι κ, cut a b ls lc us uc p x = r := by
  classical
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact ⟨Sum.inl false, rfl⟩
  rcases Finset.mem_insert.mp hr with rfl | hr
  · exact ⟨Sum.inl true, rfl⟩
  obtain ⟨⟨p, q⟩, _, hr⟩ := Finset.mem_image.mp hr
  refine ⟨Sum.inr (p, q), ?_⟩
  cases p <;> cases q <;>
    simpa only [cut, AffineMap.coe_smul, AffineMap.coe_sub, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, div_eq_mul_inv, mul_comm, Sum.elim_inl, Sum.elim_inr] using hr

theorem cut_eq_iff_of_profile_eq {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (h : profile a b ls lc us uc x = profile a b ls lc us uc y)
    (p q : CutIndex ι κ) :
    cut a b ls lc us uc p x = cut a b ls lc us uc q x ↔
      cut a b ls lc us uc p y = cut a b ls lc us uc q y := by
  rw [le_antisymm_iff, le_antisymm_iff,
    cut_le_iff_of_profile_eq a b ls lc us uc h p q,
    cut_le_iff_of_profile_eq a b ls lc us uc h q p]

/-- Preserve the weak comparisons holding at the reference point. This
allows strict inequalities to become equalities at a chart boundary. -/
def Compatible {τ : Type*} (F : τ → E →ᵃ[ℝ] ℝ) (x y : E) : Prop :=
  ∀ w, F w x ≤ 0 → F w y ≤ 0

theorem compatible_of_profile_eq {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (h : profile a b ls lc us uc x = profile a b ls lc us uc y) :
    Compatible (wall a b ls lc us uc) x y := by
  intro w hw
  exact (decide_eq_decide.mp (congrFun h w)).mp hw

theorem cut_le_of_compatible {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (h : Compatible (wall a b ls lc us uc) x y) (p q : CutIndex ι κ)
    (hle : cut a b ls lc us uc p x ≤ cut a b ls lc us uc q x) :
    cut a b ls lc us uc p y ≤ cut a b ls lc us uc q y :=
  sub_nonpos.mp (h (Sum.inl (p, q)) (sub_nonpos.mpr hle))

theorem cut_eq_of_compatible {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (h : Compatible (wall a b ls lc us uc) x y) (p q : CutIndex ι κ)
    (heq : cut a b ls lc us uc p x = cut a b ls lc us uc q x) :
    cut a b ls lc us uc p y = cut a b ls lc us uc q y :=
  le_antisymm (cut_le_of_compatible a b ls lc us uc h p q heq.le)
    (cut_le_of_compatible a b ls lc us uc h q p heq.ge)

theorem graph_le_of_compatible {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (h : Compatible (wall a b ls lc us uc) x y) (r : CutIndex ι κ) (p q : ι ⊕ κ)
    (hle : Sum.elim ls us p*cut a b ls lc us uc r x+Sum.elim lc uc p x ≤
      Sum.elim ls us q*cut a b ls lc us uc r x+Sum.elim lc uc q x) :
    Sum.elim ls us p*cut a b ls lc us uc r y+Sum.elim lc uc p y ≤
      Sum.elim ls us q*cut a b ls lc us uc r y+Sum.elim lc uc q y := by
  have h0 : wall a b ls lc us uc (Sum.inr (r, p, q)) x ≤ 0 := by
    change (Sum.elim ls us p-Sum.elim ls us q)*cut a b ls lc us uc r x+
      (Sum.elim lc uc p x-Sum.elim lc uc q x) ≤ 0
    nlinarith only [hle]
  have h1 := h (Sum.inr (r, p, q)) h0
  change (Sum.elim ls us p-Sum.elim ls us q)*cut a b ls lc us uc r y+
    (Sum.elim lc uc p y-Sum.elim lc uc q y) ≤ 0 at h1
  nlinarith only [h1]

/-- Weak comparisons preserve active facets, including at chart boundaries. -/
theorem activeFacets_of_compatible {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) {x y : E}
    (h : Compatible (wall a b ls lc us uc) x y)
    (p q : CutIndex ι κ) (i : ι) (j : κ)
    (hf : ActiveFacets (cut a b ls lc us uc p x) (cut a b ls lc us uc q x)
      ls (fun k => lc k x) us (fun k => uc k x) i j) :
    ActiveFacets (cut a b ls lc us uc p y) (cut a b ls lc us uc q y)
      ls (fun k => lc k y) us (fun k => uc k y) i j := by
  refine ⟨cut_le_of_compatible a b ls lc us uc h p q hf.ordered,
    fun k => ⟨?_, ?_⟩, fun k => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact graph_le_of_compatible a b ls lc us uc h p (Sum.inl k) (Sum.inl i)
      (hf.lower k).1
  · exact graph_le_of_compatible a b ls lc us uc h q (Sum.inl k) (Sum.inl i)
      (hf.lower k).2
  · exact graph_le_of_compatible a b ls lc us uc h p (Sum.inr j) (Sum.inr k)
      (hf.upper k).1
  · exact graph_le_of_compatible a b ls lc us uc h q (Sum.inr j) (Sum.inr k)
      (hf.upper k).2
  · exact graph_le_of_compatible a b ls lc us uc h p (Sum.inl i) (Sum.inr j)
      hf.left_height
  · exact graph_le_of_compatible a b ls lc us uc h q (Sum.inl i) (Sum.inr j)
      hf.right_height

/-- The static partition at one parameter point extends to an actual area
formula throughout its entire affine comparison region. All combinatorial
certificates are constructed by the previous geometric lemmas. -/
theorem exists_formula_on_compatible_of_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) (x : E) (hab : a x ≤ b x) :
    ∃ q : QuadraticFormula E, ∀ y : E,
      Compatible (wall a b ls lc us uc) x y →
      (volume (closedSlab (a y) (b y) ls (fun i => lc i y) us (fun j => uc j y))).toReal =
        q.eval y := by
  classical
  obtain ⟨n, _, r, hmono, hr0, hrn, hmem, i, j, hcert⟩ :=
    exists_polygon_slab_certificates hab ls (fun i => lc i x) us (fun j => uc j x)
  choose index hindex using fun k => exists_cut_index a b ls lc us uc x (r k) (hmem k)
  let s (k : ℕ) : E →ᵃ[ℝ] ℝ := cut a b ls lc us uc (index k)
  have hs (k : ℕ) : s k x = r k := hindex k
  have hex (k : ℕ) : ∃ L U : E →ᵃ[ℝ] ℝ, k < n → ∀ y : E,
      Compatible (wall a b ls lc us uc) x y →
      volume (slab (s k y) (s (k+1) y) ls (fun i => lc i y) us (fun j => uc j y)) =
        ENNReal.ofReal (L y*U y) ∧ 0 ≤ L y*U y := by
    by_cases hk : k < n
    · rcases hcert k hk with ha | he
      · refine ⟨s (k+1)-s k,
          (1/2 : ℝ) • ((us (j k)-ls (i k)) • (s k+s (k+1)) +
            (2 : ℝ) • (uc (j k)-lc (i k))), fun _ y hy => ?_⟩
        have ha' : ActiveFacets (s k x) (s (k+1) x)
            ls (fun k => lc k x) us (fun k => uc k x) (i k) (j k) := by
          simpa only [hs] using ha
        have hf := activeFacets_of_compatible a b ls lc us uc hy
          (index k) (index (k+1)) (i k) (j k) ha'
        have hval : (s (k+1)-s k) y *
            ((1/2 : ℝ) • ((us (j k)-ls (i k)) • (s k+s (k+1)) +
              (2 : ℝ) • (uc (j k)-lc (i k)))) y =
            (s (k+1) y-s k y)*((us (j k)-ls (i k))*(s k y+s (k+1) y)+
              2*(uc (j k) y-lc (i k) y))/2 := by
          change (s (k+1) y-s k y)*
            ((1/2)*((us (j k)-ls (i k))*(s k y+s (k+1) y)+
              2*(uc (j k) y-lc (i k) y))) = _
          ring
        rw [hval]
        exact ⟨measure_slab_of_active hf.ordered ls _ us _ (i k) (j k)
          hf.lower hf.upper hf.left_height hf.right_height,
          trapezoid_nonneg hf.ordered hf.left_height hf.right_height⟩
      · refine ⟨0, 0, fun _ y hy => ?_⟩
        have he0 : us (j k)*s k x+uc (j k) x ≤ ls (i k)*s k x+lc (i k) x := by
          simpa only [hs] using he.1
        have he1 : us (j k)*s (k+1) x+uc (j k) x ≤
            ls (i k)*s (k+1) x+lc (i k) x := by simpa only [hs] using he.2
        have he0' := graph_le_of_compatible a b ls lc us uc hy
          (index k) (Sum.inr (j k)) (Sum.inl (i k)) he0
        have he1' := graph_le_of_compatible a b ls lc us uc hy
          (index (k+1)) (Sum.inr (j k)) (Sum.inl (i k)) he1
        have hz := measure_slab_zero ls (fun i => lc i y) us (fun j => uc j y)
          (i k) (j k) he0' he1'
        simpa only [AffineMap.coe_zero, Pi.zero_apply, zero_mul, ENNReal.ofReal_zero] using
          And.intro hz (le_refl (0 : ℝ))
    · exact ⟨0, 0, fun h => (hk h).elim⟩
  choose L U hpieces using hex
  refine ⟨⟨n, L, U⟩, fun y hy => ?_⟩
  have hmonoy : Monotone (fun k => s k y) := by
    intro k l hkl
    apply cut_le_of_compatible a b ls lc us uc hy (index k) (index l)
    simpa only [hindex] using hmono hkl
  have hzero : s 0 y = a y :=
    cut_eq_of_compatible a b ls lc us uc hy (index 0) (Sum.inl false)
      ((hindex 0).trans hr0)
  have hlast : s n y = b y :=
    cut_eq_of_compatible a b ls lc us uc hy (index n) (Sum.inl true)
      ((hindex n).trans hrn)
  have hp (k : ℕ) (hk : k ∈ Finset.range n) := hpieces k (Finset.mem_range.mp hk) y hy
  rw [measure_closedSlab, measure_coordinateSlab, ← hzero, ← hlast,
    measure_slab_sum _ hmonoy, ENNReal.toReal_sum
      (fun k hk => by rw [(hp k hk).1]; exact ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [(hp k hk).1, ENNReal.toReal_ofReal (hp k hk).2]

/-- Reversed horizontal endpoints give the empty set throughout their
profile region, so no domain restriction is needed in the finite atlas. -/
theorem exists_formula_on_compatible {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) (x : E) :
    ∃ q : QuadraticFormula E, ∀ y : E,
      Compatible (wall a b ls lc us uc) x y →
      (volume (closedSlab (a y) (b y) ls (fun i => lc i y) us (fun j => uc j y))).toReal =
        q.eval y := by
  by_cases hab : a x ≤ b x
  · exact exists_formula_on_compatible_of_le a b ls lc us uc x hab
  · refine ⟨QuadraticFormula.zero, fun y hy => ?_⟩
    have hbad : b y ≤ a y := cut_le_of_compatible a b ls lc us uc hy
      (Sum.inl true) (Sum.inl false) (le_of_not_ge hab)
    have hempty : coordinateSlab (a y) (b y) ls (fun i => lc i y) us (fun j => uc j y) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact (not_lt_of_ge (hp.1.2.trans hbad)) hp.1.1
    rw [measure_closedSlab, hempty]
    simp [QuadraticFormula.zero, QuadraticFormula.eval]

theorem exists_formula_on_profile {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) (x : E) :
    ∃ q : QuadraticFormula E, ∀ y : E,
      profile a b ls lc us uc x = profile a b ls lc us uc y →
      (volume (closedSlab (a y) (b y) ls (fun i => lc i y) us (fun j => uc j y))).toReal =
        q.eval y := by
  obtain ⟨q, hq⟩ := exists_formula_on_compatible a b ls lc us uc x
  exact ⟨q, fun y hy => hq y (compatible_of_profile_eq a b ls lc us uc hy)⟩

/-- A finite family of actual area polynomials, indexed by the sign regions
of explicitly constructed affine walls. This is uniform over the full
parameter space; the input supplies no charts or area identities. -/
theorem exists_finite_area_formulas {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) :
    ∃ q : (WallIndex ι κ → Bool) → QuadraticFormula E, ∀ x : E,
      (volume (closedSlab (a x) (b x) ls (fun i => lc i x) us (fun j => uc j x))).toReal =
        (q (profile a b ls lc us uc x)).eval x := by
  classical
  have hex (s : WallIndex ι κ → Bool) : ∃ q : QuadraticFormula E, ∀ x : E,
      profile a b ls lc us uc x = s →
      (volume (closedSlab (a x) (b x) ls (fun i => lc i x) us (fun j => uc j x))).toReal =
        q.eval x := by
    by_cases hs : ∃ x, profile a b ls lc us uc x = s
    · obtain ⟨x, hx⟩ := hs
      obtain ⟨q, hq⟩ := exists_formula_on_profile a b ls lc us uc x
      exact ⟨q, fun y hy => hq y (hx.trans hy.symm)⟩
    · exact ⟨QuadraticFormula.zero, fun x hx => (hs ⟨x, hx⟩).elim⟩
  choose q hq using hex
  exact ⟨q, fun x => hq _ x rfl⟩

theorem affine_eval_line (f : E →ᵃ[ℝ] ℝ) (x z : E) (t : ℝ) :
    f (x+t • z) = f x+t*f.linear z := by
  have h := f.map_vadd x (t • z)
  simpa only [vadd_eq_add, map_smul, smul_eq_mul, add_comm] using h

/-- The product representation yields an exact quadratic on every affine
parameter line, with its coefficients constructed from the affine factors. -/
theorem QuadraticFormula.eval_line (q : QuadraticFormula E) (x z : E) :
    ∃ A g H : ℝ, ∀ t : ℝ, q.eval (x+t • z) = A+g*t+(H/2)*t^2 := by
  let A (k : ℕ) := q.left k x*q.right k x
  let g (k : ℕ) := (q.left k).linear z*q.right k x+q.left k x*(q.right k).linear z
  let H (k : ℕ) := 2*(q.left k).linear z*(q.right k).linear z
  refine ⟨∑ k ∈ Finset.range q.size, A k, ∑ k ∈ Finset.range q.size, g k,
    ∑ k ∈ Finset.range q.size, H k, fun t => ?_⟩
  calc
    q.eval (x+t • z) = ∑ k ∈ Finset.range q.size, (A k+g k*t+(H k/2)*t^2) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [affine_eval_line, affine_eval_line]
      dsimp [A, g, H]
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]

/-- Open sign regions for a family of affine walls. Identically zero walls
are retained as constant true comparisons and impose no geometric boundary. -/
def openRegion {τ : Type*} (F : τ → E →ᵃ[ℝ] ℝ) (s : τ → Bool) : Set E := by
  classical
  exact {x | ∀ w, if F w = 0 then s w = true else
    if s w = true then F w x < 0 else 0 < F w x}

theorem profile_eq_of_mem_openRegion {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) (s : WallIndex ι κ → Bool) {x : E}
    (hx : x ∈ openRegion (wall a b ls lc us uc) s) :
    profile a b ls lc us uc x = s := by
  classical
  funext w
  have hw := hx w
  change decide (wall a b ls lc us uc w x ≤ 0) = s w
  by_cases hz : wall a b ls lc us uc w = 0
  · simp only [hz, if_pos] at hw
    simp [hz, hw]
  · simp only [hz, if_false] at hw
    by_cases hs : s w = true
    · simp only [hs, if_pos] at hw
      simp [hs, hw.le]
    · simp only [hs] at hw
      have hs' : s w = false := Bool.eq_false_iff.mpr hs
      simp [hs', not_le.mpr hw]

/-- Every parameter away from the nontrivial walls belongs to the open
region corresponding to its comparison profile. -/
theorem mem_openRegion_of_off_walls {ι κ : Type*}
    (a b : E →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → E →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → E →ᵃ[ℝ] ℝ) (x : E)
    (hoff : ∀ w, wall a b ls lc us uc w ≠ 0 → wall a b ls lc us uc w x ≠ 0) :
    x ∈ openRegion (wall a b ls lc us uc) (profile a b ls lc us uc x) := by
  classical
  intro w
  by_cases hz : wall a b ls lc us uc w = 0
  · simp [hz, profile]
  · simp only [hz, if_false]
    by_cases hle : wall a b ls lc us uc w x ≤ 0
    · have hlt := lt_of_le_of_ne hle (hoff w hz)
      simpa only [profile, decide_eq_true hle, if_pos] using hlt
    · have hlt := lt_of_not_ge hle
      simpa only [profile, decide_eq_false hle, Bool.false_eq_true, if_false] using hlt

theorem convex_openRegion {τ : Type*} (F : τ → E →ᵃ[ℝ] ℝ) (s : τ → Bool) :
    Convex ℝ (openRegion F s) := by
  classical
  unfold openRegion
  simp only [Set.ofPred_forall]
  apply convex_iInter
  intro w
  by_cases hz : F w = 0
  · simp only [hz, if_pos]
    by_cases hs : s w = true
    · simpa [hs] using (convex_univ : Convex ℝ (univ : Set E))
    · simpa [hs] using (convex_empty : Convex ℝ (∅ : Set E))
  · simp only [hz, if_false]
    by_cases hs : s w = true
    · simp only [hs, if_pos]
      exact (convex_Iio (0 : ℝ)).affine_preimage (F w)
    · simp only [hs]
      exact (convex_Ioi (0 : ℝ)).affine_preimage (F w)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem continuous_affine (f : V →ᵃ[ℝ] ℝ) : Continuous f := by
  rw [f.decomp]
  exact f.linear.continuous_of_finiteDimensional.add continuous_const

theorem QuadraticFormula.continuous_eval (q : QuadraticFormula V) : Continuous q.eval := by
  unfold QuadraticFormula.eval
  exact continuous_finsetSum _ fun k _ =>
    (continuous_affine (q.left k)).mul (continuous_affine (q.right k))

/-- The geometric weak inequalities extend each actual area identity to
the closure of its profile region. This uses no prior continuity theorem
for the moving polygon's area. -/
theorem exists_closed_profile_formulas {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (a b : V →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → V →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → V →ᵃ[ℝ] ℝ) :
    ∃ q : (WallIndex ι κ → Bool) → QuadraticFormula V, ∀ s, ∀ y ∈
      closure {x | profile a b ls lc us uc x = s},
      (volume (closedSlab (a y) (b y) ls (fun i => lc i y) us (fun j => uc j y))).toReal =
        (q s).eval y := by
  classical
  have hex (s : WallIndex ι κ → Bool) : ∃ q : QuadraticFormula V, ∀ y ∈
      closure {x | profile a b ls lc us uc x = s},
      (volume (closedSlab (a y) (b y) ls (fun i => lc i y) us (fun j => uc j y))).toReal =
        q.eval y := by
    by_cases hs : ∃ x, profile a b ls lc us uc x = s
    · obtain ⟨x, hx⟩ := hs
      obtain ⟨q, hq⟩ := exists_formula_on_compatible a b ls lc us uc x
      refine ⟨q, fun y hy => hq y (fun w hw => ?_)⟩
      have hsub : {z | profile a b ls lc us uc z = s} ⊆
          {z | wall a b ls lc us uc w z ≤ 0} := by
        intro z hz
        exact compatible_of_profile_eq a b ls lc us uc (hx.trans hz.symm) w hw
      exact closure_minimal hsub
        (isClosed_le (continuous_affine (wall a b ls lc us uc w)) continuous_const) hy
    · refine ⟨QuadraticFormula.zero, fun y hy => ?_⟩
      have hempty : {x | profile a b ls lc us uc x = s} = ∅ :=
        eq_empty_iff_forall_notMem.mpr (fun x hx => hs ⟨x, hx⟩)
      simp only [hempty, closure_empty, mem_empty_iff_false] at hy
  choose q hq using hex
  exact ⟨q, hq⟩

/-- Finite closed-chart gluing proves continuity of the actual moving area. -/
theorem continuous_actual_area {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (a b : V →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → V →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → V →ᵃ[ℝ] ℝ) :
    Continuous (fun x =>
      (volume (closedSlab (a x) (b x) ls (fun i => lc i x) us (fun j => uc j x))).toReal) := by
  obtain ⟨q, hq⟩ := exists_closed_profile_formulas a b ls lc us uc
  apply continuous_iff_isClosed.mpr
  intro T hT
  have heq :
      {x | (volume (closedSlab (a x) (b x) ls (fun i => lc i x) us (fun j => uc j x))).toReal ∈ T} =
        ⋃ s, closure {x | profile a b ls lc us uc x = s} ∩ ((q s).eval ⁻¹' T) := by
    ext x
    constructor
    · intro hx
      apply mem_iUnion.mpr
      refine ⟨profile a b ls lc us uc x, subset_closure rfl, ?_⟩
      change (q (profile a b ls lc us uc x)).eval x ∈ T
      rwa [← hq _ x (subset_closure rfl)]
    · intro hx
      obtain ⟨s, hs, hval⟩ := mem_iUnion.mp hx
      change (volume (closedSlab (a x) (b x) ls (fun i => lc i x) us (fun j => uc j x))).toReal ∈ T
      rwa [hq s x hs]
  change IsClosed {x | (volume
    (closedSlab (a x) (b x) ls (fun i => lc i x) us (fun j => uc j x))).toReal ∈ T}
  rw [heq]
  exact isClosed_iUnion_of_finite fun s =>
    isClosed_closure.inter (hT.preimage (q s).continuous_eval)

theorem isOpen_openRegion {τ : Type*} [Finite τ]
    (F : τ → V →ᵃ[ℝ] ℝ) (s : τ → Bool) : IsOpen (openRegion F s) := by
  classical
  unfold openRegion
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro w
  by_cases hz : F w = 0
  · simp only [hz, if_pos]
    exact isOpen_const
  · simp only [hz, if_false]
    by_cases hs : s w = true
    · simp only [hs, if_pos]
      exact isOpen_lt (continuous_affine (F w)) continuous_const
    · simp only [hs]
      exact isOpen_lt continuous_const (continuous_affine (F w))

/-- The actual polygon area has a quadratic formula on every open region
of a constructed finite affine arrangement. Those regions cover every
parameter away from the finitely many nontrivial wall hyperplanes. -/
theorem exists_open_area_charts {ι κ : Type*} [Fintype ι] [Fintype κ]
    [Nonempty ι] [Nonempty κ]
    (a b : V →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → V →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → V →ᵃ[ℝ] ℝ) :
    ∃ q : (WallIndex ι κ → Bool) → QuadraticFormula V,
      (∀ s, IsOpen (openRegion (wall a b ls lc us uc) s) ∧
        Convex ℝ (openRegion (wall a b ls lc us uc) s) ∧
        ∀ x ∈ closure (openRegion (wall a b ls lc us uc) s),
          (volume (closedSlab (a x) (b x) ls (fun i => lc i x) us (fun j => uc j x))).toReal =
            (q s).eval x) ∧
      ∀ x, (∀ w, wall a b ls lc us uc w ≠ 0 → wall a b ls lc us uc w x ≠ 0) →
        x ∈ openRegion (wall a b ls lc us uc) (profile a b ls lc us uc x) := by
  obtain ⟨q, hq⟩ := exists_closed_profile_formulas a b ls lc us uc
  refine ⟨q, fun s => ⟨isOpen_openRegion _ _, convex_openRegion _ _, fun x hx => ?_⟩,
    mem_openRegion_of_off_walls a b ls lc us uc⟩
  exact hq s x (closure_mono (fun y hy => profile_eq_of_mem_openRegion a b ls lc us uc s hy) hx)

omit [FiniteDimensional ℝ V] in
/-- A nonzero affine equation has dense complement. The proof perturbs
along a line on which the actual affine value changes. -/
theorem dense_affine_ne_zero (f : V →ᵃ[ℝ] ℝ) (hf : f ≠ 0) :
    Dense {x : V | f x ≠ 0} := by
  intro x
  apply Metric.mem_closure_iff.mpr
  intro epsilon hepsilon
  by_cases hx : f x = 0
  · obtain ⟨z, hz⟩ : ∃ z : V, f z ≠ 0 := by
      by_contra hn
      apply hf
      ext z
      by_contra hz
      exact hn ⟨z, hz⟩
    let t := epsilon/(2*(‖z-x‖+1))
    have hden : 0 < 2*(‖z-x‖+1) := by positivity
    have ht : 0 < t := div_pos hepsilon hden
    have hmul : t*(2*(‖z-x‖+1)) = epsilon := div_mul_cancel₀ _ (ne_of_gt hden)
    have hlin : f.linear (z-x) = f z := by
      simpa only [vsub_eq_sub, hx, sub_zero] using f.linearMap_vsub z x
    refine ⟨x+t • (z-x), ?_, ?_⟩
    · change f (x+t • (z-x)) ≠ 0
      rw [affine_eval_line, hx, hlin, zero_add]
      exact mul_ne_zero (ne_of_gt ht) hz
    · have hdist : dist x (x+t • (z-x)) = t*‖z-x‖ := by
        rw [dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_pos ht]
      rw [hdist]
      nlinarith only [hmul, ht, norm_nonneg (z-x)]
  · exact ⟨x, hx, by simpa only [dist_self] using hepsilon⟩

/-- Finitely many nontrivial affine walls leave a dense set of parameters. -/
theorem dense_off_walls {τ : Type*} [Finite τ] (F : τ → V →ᵃ[ℝ] ℝ) :
    Dense {x : V | ∀ w, F w ≠ 0 → F w x ≠ 0} := by
  classical
  let _ := Fintype.ofFinite τ
  have hsingle (w : τ) : Dense {x : V | F w ≠ 0 → F w x ≠ 0} ∧
      IsOpen {x : V | F w ≠ 0 → F w x ≠ 0} := by
    by_cases hw : F w = 0
    · simp [hw]
    · have heq : {x : V | F w ≠ 0 → F w x ≠ 0} = {x : V | F w x ≠ 0} := by
        ext x
        exact ⟨fun h => h hw, fun h _ => h⟩
      rw [heq]
      exact ⟨dense_affine_ne_zero (F w) hw,
        (isClosed_eq (continuous_affine (F w)) continuous_const).isOpen_compl⟩
  have hfinite (s : Finset τ) : Dense {x : V | ∀ w ∈ s, F w ≠ 0 → F w x ≠ 0} := by
    induction s using Finset.induction with
    | empty => simp
    | @insert w s _ ih =>
      have heq : {x : V | ∀ v ∈ insert w s, F v ≠ 0 → F v x ≠ 0} =
          {x : V | F w ≠ 0 → F w x ≠ 0} ∩ {x : V | ∀ v ∈ s, F v ≠ 0 → F v x ≠ 0} := by
        ext x
        simp
      rw [heq]
      exact (hsingle w).1.inter_of_isOpen_left ih (hsingle w).2
  simpa using hfinite Finset.univ

/-- The closures of the finitely many open chart regions cover the entire
parameter space, including all multiple incidences and degenerate positions. -/
theorem closures_open_regions_cover {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : V →ᵃ[ℝ] ℝ) (ls : ι → ℝ) (lc : ι → V →ᵃ[ℝ] ℝ)
    (us : κ → ℝ) (uc : κ → V →ᵃ[ℝ] ℝ) :
    (⋃ s : WallIndex ι κ → Bool, closure (openRegion (wall a b ls lc us uc) s)) = univ := by
  have hd : Dense (⋃ s : WallIndex ι κ → Bool, openRegion (wall a b ls lc us uc) s) := by
    apply (dense_off_walls (wall a b ls lc us uc)).mono
    intro x hx
    exact mem_iUnion.mpr ⟨profile a b ls lc us uc x,
      mem_openRegion_of_off_walls a b ls lc us uc x hx⟩
  rw [← closure_iUnion_of_finite]
  exact hd.closure_eq

end Plank.PlanarPolygonCharts
