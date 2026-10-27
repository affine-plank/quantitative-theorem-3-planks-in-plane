/- Construct the ABC chart from the strict cyclic vertex-order condition. -/
module
public import Plank.Proofs.Quant.TriangleNullableCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicNormalization
open Set MeasureTheory Proofs.Basic Proofs.Transport
open TriangleCommonExtremeCatalogue TriangleOrientationExhaustion
open scoped BigOperators

/-- Choose the positive first coordinate, without changing the physical band. -/
def facePositive (p : Plank) : Plank := by
  classical
  exact if 0 < p.u.1 then p else flipP p

theorem facePositive_set (p : Plank) : (facePositive p).set=p.set := by
  unfold facePositive
  split_ifs
  · rfl
  · exact flip_set p

theorem facePositive_width (T : Triangle) (p : Plank) :
    (facePositive p).relWidth T=p.relWidth T := by
  unfold facePositive
  split_ifs
  · rfl
  · exact flip_width T p

theorem facePositive_ab (p : Plank)
    (h : (0 < p.u.2 ∧ p.u.2 < p.u.1) ∨ (p.u.1 < p.u.2 ∧ p.u.2 < 0)) :
    0 < (facePositive p).u.2 ∧ (facePositive p).u.2 < (facePositive p).u.1 := by
  rcases h with h | h
  · rw [facePositive,if_pos (h.1.trans h.2)]
    exact h
  · rw [facePositive,if_neg (not_lt.mpr (h.1.trans h.2).le)]
    change 0 < -p.u.2 ∧ -p.u.2 < -p.u.1
    constructor <;> linarith only [h.1,h.2]

theorem facePositive_ac (p : Plank)
    (h : (0 < p.u.1 ∧ p.u.1 < p.u.2) ∨ (p.u.2 < p.u.1 ∧ p.u.1 < 0)) :
    0 < (facePositive p).u.1 ∧ (facePositive p).u.1 < (facePositive p).u.2 := by
  rcases h with h | h
  · rw [facePositive,if_pos h.1]
    exact h
  · rw [facePositive,if_neg (not_lt.mpr h.2.le)]
    change 0 < -p.u.1 ∧ -p.u.1 < -p.u.2
    constructor <;> linarith only [h.1,h.2]

theorem facePositive_bc (p : Plank)
    (h : (0 < p.u.1 ∧ p.u.2 < 0) ∨ (p.u.1 < 0 ∧ 0 < p.u.2)) :
    0 < (facePositive p).u.1 ∧ (facePositive p).u.2 < 0 := by
  rcases h with h | h
  · rw [facePositive,if_pos h.1]
    exact h
  · rw [facePositive,if_neg (not_lt.mpr h.1.le)]
    change 0 < -p.u.1 ∧ -p.u.2 < 0
    constructor <;> linarith only [h.1,h.2]

/-- Rescale by the actual directional span of the standard triangle. -/
def unitSpan (p : Plank) : Plank :=
  scaleP (stdTriangle.width p.u)⁻¹ (inv_pos.mpr (width_pos stdTriangle p.u_ne_zero)) p

theorem unitSpan_set (p : Plank) : (unitSpan p).set=p.set :=
  TriangleMixedTransport.scale_set _ _ _

theorem unitSpan_width (p : Plank) : (unitSpan p).relWidth stdTriangle=p.relWidth stdTriangle :=
  TriangleMixedTransport.scale_width _ _ _ _

theorem unitSpan_ab (p : Plank) (h : 0 < p.u.2 ∧ p.u.2 < p.u.1) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ (unitSpan p).u=(1,b) := by
  have hx : 0 < p.u.1 := h.1.trans h.2
  have hw : stdTriangle.width p.u=p.u.1 := by
    rw [stdTriangle_width_eq,max_eq_left h.2.le,max_eq_right hx.le,
      min_eq_right h.2.le,min_eq_left h.1.le,sub_zero]
  refine ⟨p.u.2/p.u.1,div_pos h.1 hx,(div_lt_one hx).mpr h.2,?_⟩
  change (stdTriangle.width p.u)⁻¹ • p.u = _
  rw [hw]
  apply Prod.ext <;> simp [div_eq_mul_inv,mul_comm,hx.ne']

theorem unitSpan_ac (p : Plank) (h : 0 < p.u.1 ∧ p.u.1 < p.u.2) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ (unitSpan p).u=(a,1) := by
  have hy : 0 < p.u.2 := h.1.trans h.2
  have hw : stdTriangle.width p.u=p.u.2 := by
    rw [stdTriangle_width_eq,max_eq_right h.2.le,max_eq_right hy.le,
      min_eq_left h.2.le,min_eq_left h.1.le,sub_zero]
  refine ⟨p.u.1/p.u.2,div_pos h.1 hy,(div_lt_one hy).mpr h.2,?_⟩
  change (stdTriangle.width p.u)⁻¹ • p.u = _
  rw [hw]
  apply Prod.ext <;> simp [div_eq_mul_inv,mul_comm,hy.ne']

theorem unitSpan_bc (p : Plank) (h : 0 < p.u.1 ∧ p.u.2 < 0) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ (unitSpan p).u=(c,c-1) := by
  have hd : 0 < p.u.1-p.u.2 := by linarith only [h.1,h.2]
  have hxy : p.u.2 ≤ p.u.1 := by linarith only [h.1,h.2]
  have hw : stdTriangle.width p.u=p.u.1-p.u.2 := by
    rw [stdTriangle_width_eq,max_eq_left hxy,max_eq_right h.1.le,
      min_eq_right hxy,min_eq_right h.2.le]
  refine ⟨p.u.1/(p.u.1-p.u.2),div_pos h.1 hd,(div_lt_one hd).mpr ?_,?_⟩
  · linarith only [h.2]
  · change (stdTriangle.width p.u)⁻¹ • p.u = _
    rw [hw]
    apply Prod.ext
    · simp [div_eq_mul_inv,mul_comm]
    · change (p.u.1-p.u.2)⁻¹*p.u.2=p.u.1/(p.u.1-p.u.2)-1
      field_simp [hd.ne']
      ring

def normalized (p : Plank) : Plank := unitSpan (facePositive p)

theorem normalized_set (p : Plank) : (normalized p).set=p.set := by
  rw [normalized,unitSpan_set,facePositive_set]

theorem normalized_width (p : Plank) : (normalized p).relWidth stdTriangle=p.relWidth stdTriangle := by
  rw [normalized,unitSpan_width,facePositive_width]

theorem middle_c_ab (T : Triangle) (p : Plank) (h : AtMiddle (atVertex T 2) p) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ (normalized (pullbackPlank T p)).u=(1,b) := by
  apply unitSpan_ab _ (facePositive_ab _ ?_)
  dsimp [AtMiddle,atVertex,rotate] at h
  simp only [pullbackPlank,dot_sub_right]
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · left
    constructor <;> linarith only [ha,hb]
  · right
    constructor <;> linarith only [ha,hb]

theorem middle_b_ac (T : Triangle) (p : Plank) (h : AtMiddle (atVertex T 1) p) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ (normalized (pullbackPlank T p)).u=(a,1) := by
  apply unitSpan_ac _ (facePositive_ac _ ?_)
  dsimp [AtMiddle,atVertex,rotate] at h
  simp only [pullbackPlank,dot_sub_right]
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · right
    constructor <;> linarith only [ha,hb]
  · left
    constructor <;> linarith only [ha,hb]

theorem middle_a_bc (T : Triangle) (p : Plank) (h : AtMiddle (atVertex T 0) p) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ (normalized (pullbackPlank T p)).u=(c,c-1) := by
  apply unitSpan_bc _ (facePositive_bc _ ?_)
  dsimp [AtMiddle,atVertex,rotate] at h
  simp only [pullbackPlank,dot_sub_right]
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · right
    constructor <;> linarith only [ha,hb]
  · left
    constructor <;> linarith only [ha,hb]

/-- The pullback, permutation and band normalization are explicit. -/
def chartConfig (T : Triangle) (p : Fin 3 → Plank) (σ : Equiv.Perm (Fin 3)) : Config :=
  ⟨fun i => normalized (pullbackPlank T (p (σ i)))⟩

theorem chartConfig_set (T : Triangle) (p : Fin 3 → Plank) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ((chartConfig T p σ).plank i).set=(pullbackPlank T (p (σ i))).set := normalized_set _

theorem chartConfig_width (T : Triangle) (p : Fin 3 → Plank) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (chartConfig T p σ).relW i=(p (σ i)).relWidth T :=
  (normalized_width _).trans (relWidth_pullback _ _)

theorem chartConfig_sum (T : Triangle) (p : Fin 3 → Plank) (σ : Equiv.Perm (Fin 3)) :
    (chartConfig T p σ).sumRelW=∑ i, (p i).relWidth T := by
  simp only [Config.sumRelW,chartConfig_width]
  exact TriangleNullableCatalogue.sum_permute T p σ

theorem chartConfig_gap (T : Triangle) (p : Fin 3 → Plank) (σ : Equiv.Perm (Fin 3)) :
    (volume (T.set \ ⋃ i, (p i).set)).toReal=
      |det3 T.A T.B T.C| * (chartConfig T p σ).gapArea := by
  have hu : (⋃ i, (p (σ i)).set)=⋃ i, (p i).set := by
    ext z
    constructor
    · intro h
      obtain ⟨i,hi⟩ := mem_iUnion.mp h
      exact mem_iUnion.mpr ⟨σ i,hi⟩
    · intro h
      obtain ⟨j,hj⟩ := mem_iUnion.mp h
      obtain ⟨i,rfl⟩ := σ.surjective j
      exact mem_iUnion.mpr ⟨i,hj⟩
  rw [← hu,AffineTransport.gapArea_transport]
  congr 1
  simp only [Config.gapArea,Config.uncovered,AffineTransport.pullbackConfig,
    chartConfig,normalized_set]

theorem chartConfig_equality (T : Triangle) (p : Fin 3 → Plank) (σ : Equiv.Perm (Fin 3))
    (hR : (∑ i, (p i).relWidth T) < 1) :
    TriangleNullableCatalogue.Equality T p ↔ TriangleEqualityReductions.Equality (chartConfig T p σ) := by
  have hd : 0 < (chartConfig T p σ).deficit := by
    rw [Config.deficit,chartConfig_sum]
    exact sub_pos.mpr hR
  unfold TriangleNullableCatalogue.Equality TriangleEqualityReductions.Equality
  rw [chartConfig_gap T p σ,AffineTransport.area_triangle,max_eq_right hd.le,
    Config.deficit,chartConfig_sum]
  rw [show (1-∑ i, (p i).relWidth T)^2*(|det3 T.A T.B T.C| * (1/2)) =
    |det3 T.A T.B T.C| * ((1-∑ i, (p i).relWidth T)^2*(1/2)) by ring]
  exact ⟨mul_left_cancel₀ (abs_ne_zero.mpr (det3_ne_zero T)),
    fun h => congrArg (fun x => |det3 T.A T.B T.C| * x) h⟩

/-- Every strict cyclic triple has the ABC normal directions. The
parameters, permutation and physical band chart are constructed from
the vertex orders; no clipping or position hypothesis is imposed. -/
theorem exists_abc (T : Triangle) (p : Fin 3 → Plank) (h : StrictCyclic T p) :
    ∃ (σ : Equiv.Perm (Fin 3)) (b a c : ℝ),
      (0 < b ∧ b < 1) ∧ (0 < a ∧ a < 1) ∧ (0 < c ∧ c < 1) ∧
      ((chartConfig T p σ).plank 0).u=(1,b) ∧
      ((chartConfig T p σ).plank 1).u=(a,1) ∧
      ((chartConfig T p σ).plank 2).u=(c,c-1) := by
  obtain ⟨τ,hτ⟩ := h
  obtain ⟨b,hb,hb',hu0⟩ := middle_c_ab T (p (τ 2)) (hτ 2)
  obtain ⟨a,ha,ha',hu1⟩ := middle_b_ac T (p (τ 1)) (hτ 1)
  obtain ⟨c,hc,hc',hu2⟩ := middle_a_bc T (p (τ 0)) (hτ 0)
  refine ⟨(Equiv.swap 0 2).trans τ,b,a,c,⟨hb,hb'⟩,⟨ha,ha'⟩,⟨hc,hc'⟩,?_,?_,?_⟩
  all_goals simp only [chartConfig,Equiv.trans_apply,Equiv.swap_apply_def]
  all_goals norm_num
  exacts [hu0,hu1,hu2]

private theorem plank_ext (p q : Plank) (hu : p.u=q.u)
    (hl : p.lo=q.lo) (hh : p.hi=q.hi) : p=q := by
  cases p
  cases q
  cases hu
  cases hl
  cases hh
  rfl

/-- The normal-direction description is the existing ABC configuration,
with exactly the normalized band endpoints. -/
theorem config_eq_abc (C : Config) (b a c : ℝ)
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (h0 : (C.plank 0).u=(1,b)) (h1 : (C.plank 1).u=(a,1))
    (h2 : (C.plank 2).u=(c,c-1)) :
    C=abcConfig b a c hb ha hc (fun i => (C.plank i).lo)
      (fun i => (C.plank i).hi) (fun i => (C.plank i).lo_le_hi) := by
  cases C with
  | mk p =>
    congr 1
    funext i
    fin_cases i
    all_goals apply plank_ext
    all_goals first | exact h0 | exact h1 | exact h2 | rfl

theorem exists_abc_config (T : Triangle) (p : Fin 3 → Plank) (h : StrictCyclic T p) :
    ∃ (σ : Equiv.Perm (Fin 3)) (b a c : ℝ)
      (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
      (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i),
      chartConfig T p σ=abcConfig b a c hb ha hc lo hi hle := by
  obtain ⟨σ,b,a,c,hb,ha,hc,h0,h1,h2⟩ := exists_abc T p h
  refine ⟨σ,b,a,c,hb,ha,hc,fun i => ((chartConfig T p σ).plank i).lo,
    fun i => ((chartConfig T p σ).plank i).hi,
    fun i => ((chartConfig T p σ).plank i).lo_le_hi,?_⟩
  exact config_eq_abc _ _ _ _ hb ha hc h0 h1 h2

/-- Every remaining subcritical cyclic equality is an actual positive-width
ABC equality, preserving each whole pulled-back band and its original
relative width. The original triangle need not already be normalized. -/
theorem cyclic_equality_normal_form (T : Triangle) (p : Fin 3 → Plank)
    (h : StrictCyclic T p) (hp : ∀ i, 0 < (p i).relWidth T)
    (hR : (∑ i, (p i).relWidth T) < 1) (he : TriangleNullableCatalogue.Equality T p) :
    ∃ (σ : Equiv.Perm (Fin 3)) (b a c : ℝ)
      (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
      (lo hi : Fin 3 → ℝ) (hle : ∀ i, lo i ≤ hi i),
      let C := abcConfig b a c hb ha hc lo hi hle
      (∀ i, (C.plank i).set=(pullbackPlank T (p (σ i))).set) ∧
      (∀ i, C.relW i=(p (σ i)).relWidth T) ∧
      (∀ i, 0 < C.relW i) ∧ TriangleEqualityReductions.Equality C := by
  obtain ⟨σ,b,a,c,hb,ha,hc,lo,hi,hle,hC⟩ := exists_abc_config T p h
  refine ⟨σ,b,a,c,hb,ha,hc,lo,hi,hle,?_⟩
  dsimp only
  rw [← hC]
  exact ⟨chartConfig_set T p σ,chartConfig_width T p σ,
    fun i => by rw [chartConfig_width]; exact hp (σ i),
    (chartConfig_equality T p σ hR).mp he⟩

end Quant.TriangleCyclicNormalization

/-- info: 'Quant.TriangleCyclicNormalization.exists_abc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicNormalization.exists_abc

/-- info: 'Quant.TriangleCyclicNormalization.chartConfig_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicNormalization.chartConfig_equality

/-- info: 'Quant.TriangleCyclicNormalization.cyclic_equality_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicNormalization.cyclic_equality_normal_form
