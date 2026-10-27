/- Reflection and one-form shear transfer for any finite plank family
in every positive dimension. The strictly positive relation case is an
explicit hypothesis; this module does not prove the general plank bound. -/
module
public import Plank.Proofs.Quant.FiniteDimensionalNormalization

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.FiniteDimensionalRelationPerturbation

open Set MeasureTheory FiniteDimensionalCapWindowScaling
  FiniteDimensionalEndpointMajorants FiniteDimensionalFewCellScaling
  FiniteDimensionalMinimumCellRank FiniteDimensionalParameterDomain
  FiniteDimensionalNormalization
open scoped BigOperators

variable {d m : ℕ}

/-- The quantitative bound restricted to families with a strictly positive
affine relation on a fixed body. This is an input to the transfer theorems. -/
def PositiveRelationBound (K : Set (Point d)) (m : ℕ) : Prop :=
  ∀ (g : Fin m → (Point d) →ᵃ[ℝ] ℝ), (∀ i, 0 < Body.width K (g i)) →
  ∀ (c : Fin m → ℝ) (level : ℝ), (∀ i, 0 < c i) →
  (∀ x ∈ K, ∑ i, c i*g i x = level) →
  ∀ (p : Endpoints (Fin m)), (∀ i, p.1 i ≤ p.2 i) →
  (max 0 (1-budget K g p))^(d+1)*(volume K).toReal ≤ gapVolume K g p


/-- Shearing one form by the sum of the other forms makes the relation strictly
positive while preserving every covered point and any prescribed nonnegative
allowance below total cost one. No volume hypothesis or plank inequality is used. -/
theorem exists_positive_relation_refinement
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (A : Fin m → ℝ) (level : ℝ) (hA : ∀ i, 0 ≤ A i) (hpos : ∃ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i*f i x = level)
    (p : Endpoints (Fin m)) (hp : ∀ i, p.1 i ≤ p.2 i)
    (q : ℝ) (hq : 0 ≤ q) (hsmall : budget K f p+q < 1) :
    ∃ (g : Fin m → (Point d) →ᵃ[ℝ] ℝ) (B : Fin m → ℝ)
      (c : ℝ) (w : Endpoints (Fin m)),
      (∀ i, 0 < Body.width K (g i)) ∧ (∀ i, 0 < B i) ∧
      (∀ x ∈ K, ∑ i, B i*g i x = c) ∧
      (∀ i, w.1 i ≤ w.2 i) ∧
      (K ∩ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) ⊆
        (⋃ i, {x | w.1 i ≤ g i x ∧ g i x ≤ w.2 i}) ∧
      budget K g w+q < 1 := by
  classical
  obtain ⟨k,hAk⟩ := hpos
  let T := Finset.univ.erase k
  let R := budget K f p
  let N : ℝ := max 1 ((m:ℝ)-1)
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hm : 1 ≤ m := Nat.succ_le_of_lt (Nat.zero_le k.val |>.trans_lt k.isLt)
  let e := (1-(R+q))/(4*N)
  have hR : 0 ≤ R := Finset.sum_nonneg (fun i _ =>
    div_nonneg (sub_nonneg.mpr (hp i)) (by rw [hunit]; norm_num))
  have he : 0 < e := div_pos (sub_pos.mpr hsmall) (mul_pos (by norm_num) hN)
  have heq : 4*N*e = 1-(R+q) := by dsimp [e]; field_simp
  have hd : 0 < 1-N*e := by nlinarith only [heq,hR,hq]
  have hsum (x : Point d) (hx : x ∈ K) :
      0 ≤ ∑ j ∈ T, f j x ∧ ∑ j ∈ T, f j x ≤ N := by
    refine ⟨Finset.sum_nonneg (fun i _ => (hnorm i x hx).1),?_⟩
    calc
      _ ≤ ∑ j ∈ T, (1:ℝ) := Finset.sum_le_sum (fun j _ => (hnorm j x hx).2)
      _ = (m:ℝ)-1 := by simp [T,Finset.card_erase_of_mem, Nat.cast_sub hm]
      _ ≤ N := le_max_right _ _
  let step : Fin m → ℝ := fun i => if i=k then e else 0
  have hstep (i) : 0 ≤ step i ∧ step i ≤ e := by
    by_cases hi : i=k <;> simp [step,hi,he.le]
  let g : Fin m → (Point d) →ᵃ[ℝ] ℝ :=
    fun i => f i-step i • ∑ j ∈ T, f j
  have hg (i : Fin m) (x : Point d) :
      g i x = f i x-step i*(∑ j ∈ T, f j x) := by
    let ev : ((Point d) →ᵃ[ℝ] ℝ) →+ ℝ :=
      { toFun := fun h => h x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    change f i x-step i*(∑ j ∈ T, f j) x = _
    rw [show (∑ j ∈ T, f j) x = ∑ j ∈ T, f j x from map_sum ev f T]
  have hnear (x : Point d) (hx : x ∈ K) (i : Fin m) :
      f i x-N*step i ≤ g i x ∧ g i x ≤ f i x := by
    rw [hg]
    constructor <;> nlinarith only [mul_le_mul_of_nonneg_left (hsum x hx).2 (hstep i).1,
      mul_nonneg (hstep i).1 (hsum x hx).1]
  have hWbound (i : Fin m) : 1-N*e ≤ Body.width K (g i) := by
    obtain ⟨x,hx,hxi⟩ := (unit_realisers hK hne (f i) (hnorm i) (hunit i)).1
    obtain ⟨y,hy,hyi⟩ := (unit_realisers hK hne (f i) (hnorm i) (hunit i)).2
    linarith only [hxi,hyi,Body.sub_le_width hK (continuous_form (g i)) hy hx,
      (hnear x hx i).2,(hnear y hy i).1,mul_le_mul_of_nonneg_left (hstep i).2 hN.le]
  have hgW (i : Fin m) : 0 < Body.width K (g i) := hd.trans_le (hWbound i)
  let B : Fin m → ℝ := fun i => if i=k then A i else A i+e*A k
  have hB (i) : 0 < B i := by
    by_cases hi : i=k
    · subst i; simpa [B] using hAk
    · simpa [B,hi] using add_pos_of_nonneg_of_pos (hA i) (mul_pos he hAk)
  have hgplane : ∀ x ∈ K, ∑ i, B i*g i x = level := by
    intro x hx
    rw [← hplane x hx]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
      ← Finset.sum_erase_add _ (fun i => A i*f i x) (Finset.mem_univ k)]
    have ht : ∑ i ∈ T, B i*g i x = ∑ i ∈ T, (A i+e*A k)*f i x := by
      exact Finset.sum_congr rfl fun i hi => by
        simp [B,hg,step,(Finset.mem_erase.mp hi).1]
    change (∑ i ∈ T, B i*g i x) + B k*g k x = (∑ i ∈ T, A i*f i x) + A k*f k x
    rw [ht]
    simp only [B,step,ite_true,hg,add_mul,Finset.sum_add_distrib,← Finset.mul_sum]
    ring
  let w : Endpoints (Fin m) := (fun i => p.1 i-N*step i,p.2)
  have hworder (i) : w.1 i ≤ w.2 i :=
    (sub_le_self _ (mul_nonneg hN.le (hstep i).1)).trans (hp i)
  have hbudget : budget K g w ≤ (R+N*e)/(1-N*e) := by
    calc
      _ ≤ ∑ i, (w.2 i-w.1 i)/(1-N*e) := Finset.sum_le_sum (fun i _ =>
        div_le_div_of_nonneg_left (sub_nonneg.mpr (hworder i)) hd (hWbound i))
      _ = _ := by
        rw [← Finset.sum_div]
        congr 1
        simp [R,budget,hunit,w,step,mul_ite,sub_sub_eq_add_sub,Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
        ring
  have hcovered :
      (K ∩ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) ⊆
        ⋃ i, {x | w.1 i ≤ g i x ∧ g i x ≤ w.2 i} := by
    rintro x ⟨hx,hcov⟩
    obtain ⟨i,hi⟩ := mem_iUnion.mp hcov
    apply mem_iUnion.mpr
    exact ⟨i,(sub_le_sub_right hi.1 (N*step i)).trans (hnear x hx i).1,
      (hnear x hx i).2.trans hi.2⟩
  refine ⟨g,B,level,w,hgW,hB,hgplane,hworder,hcovered,
    lt_of_le_of_lt (add_le_add hbudget (le_refl q)) ?_⟩
  rw [← lt_sub_iff_add_lt,div_lt_iff₀ hd]
  nlinarith only [heq,mul_pos hN he,mul_nonneg (mul_nonneg hN.le he.le) hq]

/-- The quantitative transfer is the geometric refinement with the original
gap root as allowance. Covered-set inclusion makes the new gap no larger. -/
theorem nonnegative_relation_bound_of_order
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (hpositive : PositiveRelationBound K m)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (A : Fin m → ℝ) (level : ℝ) (hA : ∀ i, 0 ≤ A i) (hpos : ∃ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i*f i x = level)
    (p : Endpoints (Fin m)) (hp : ∀ i, p.1 i ≤ p.2 i) :
    (max 0 (1-budget K f p))^(d+1)*(volume K).toReal ≤ gapVolume K f p := by
  by_contra hn
  have hR : budget K f p ≤ 1 := by
    by_contra hnR
    apply hn
    rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge hnR)),
      zero_pow (Nat.succ_ne_zero d), zero_mul]
    exact ENNReal.toReal_nonneg
  have hbad : rootCost K f p < 1 :=
    (rootCost_lt_one_iff hV f p hR).mpr (lt_of_not_ge hn)
  have hq : 0 ≤ gapRoot K f p :=
    Real.rpow_nonneg (div_nonneg ENNReal.toReal_nonneg hV.le) _
  obtain ⟨g,B,c,w,hgW,hB,hplane,horder,hcovered,hcost⟩ :=
    exists_positive_relation_refinement hK hne f hnorm hunit A level hA hpos hplane
      p hp (gapRoot K f p) hq
      (by simpa only [rootCost,add_comm] using hbad)
  have hgap : gapVolume K g w ≤ gapVolume K f p := by
    apply ENNReal.toReal_mono (measure_ne_top_of_subset sdiff_subset hK.measure_ne_top)
    apply measure_mono
    intro x hx
    exact ⟨hx.1,fun hcov => hx.2 (hcovered ⟨hx.1,hcov⟩)⟩
  have hroot : gapRoot K g w ≤ gapRoot K f p :=
    Real.rpow_le_rpow (div_nonneg ENNReal.toReal_nonneg hV.le)
      (div_le_div_of_nonneg_right hgap hV.le) (by positivity)
  have hgcost : rootCost K g w < 1 := by
    unfold rootCost
    linarith only [hroot,hcost]
  have hgR : budget K g w ≤ 1 := by linarith only [hcost,hq]
  exact ((rootCost_lt_one_iff hV g w hgR).mp hgcost).not_ge
    (hpositive g hgW B c hB hplane w horder)

/-- The original normalized-domain interface is a specialization of the
ordered-endpoint transfer. No clipping is used by that transfer. -/
theorem nonnegative_relation_bound
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (hpositive : PositiveRelationBound K m)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (A : Fin m → ℝ) (level : ℝ) (hA : ∀ i, 0 ≤ A i) (hpos : ∃ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i*f i x = level)
    (p : Endpoints (Fin m)) (hp : p ∈ domain K f) :
    (max 0 (1-budget K f p))^(d+1)*(volume K).toReal ≤ gapVolume K f p :=
  nonnegative_relation_bound_of_order hK hne hV hpositive f hnorm hunit
    A level hA hpos hplane p (fun i => (hp.1 i).2.1)

/-- Reflect negative coefficients using one common sign choice. This
preserves the entire union of bands, budget, order and any normalized-domain
membership. The supplied endpoints need not belong to that domain. -/
theorem exists_reflected_family_of_order
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (a : Fin m → ℝ) (level : ℝ)
    (hplane : ∀ x ∈ K, ∑ i, a i*f i x = level)
    (p : Endpoints (Fin m)) (hp : ∀ i, p.1 i ≤ p.2 i) :
    ∃ (g : Fin m → (Point d) →ᵃ[ℝ] ℝ) (q : Endpoints (Fin m)) (c : ℝ),
      (∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1) ∧
      (∀ i, Body.width K (g i) = 1) ∧
      (∀ x ∈ K, ∑ i, |a i| * g i x = c) ∧
      (∀ i, q.1 i ≤ q.2 i) ∧ (p ∈ domain K f → q ∈ domain K g) ∧
      (⋃ i, {x | q.1 i ≤ g i x ∧ g i x ≤ q.2 i}) =
        (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) ∧
      budget K g q = budget K f p := by
  let g : Fin m → (Point d) →ᵃ[ℝ] ℝ := fun i =>
    if a i < 0 then AffineMap.const ℝ (Point d) 1-f i else f i
  let q : Endpoints (Fin m) :=
    (fun i => if a i < 0 then 1-p.2 i else p.1 i,
     fun i => if a i < 0 then 1-p.1 i else p.2 i)
  have hgnorm : ∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1 := by
    intro i x hx
    by_cases hi : a i < 0
    · simp only [g,ite_eq_left hi]
      change 0 ≤ 1-f i x ∧ 1-f i x ≤ 1
      constructor <;> linarith only [(hnorm i x hx).1,(hnorm i x hx).2]
    · simpa only [g,ite_eq_right hi] using hnorm i x hx
  have hgunit (i) : Body.width K (g i) = 1 := by
    dsimp only [g]
    split_ifs <;> simpa only [Body.width_const_sub hK hne (continuous_form (f i))] using hunit i
  have hbudget : budget K g q = budget K f p := by
    simp only [budget,hgunit,hunit,div_one]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [q]
    split_ifs <;> ring
  have hset : (⋃ i, {x | q.1 i ≤ g i x ∧ g i x ≤ q.2 i}) =
      ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i} := by
    ext x
    simp only [mem_iUnion,mem_ofPred_eq]
    apply exists_congr
    intro i
    by_cases hi : a i < 0
    · simp only [g,q,ite_eq_left hi]
      change (1-p.2 i ≤ 1-f i x ∧ 1-f i x ≤ 1-p.1 i) ↔
        (p.1 i ≤ f i x ∧ f i x ≤ p.2 i)
      constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith only [h1,h2]
    · simp only [g,q,ite_eq_right hi]
  have hqorder : ∀ i, q.1 i ≤ q.2 i := by
    intro i
    dsimp [q]
    split_ifs
    · linarith only [hp i]
    · exact hp i
  have hq : p ∈ domain K f → q ∈ domain K g := by
    intro hpD
    refine ⟨?_,by simpa only [hbudget] using hpD.2⟩
    intro i
    dsimp [q]
    split_ifs
    · constructor
      · linarith only [(hpD.1 i).2.2]
      · constructor <;> linarith only [(hpD.1 i).1,(hpD.1 i).2.1]
    · exact hpD.1 i
  have hgplane : ∀ x ∈ K, ∑ i, |a i| * g i x =
      level+∑ i, if a i < 0 then -a i else 0 := by
    intro x hx
    rw [← hplane x hx,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a i < 0
    · simp only [g,ite_eq_left hi,abs_of_neg hi]
      change (-a i)*(1-f i x) = a i*f i x + -a i
      ring
    · simp only [g,ite_eq_right hi,abs_of_nonneg (le_of_not_gt hi),add_zero]
  exact ⟨g,q,level+∑ i, if a i < 0 then -a i else 0,
    hgnorm,hgunit,hgplane,hqorder,hq,hset,hbudget⟩

/-- The original reflection contract retains normalized-domain membership. -/
theorem exists_reflected_family
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (a : Fin m → ℝ) (level : ℝ)
    (hplane : ∀ x ∈ K, ∑ i, a i*f i x = level)
    (p : Endpoints (Fin m)) (hp : p ∈ domain K f) :
    ∃ (g : Fin m → (Point d) →ᵃ[ℝ] ℝ) (q : Endpoints (Fin m)) (c : ℝ),
      (∀ i x, x ∈ K → 0 ≤ g i x ∧ g i x ≤ 1) ∧
      (∀ i, Body.width K (g i) = 1) ∧
      (∀ x ∈ K, ∑ i, |a i| * g i x = c) ∧ q ∈ domain K g ∧
      (⋃ i, {x | q.1 i ≤ g i x ∧ g i x ≤ q.2 i}) =
        (⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) ∧
      budget K g q = budget K f p := by
  obtain ⟨g,q,c,hgnorm,hgunit,hgplane,_,hq,hset,hbudget⟩ :=
    exists_reflected_family_of_order hK hne f hnorm hunit a level hplane p
      (fun i => (hp.1 i).2.1)
  exact ⟨g,q,c,hgnorm,hgunit,hgplane,hq hp,hset,hbudget⟩

/-- Any nonzero relation transfers the bound for arbitrary ordered endpoints.
No clipping or normalized-domain premise is required. -/
theorem relation_bound_of_order
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (hpositive : PositiveRelationBound K m)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (a : Fin m → ℝ) (level : ℝ) (ha : ∃ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i*f i x = level)
    (p : Endpoints (Fin m)) (hp : ∀ i, p.1 i ≤ p.2 i) :
    (max 0 (1-budget K f p))^(d+1)*(volume K).toReal ≤ gapVolume K f p := by
  obtain ⟨g,q,c,hgnorm,hgunit,hgplane,hq,_,hset,hbudget⟩ :=
    exists_reflected_family_of_order hK hne f hnorm hunit a level hplane p hp
  have hapos : ∃ i, 0 < |a i| := by
    obtain ⟨i,hi⟩ := ha
    exact ⟨i,abs_pos.mpr hi⟩
  have H := nonnegative_relation_bound_of_order hK hne hV hpositive g hgnorm hgunit
    (fun i => |a i|) c (fun i => abs_nonneg _) hapos hgplane q hq
  simpa only [hbudget,gapVolume,hset] using H

/-- Normalize an arbitrary dependent family exactly, then reflect and refine.
The positive-relation bound remains an explicit input in every dimension and
plank count. This transfer does not clip endpoints or select a minimum. -/
theorem bound_of_relation
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (hpositive : PositiveRelationBound K m)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ) (hW : ∀ i, 0 < Body.width K (f i))
    (a : Fin m → ℝ) (level : ℝ) (ha : ∃ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i*f i x = level)
    (p : Endpoints (Fin m)) (hp : ∀ i, p.1 i ≤ p.2 i) :
    (max 0 (1-budget K f p))^(d+1)*(volume K).toReal ≤ gapVolume K f p := by
  obtain ⟨g,q,b,hg,hunit,hnorm,hq,hbudget,_,hgap⟩ :=
    normalize_data_with_formula hK hne f p.1 p.2 hp hW
  have hgplane : ∀ x ∈ K,
      ∑ i, (a i*Body.width K (f i))*g i x = level-∑ i, a i*b i := by
    intro x hx
    rw [← hplane x hx,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hg]
    field_simp [(hW i).ne']
  have hane : ∃ i, a i*Body.width K (f i) ≠ 0 := by
    obtain ⟨i,hi⟩ := ha
    exact ⟨i,mul_ne_zero hi (hW i).ne'⟩
  have H := relation_bound_of_order hK hne hV hpositive g hnorm hunit
    (fun i => a i*Body.width K (f i)) (level-∑ i, a i*b i) hane hgplane q hq
  simpa only [hbudget,hgap] using H

/-- Reflect and refine any nonzero affine relation before minimizing. -/
theorem relation_bound
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (hV : 0 < (volume K).toReal) (hpositive : PositiveRelationBound K m)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (a : Fin m → ℝ) (level : ℝ) (ha : ∃ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i*f i x = level)
    (p : Endpoints (Fin m)) (hp : p ∈ domain K f) :
    (max 0 (1-budget K f p))^(d+1)*(volume K).toReal ≤ gapVolume K f p :=
  relation_bound_of_order hK hne hV hpositive f hnorm hunit a level ha hplane p
    (fun i => (hp.1 i).2.1)

/-- The covering inequality restricted to strictly positive affine relations.
It is a geometric input; no quantitative gap estimate is assumed. -/
def PositiveRelationCoverBound (K : Set (Point d)) (m : ℕ) : Prop :=
  ∀ (g : Fin m → (Point d) →ᵃ[ℝ] ℝ), (∀ i, 0 < Body.width K (g i)) →
  ∀ (c : Fin m → ℝ) (level : ℝ), (∀ i, 0 < c i) →
  (∀ x ∈ K, ∑ i, c i*g i x = level) →
  ∀ (p : Endpoints (Fin m)), (∀ i, p.1 i ≤ p.2 i) →
  K ⊆ (⋃ i, {x | p.1 i ≤ g i x ∧ g i x ≤ p.2 i}) → 1 ≤ budget K g p

/-- The same refinement gives a covering transfer by taking allowance zero.
Neither positive volume nor a quantitative bound is needed. -/
theorem nonnegative_relation_cover_bound
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (hpositive : PositiveRelationCoverBound K m)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (A : Fin m → ℝ) (level : ℝ) (hA : ∀ i, 0 ≤ A i) (hpos : ∃ i, 0 < A i)
    (hplane : ∀ x ∈ K, ∑ i, A i*f i x = level)
    (p : Endpoints (Fin m)) (hp : ∀ i, p.1 i ≤ p.2 i)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  by_contra hn
  obtain ⟨g,B,c,w,hgW,hB,hplane,horder,hcovered,hcost⟩ :=
    exists_positive_relation_refinement hK hne f hnorm hunit A level hA hpos hplane
      p hp 0 (le_refl 0) (by simpa only [add_zero] using lt_of_not_ge hn)
  have H := hpositive g hgW B c hB hplane w horder
    (fun x hx => hcovered ⟨hx,hcover hx⟩)
  linarith only [hcost,H]

/-- Covering for an arbitrary nonzero relation reduces to covering for positive
relations, using the same reflection and refinement as the quantitative proof. -/
theorem relation_cover_bound_of_order
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (hpositive : PositiveRelationCoverBound K m)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (a : Fin m → ℝ) (level : ℝ) (ha : ∃ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i*f i x = level)
    (p : Endpoints (Fin m)) (hp : ∀ i, p.1 i ≤ p.2 i)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  obtain ⟨g,q,c,hgnorm,hgunit,hgplane,hq,_,hset,hbudget⟩ :=
    exists_reflected_family_of_order hK hne f hnorm hunit a level hplane p hp
  have hapos : ∃ i, 0 < |a i| := by
    obtain ⟨i,hi⟩ := ha
    exact ⟨i,abs_pos.mpr hi⟩
  have H := nonnegative_relation_cover_bound hK hne hpositive g hgnorm hgunit
    (fun i => |a i|) c (fun i => abs_nonneg _) hapos hgplane q
    hq (by rw [hset]; exact hcover)
  simpa only [hbudget] using H

/-- Covering for an arbitrary nonzero relation reduces to covering for positive
relations, using the same reflection and refinement as the quantitative proof. -/
theorem relation_cover_bound
    {K : Set (Point d)} (hK : IsCompact K) (hne : K.Nonempty)
    (hpositive : PositiveRelationCoverBound K m)
    (f : Fin m → (Point d) →ᵃ[ℝ] ℝ)
    (hnorm : ∀ i x, x ∈ K → 0 ≤ f i x ∧ f i x ≤ 1)
    (hunit : ∀ i, Body.width K (f i) = 1)
    (a : Fin m → ℝ) (level : ℝ) (ha : ∃ i, a i ≠ 0)
    (hplane : ∀ x ∈ K, ∑ i, a i*f i x = level)
    (p : Endpoints (Fin m)) (hp : p ∈ domain K f)
    (hcover : K ⊆ ⋃ i, {x | p.1 i ≤ f i x ∧ f i x ≤ p.2 i}) :
    1 ≤ budget K f p := by
  exact relation_cover_bound_of_order hK hne hpositive f hnorm hunit a level ha hplane
    p (fun i => (hp.1 i).2.1) hcover

end Plank.FiniteDimensionalRelationPerturbation

#print axioms Plank.FiniteDimensionalRelationPerturbation.exists_positive_relation_refinement
#print axioms Plank.FiniteDimensionalRelationPerturbation.nonnegative_relation_bound_of_order
#print axioms Plank.FiniteDimensionalRelationPerturbation.exists_reflected_family_of_order
#print axioms Plank.FiniteDimensionalRelationPerturbation.relation_bound_of_order
#print axioms Plank.FiniteDimensionalRelationPerturbation.bound_of_relation
#print axioms Plank.FiniteDimensionalRelationPerturbation.nonnegative_relation_bound
#print axioms Plank.FiniteDimensionalRelationPerturbation.exists_reflected_family
#print axioms Plank.FiniteDimensionalRelationPerturbation.relation_bound
#print axioms Plank.FiniteDimensionalRelationPerturbation.nonnegative_relation_cover_bound
#print axioms Plank.FiniteDimensionalRelationPerturbation.relation_cover_bound
