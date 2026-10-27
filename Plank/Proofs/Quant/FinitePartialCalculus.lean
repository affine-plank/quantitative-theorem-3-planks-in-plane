module

public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pi

@[expose] public section

set_option autoImplicit false

open Filter
open scoped Topology BigOperators

namespace Plank.FinitePartialCalculus

/-- A continuous family of coordinate partial derivatives gives the full derivative. -/
theorem hasFDerivAt_of_continuousOn_partials
    {n : ℕ} {G : (Fin n → ℝ) → ℝ} {D : Fin n → (Fin n → ℝ) → ℝ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (hc : ∀ i, ContinuousOn (D i) U)
    (hd : ∀ x ∈ U, ∀ i,
      HasDerivAt (fun t => G (Function.update x i t)) (D i x) (x i))
    {x : Fin n → ℝ} (hx : x ∈ U) :
    HasFDerivAt G (∑ i, D i x • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  induction n with
  | zero =>
      have hG : G = fun _ => G x := funext fun y => congrArg G (Subsingleton.elim y x)
      rw [hG]
      simpa only [Finset.univ_eq_empty, Finset.sum_empty] using
        hasFDerivAt_const (𝕜 := ℝ) (G x) x
  | succ n ih =>
      let e := Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)
      let A : (ℝ × (Fin n → ℝ)) → ℝ →L[ℝ] ℝ :=
        fun v => D 0 (e v) • ContinuousLinearMap.id ℝ ℝ
      let B : (ℝ × (Fin n → ℝ)) → (Fin n → ℝ) →L[ℝ] ℝ :=
        fun v => ∑ i, D i.succ (e v) • ContinuousLinearMap.proj i
      have he : Continuous e := e.continuous
      have hV : IsOpen (e ⁻¹' U) := hU.preimage he
      have hxV : e.symm x ∈ e ⁻¹' U := by simpa using hx
      have dA : ∀ᶠ v in 𝓝 (e.symm x),
          HasFDerivAt (fun a => G (e (a, v.2))) (A v) v.1 := by
        filter_upwards [hV.mem_nhds hxV] with v hv
        apply hasFDerivAt_iff_hasDerivAt.2
        change HasDerivAt (fun a => G (Fin.cons a v.2))
          ((D 0 (Fin.cons v.1 v.2) • ContinuousLinearMap.id ℝ ℝ) 1) v.1
        simpa only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one,
          Fin.update_cons_zero, Fin.cons_zero] using hd (Fin.cons v.1 v.2) hv 0
      have dB : ∀ᶠ v in 𝓝 (e.symm x),
          HasFDerivAt (fun b => G (e (v.1, b))) (B v) v.2 := by
        filter_upwards [hV.mem_nhds hxV] with v hv
        have hs : Continuous (fun b : Fin n → ℝ => e (v.1, b)) :=
          he.comp (continuous_const.prodMk continuous_id)
        apply ih (G := fun b => G (e (v.1, b)))
          (D := fun i b => D i.succ (e (v.1, b))) (hU.preimage hs)
        · intro i
          exact (hc i.succ).comp hs.continuousOn (fun _ h => h)
        · intro y hy i
          change HasDerivAt (fun t => G (Fin.cons v.1 (Function.update y i t)))
            (D i.succ (Fin.cons v.1 y)) (y i)
          simpa only [Fin.cons_update, Fin.cons_succ] using hd (Fin.cons v.1 y) hy i.succ
        · exact hv
      have cA : ContinuousAt A (e.symm x) := by
        have h : ContinuousOn A (e ⁻¹' U) :=
          ((hc 0).comp he.continuousOn (fun _ h => h)).smul continuousOn_const
        exact (h _ hxV).continuousAt (hV.mem_nhds hxV)
      have cB : ContinuousAt B (e.symm x) := by
        have h : ContinuousOn B (e ⁻¹' U) := by
          apply continuousOn_finsetSum
          intro i _
          exact ((hc i.succ).comp he.continuousOn (fun _ h => h)).smul continuousOn_const
        exact (h _ hxV).continuousAt (hV.mem_nhds hxV)
      have hg := hasStrictFDerivAt_uncurry_coprod
        (f := fun a b => G (e (a, b)))
        (f₁ := fun a b => A (a, b)) (f₂ := fun a b => B (a, b)) dA dB cA cB
      have h := hg.hasFDerivAt.comp x e.symm.hasFDerivAt
      convert! h using 1
      · ext y
        change G y = G (e (e.symm y))
        simp
      · ext y
        change (∑ i, D i x •
          (ContinuousLinearMap.proj i : (Fin (n + 1) → ℝ) →L[ℝ] ℝ)) y =
            ((A (e.symm x)).coprod (B (e.symm x))) (e.symm y)
        simp only [A, B, e.apply_symm_apply, ContinuousLinearMap.coprod_apply,
          sum_apply, add_apply, smul_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, Fin.sum_univ_succ]
        rfl

/-- The coordinate-partial criterion is invariant under finite reindexing. -/
theorem hasFDerivAt_fintype_of_continuousOn_partials
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {G : (κ → ℝ) → ℝ} {D : κ → (κ → ℝ) → ℝ}
    {U : Set (κ → ℝ)} (hU : IsOpen U)
    (hc : ∀ i, ContinuousOn (D i) U)
    (hd : ∀ x ∈ U, ∀ i,
      HasDerivAt (fun t => G (Function.update x i t)) (D i x) (x i))
    {x : κ → ℝ} (hx : x ∈ U) :
    HasFDerivAt G (∑ i, D i x • (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ)) x := by
  let q : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let e : (Fin (Fintype.card κ) → ℝ) ≃L[ℝ] (κ → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : κ => ℝ) q
  have he_apply (y : Fin (Fintype.card κ) → ℝ) (i : κ) : e y i = y (q.symm i) := by
    change (Equiv.piCongrLeft (fun _ : κ => ℝ) q) y i = y (q.symm i)
    simp [Equiv.piCongrLeft_apply]
  have he_symm_apply (y : κ → ℝ) (i : Fin (Fintype.card κ)) : e.symm y i = y (q i) := rfl
  have he_update (y : Fin (Fintype.card κ) → ℝ) (i : Fin (Fintype.card κ)) (t : ℝ) :
      e (Function.update y i t) = Function.update (e y) (q i) t := by
    have he_eq (z : Fin (Fintype.card κ) → ℝ) : e z = z ∘ q.symm := funext (he_apply z)
    rw [he_eq, he_eq]
    simpa only [Equiv.symm_symm] using Function.update_comp_equiv y q.symm i t
  have hd' : ∀ y ∈ e ⁻¹' U, ∀ i,
      HasDerivAt (fun t => G (e (Function.update y i t))) (D (q i) (e y)) (y i) := by
    intro y hy i
    simpa only [he_update, he_apply, q.symm_apply_apply] using hd (e y) hy (q i)
  have hg := hasFDerivAt_of_continuousOn_partials
    (G := fun y => G (e y)) (D := fun i y => D (q i) (e y))
    (hU.preimage e.continuous)
    (fun i => (hc (q i)).comp e.continuous.continuousOn (fun _ h => h)) hd'
    (x := e.symm x) (by simpa using hx)
  have h := hg.comp x e.symm.hasFDerivAt
  convert! h using 1
  · ext y
    change G y = G (e (e.symm y))
    simp
  · ext y
    change (∑ i, D i x • (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ)) y =
      (∑ i, D (q i) (e (e.symm x)) •
        (ContinuousLinearMap.proj i : (Fin (Fintype.card κ) → ℝ) →L[ℝ] ℝ)) (e.symm y)
    simp only [e.apply_symm_apply, sum_apply, smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, he_symm_apply]
    exact (q.sum_comp (fun i => D i x * y i)).symm

/-- The coordinate-partial criterion on a product of arbitrary finite coordinate spaces. -/
theorem hasFDerivAt_fintype_prod_of_continuousOn_partials
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] {G : ((κ → ℝ) × (ι → ℝ)) → ℝ}
    {D₁ : κ → ((κ → ℝ) × (ι → ℝ)) → ℝ}
    {D₂ : ι → ((κ → ℝ) × (ι → ℝ)) → ℝ}
    {U : Set ((κ → ℝ) × (ι → ℝ))} (hU : IsOpen U)
    (hc₁ : ∀ i, ContinuousOn (D₁ i) U) (hc₂ : ∀ i, ContinuousOn (D₂ i) U)
    (hd₁ : ∀ x ∈ U, ∀ i,
      HasDerivAt (fun t => G (Function.update x.1 i t, x.2)) (D₁ i x) (x.1 i))
    (hd₂ : ∀ x ∈ U, ∀ i,
      HasDerivAt (fun t => G (x.1, Function.update x.2 i t)) (D₂ i x) (x.2 i))
    {x : (κ → ℝ) × (ι → ℝ)} (hx : x ∈ U) :
    HasFDerivAt G
      ((∑ i, D₁ i x • (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ)).coprod
       (∑ i, D₂ i x • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))) x := by
  let A : ((κ → ℝ) × (ι → ℝ)) → (κ → ℝ) →L[ℝ] ℝ :=
    fun v => ∑ i, D₁ i v • ContinuousLinearMap.proj i
  let B : ((κ → ℝ) × (ι → ℝ)) → (ι → ℝ) →L[ℝ] ℝ :=
    fun v => ∑ i, D₂ i v • ContinuousLinearMap.proj i
  have dA : ∀ᶠ v in 𝓝 x, HasFDerivAt (fun a => G (a, v.2)) (A v) v.1 := by
    filter_upwards [hU.mem_nhds hx] with v hv
    have hs : Continuous (fun a : κ → ℝ => (a, v.2)) :=
      continuous_id.prodMk continuous_const
    exact hasFDerivAt_fintype_of_continuousOn_partials (G := fun a => G (a, v.2))
      (D := fun i a => D₁ i (a, v.2)) (hU.preimage hs)
      (fun i => (hc₁ i).comp hs.continuousOn (fun _ h => h))
      (fun a ha i => hd₁ (a, v.2) ha i) hv
  have dB : ∀ᶠ v in 𝓝 x, HasFDerivAt (fun b => G (v.1, b)) (B v) v.2 := by
    filter_upwards [hU.mem_nhds hx] with v hv
    have hs : Continuous (fun b : ι → ℝ => (v.1, b)) :=
      continuous_const.prodMk continuous_id
    exact hasFDerivAt_fintype_of_continuousOn_partials (G := fun b => G (v.1, b))
      (D := fun i b => D₂ i (v.1, b)) (hU.preimage hs)
      (fun i => (hc₂ i).comp hs.continuousOn (fun _ h => h))
      (fun b hb i => hd₂ (v.1, b) hb i) hv
  have cA : ContinuousOn A U :=
    continuousOn_finsetSum _ (fun i _ => (hc₁ i).smul continuousOn_const)
  have cB : ContinuousOn B U :=
    continuousOn_finsetSum _ (fun i _ => (hc₂ i).smul continuousOn_const)
  exact (hasStrictFDerivAt_uncurry_coprod (f := fun a b => G (a, b))
    (f₁ := fun a b => A (a, b)) (f₂ := fun a b => B (a, b)) dA dB
    ((cA _ hx).continuousAt (hU.mem_nhds hx))
    ((cB _ hx).continuousAt (hU.mem_nhds hx))).hasFDerivAt

/-- Continuous lower- and upper-coordinate partials give `C¹` regularity. -/
theorem contDiffOn_one_fintype_prod_of_continuousOn_partials
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι] {G : ((κ → ℝ) × (ι → ℝ)) → ℝ}
    {D₁ : κ → ((κ → ℝ) × (ι → ℝ)) → ℝ}
    {D₂ : ι → ((κ → ℝ) × (ι → ℝ)) → ℝ}
    {U : Set ((κ → ℝ) × (ι → ℝ))} (hU : IsOpen U)
    (hc₁ : ∀ i, ContinuousOn (D₁ i) U) (hc₂ : ∀ i, ContinuousOn (D₂ i) U)
    (hd₁ : ∀ x ∈ U, ∀ i,
      HasDerivAt (fun t => G (Function.update x.1 i t, x.2)) (D₁ i x) (x.1 i))
    (hd₂ : ∀ x ∈ U, ∀ i,
      HasDerivAt (fun t => G (x.1, Function.update x.2 i t)) (D₂ i x) (x.2 i)) :
    ContDiffOn ℝ 1 G U := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := 0) hU.uniqueDiffOn).2
  refine ⟨by simp,
    (fun x => (∑ i, D₁ i x • (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ)).coprod
      (∑ i, D₂ i x • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))), ?_, ?_⟩
  · apply contDiffOn_zero.2
    exact (continuousOn_finsetSum _ (fun i _ => (hc₁ i).smul continuousOn_const)).continuousLinearMapCoprod
        (continuousOn_finsetSum _ (fun i _ => (hc₂ i).smul continuousOn_const))
  · intro x hx
    exact (hasFDerivAt_fintype_prod_of_continuousOn_partials hU hc₁ hc₂ hd₁ hd₂ hx).hasFDerivWithinAt

end Plank.FinitePartialCalculus
