/- Two outer caps bound the deficit by the vertical spread and position of width chords. -/
module
public import Plank.Proofs.TwoPlankBody
public import Mathlib.Topology.Order.DenselyOrdered
@[expose] public section
noncomputable section
open Set
namespace Plank.Convex.TwoCapChordPlanks

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coverage of a strict lower cap by two closed strips extends to its wall
when the body contains a point strictly below that wall. -/
theorem closed_lower_cap_covered {K : Set E} (hK : Convex ℝ K)
    (X Y Z : E →L[ℝ] ℝ) (ax bx ay byy a : ℝ) {C : E}
    (hC : C ∈ K) (hCa : Z C < a)
    (hc : ∀ P ∈ K, Z P < a → X P ∈ Icc ax bx ∨ Y P ∈ Icc ay byy)
    {P : E} (hP : P ∈ K) (hPa : Z P ≤ a) :
    X P ∈ Icc ax bx ∨ Y P ∈ Icc ay byy := by
  let F : Set E := X ⁻¹' Icc ax bx ∪ Y ⁻¹' Icc ay byy
  have hF : IsClosed F :=
    (isClosed_Icc.preimage X.continuous).union (isClosed_Icc.preimage Y.continuous)
  let f : ℝ → E := fun t => (1-t) • P+t • C
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hmaps : MapsTo f (Ioc 0 1) F := by
    intro t ht
    have hm : f t ∈ K := hK hP hC (by linarith [ht.2]) ht.1.le (by ring)
    have hz : Z (f t) < a := by
      dsimp [f]
      simp only [map_add,map_smul,smul_eq_mul]
      have hstrict := mul_pos ht.1 (sub_pos.mpr hCa)
      nlinarith [mul_nonneg (by linarith [ht.2] : 0 ≤ 1-t) (sub_nonneg.mpr hPa)]
    exact hc (f t) hm hz
  have hzero : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl,zero_le_one⟩
  have hm := hF.closure_subset (hf.continuousWithinAt.mem_closure hzero hmaps)
  simpa [f,F] using hm

/-- The corresponding closed upper-cap coverage, with a strictly higher
point providing the approach to the wall. -/
theorem closed_upper_cap_covered {K : Set E} (hK : Convex ℝ K)
    (X Y Z : E →L[ℝ] ℝ) (ax bx ay byy b : ℝ) {C : E}
    (hC : C ∈ K) (hCb : b < Z C)
    (hc : ∀ P ∈ K, b < Z P → X P ∈ Icc ax bx ∨ Y P ∈ Icc ay byy)
    {P : E} (hP : P ∈ K) (hPb : b ≤ Z P) :
    X P ∈ Icc ax bx ∨ Y P ∈ Icc ay byy := by
  exact closed_lower_cap_covered hK X Y (-Z) ax bx ay byy (-b) hC
    (by change -Z C < -b; linarith)
    (fun Q hQ hh => hc Q hQ (by change -Z Q < -b at hh; linarith)) hP
    (by change -Z P ≤ -b; linarith)

/-- Two coordinate gaps give lower bounds on the true cap widths, so their
relative strip-width sum is at least one. -/
theorem two_plank_chord_bound {K : Set E} (hK : Convex ℝ K)
    (hcompact : IsCompact K) (X Y : E →L[ℝ] ℝ)
    (ax ay σ τ dx dy : ℝ) (hσ : 0 ≤ σ) (hτ : 0 ≤ τ)
    (hdx : 0 < dx) (hdy : 0 < dy)
    {A0 A1 B0 B1 : E} (hA0 : A0 ∈ K) (hA1 : A1 ∈ K)
    (hB0 : B0 ∈ K) (hB1 : B1 ∈ K)
    (hX : dx ≤ X A1-X A0) (hY : dy ≤ Y B1-Y B0)
    (hc : ∀ P ∈ K, X P ∈ Icc ax (ax+σ) ∨ Y P ∈ Icc ay (ay+τ)) :
    1 ≤ σ/dx+τ/dy := by
  let XA : E →ᵃ[ℝ] ℝ := X.toLinearMap.toAffineMap
  let YA : E →ᵃ[ℝ] ℝ := Y.toLinearMap.toAffineMap
  have hWX : dx ≤ Plank.Body.width K XA :=
    hX.trans (Plank.Body.sub_le_width (f := XA) hcompact X.continuous hA1 hA0)
  have hWY : dy ≤ Plank.Body.width K YA :=
    hY.trans (Plank.Body.sub_le_width (f := YA) hcompact Y.continuous hB1 hB0)
  let f : Fin 2 → (E →ᵃ[ℝ] ℝ) := ![XA,YA]
  have hf : ∀ i, Continuous (f i) := by
    intro i
    fin_cases i
    · exact X.continuous
    · exact Y.continuous
  have hpos : ∀ i, 0 < Plank.Body.width K (f i) := by
    intro i
    fin_cases i
    · exact hdx.trans_le hWX
    · exact hdy.trans_le hWY
  have hw : ∀ i : Fin 2, (![ax,ay] : Fin 2 → ℝ) i ≤ ![ax+σ,ay+τ] i := by
    intro i
    fin_cases i <;> dsimp <;> linarith
  have hcov : ∀ P ∈ K, ∃ i : Fin 2,
      ![ax,ay] i ≤ f i P ∧ f i P ≤ ![ax+σ,ay+τ] i := by
    intro P hP
    rcases hc P hP with hx | hy
    · exact ⟨0,hx⟩
    · exact ⟨1,hy⟩
  have htwo := Plank.TwoPlankBody.twoplank_affine hK hcompact ⟨A0,hA0⟩
    f hf ![ax,ay] ![ax+σ,ay+τ] hw hpos hcov
  simp only [Fin.sum_univ_two,f,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,add_sub_cancel_left] at htwo
  exact htwo.trans (add_le_add (div_le_div_of_nonneg_left hσ hdx hWX)
    (div_le_div_of_nonneg_left hτ hdy hWY))

/-- A lower cap keeps a uniformly shortened copy of each designated chord.
Endpoint heights may differ. The threshold and the horizontal strip offsets
are arbitrary; the nonpositive cap-depth case is a direct inequality. -/
theorem lower_cap_bound {K : Set E} (hK : Convex ℝ K) (hcompact : IsCompact K)
    (X Y Z : E →L[ℝ] ℝ) (ax ay σ τ a u v : ℝ)
    (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) {A0 A1 B0 B1 C : E}
    (hA0 : A0 ∈ K) (hA1 : A1 ∈ K) (hB0 : B0 ∈ K) (hB1 : B1 ∈ K)
    (hC : C ∈ K) (hX : 1 ≤ X A1-X A0) (hY : 1 ≤ Y B1-Y B0)
    (hCu : Z C ≤ u) (hCv : Z C ≤ v)
    (hAu0 : Z A0 ≤ u) (hAu1 : Z A1 ≤ u)
    (hBv0 : Z B0 ≤ v) (hBv1 : Z B1 ≤ v)
    (hc : ∀ P ∈ K, Z P < a → X P ∈ Icc ax (ax+σ) ∨ Y P ∈ Icc ay (ay+τ)) :
    a-Z C ≤ σ*max (a-Z C) (u-Z C)+τ*max (a-Z C) (v-Z C) := by
  by_cases ha : a ≤ Z C
  · have hu : 0 ≤ max (a-Z C) (u-Z C) :=
      (sub_nonneg.mpr hCu).trans (le_max_right _ _)
    have hv : 0 ≤ max (a-Z C) (v-Z C) :=
      (sub_nonneg.mpr hCv).trans (le_max_right _ _)
    exact (sub_nonpos.mpr ha).trans (add_nonneg (mul_nonneg hσ hu) (mul_nonneg hτ hv))
  have hCa : Z C < a := lt_of_not_ge ha
  let d := a-Z C
  have hd : 0 < d := sub_pos.mpr hCa
  let cap : Set E := K ∩ Z ⁻¹' Iic a
  have hcap : Convex ℝ cap := hK.inter ((convex_Iic a).linear_preimage Z.toLinearMap)
  have hccompact : IsCompact cap := hcompact.inter_right (isClosed_Iic.preimage Z.continuous)
  let scale (w : ℝ) := d/max d (w-Z C)
  let shrink (w : ℝ) (P : E) := scale w • P+(1-scale w) • C
  have hscale (w : ℝ) : 0 < scale w ∧ scale w ≤ 1 := by
    have hm : 0 < max d (w-Z C) := hd.trans_le (le_max_left _ _)
    exact ⟨div_pos hd hm,(div_le_one hm).2 (le_max_left _ _)⟩
  have hmul (w : ℝ) : scale w*max d (w-Z C) = d := by
    exact div_mul_cancel₀ _ (ne_of_gt (hd.trans_le (le_max_left _ _)))
  have hshrink (w : ℝ) (P : E) (hP : P ∈ K) (hPw : Z P ≤ w) : shrink w P ∈ cap := by
    refine ⟨hK hP hC (hscale w).1.le (by linarith [(hscale w).2]) (by ring),?_⟩
    change Z (shrink w P) ≤ a
    dsimp [shrink]
    simp only [map_add,map_smul,smul_eq_mul]
    have hp : Z P-Z C ≤ max d (w-Z C) :=
      (sub_le_sub_right hPw _).trans (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_left hp (hscale w).1.le
    rw [hmul w] at hh
    dsimp [d] at hh
    nlinarith
  have hgap (F : E →L[ℝ] ℝ) (w : ℝ) (P Q : E) :
      F (shrink w Q)-F (shrink w P) = scale w*(F Q-F P) := by
    dsimp [shrink]
    simp only [map_add,map_smul,smul_eq_mul]
    ring
  have htwo := two_plank_chord_bound hcap hccompact X Y ax ay σ τ (scale u) (scale v)
    hσ hτ (hscale u).1 (hscale v).1
    (hshrink u A0 hA0 hAu0) (hshrink u A1 hA1 hAu1)
    (hshrink v B0 hB0 hBv0) (hshrink v B1 hB1 hBv1)
    (by rw [hgap]; nlinarith [mul_le_mul_of_nonneg_left hX (hscale u).1.le])
    (by rw [hgap]; nlinarith [mul_le_mul_of_nonneg_left hY (hscale v).1.le])
    (fun P hP => closed_lower_cap_covered hK X Y Z ax (ax+σ) ay (ay+τ) a hC hCa hc hP.1 hP.2)
  have he : σ/scale u+τ/scale v =
      (σ*max d (u-Z C)+τ*max d (v-Z C))/d := by
    dsimp [scale]
    field_simp
  rw [he] at htwo
  simpa only [one_mul] using (le_div_iff₀ hd).1 htwo

/-- The upper-cap version is the lower-cap result with the height functional
negated. The upper apex may have arbitrary horizontal coordinates. -/
theorem upper_cap_bound {K : Set E} (hK : Convex ℝ K) (hcompact : IsCompact K)
    (X Y Z : E →L[ℝ] ℝ) (ax ay σ τ b u v : ℝ)
    (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) {A0 A1 B0 B1 C : E}
    (hA0 : A0 ∈ K) (hA1 : A1 ∈ K) (hB0 : B0 ∈ K) (hB1 : B1 ∈ K)
    (hC : C ∈ K) (hX : 1 ≤ X A1-X A0) (hY : 1 ≤ Y B1-Y B0)
    (hCu : u ≤ Z C) (hCv : v ≤ Z C)
    (hAu0 : u ≤ Z A0) (hAu1 : u ≤ Z A1)
    (hBv0 : v ≤ Z B0) (hBv1 : v ≤ Z B1)
    (hc : ∀ P ∈ K, b < Z P → X P ∈ Icc ax (ax+σ) ∨ Y P ∈ Icc ay (ay+τ)) :
    Z C-b ≤ σ*max (Z C-b) (Z C-u)+τ*max (Z C-b) (Z C-v) := by
  have hh := lower_cap_bound hK hcompact X Y (-Z) ax ay σ τ (-b) (-u) (-v)
    hσ hτ hA0 hA1 hB0 hB1 hC hX hY
    (by simpa using neg_le_neg hCu) (by simpa using neg_le_neg hCv)
    (by simpa using neg_le_neg hAu0) (by simpa using neg_le_neg hAu1)
    (by simpa using neg_le_neg hBv0) (by simpa using neg_le_neg hBv1)
    (fun P hP hh => hc P hP (by change -Z P < -b at hh; linarith))
  simpa only [neg_apply,neg_sub_neg] using hh

end General

/-- The distance of a height from the closed slab, expressed without division. -/
def outsideDistance (a b u : ℝ) : ℝ := max 0 (a-u)+max 0 (u-b)

theorem cap_cost_identity (a b u : ℝ) :
    max a u+max (1-b) (1-u)-1 = outsideDistance a b u := by
  unfold outsideDistance
  rcases le_total a u with ha | ha <;> rcases le_total u b with hb | hb
  · rw [max_eq_right ha,max_eq_right (by linarith),max_eq_left (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right ha,max_eq_left (by linarith),max_eq_left (by linarith),max_eq_right (by linarith)]
    ring
  · rw [max_eq_left ha,max_eq_right (by linarith),max_eq_right (by linarith),max_eq_left (by linarith)]
    ring
  · rw [max_eq_left ha,max_eq_left (by linarith),max_eq_right (by linarith),max_eq_right (by linarith)]
    ring

end Plank.Convex.TwoCapChordPlanks

/-- info: 'Plank.Convex.TwoCapChordPlanks.closed_lower_cap_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.TwoCapChordPlanks.closed_lower_cap_covered
/-- info: 'Plank.Convex.TwoCapChordPlanks.closed_upper_cap_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.TwoCapChordPlanks.closed_upper_cap_covered
/-- info: 'Plank.Convex.TwoCapChordPlanks.two_plank_chord_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.TwoCapChordPlanks.two_plank_chord_bound
/-- info: 'Plank.Convex.TwoCapChordPlanks.lower_cap_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.TwoCapChordPlanks.lower_cap_bound
/-- info: 'Plank.Convex.TwoCapChordPlanks.upper_cap_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Plank.Convex.TwoCapChordPlanks.upper_cap_bound
