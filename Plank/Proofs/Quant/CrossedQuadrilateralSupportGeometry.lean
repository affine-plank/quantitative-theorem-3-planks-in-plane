/- Boundary obstructions to a support contraction on a genuine quadrilateral. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralGenuine

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralSupportGeometry
open Set MeasureTheory
open CrossedQuadrilateralAttainment

theorem ray_eval (f : Point →ᵃ[ℝ] ℝ) (a b : Point) (t : ℝ) :
    f (a+t • (b-a)) = f a+t*(f b-f a) := by
  have he := f.map_vadd a (t • (b-a))
  have hd : f.linear (b-a) = f b-f a := f.linearMap_vsub b a
  simpa only [vadd_eq_add,vsub_eq_sub,map_smul,hd,smul_eq_mul,
    add_comm] using he

theorem homothety_eval (f : Point →ᵃ[ℝ] ℝ) (a x : Point) (r : ℝ) :
    f (AffineMap.homothety a (1-r) x) = r*f a+(1-r)*f x := by
  change f ((1-r) • (x-a)+a) = _
  rw [add_comm,ray_eval]
  ring

theorem homothety_support {K : Set Point} (L : Point →ᵃ[ℝ] ℝ) (a : Point)
    {r : ℝ} (hr : r ≤ 1) (hL : ∀ x ∈ K, L x ≤ 1) {x : Point}
    (hx : x ∈ AffineMap.homothety a (1-r) '' K) :
    L x ≤ r*L a+(1-r) := by
  obtain ⟨y,hy,rfl⟩ := hx
  rw [homothety_eval]
  nlinarith only [mul_le_mul_of_nonneg_left (hL y hy) (sub_nonneg.mpr hr)]

/-- An apex-centred contraction leaves a boundary point below the second
band and above the first. The hypotheses are only affine values and a
supporting line, so the lemma applies to either orientation of the diagonal. -/
theorem apex_obstruction {K : Set Point} (hK : Convex ℝ K)
    (F G L : Point →ᵃ[ℝ] ℝ) (a b z : Point)
    (ha : a ∈ K) (hb : b ∈ K) (hz : z ∈ K)
    (hFa : F a = 1) (hFb : 0 ≤ F b)
    (hGa : G a = 1) (hGb : G b = 0)
    (t r s : ℝ) (ht : 0 < t) (ht1 : t < 1) (hGz : G z = t)
    (hFz : t+(1-t)*F b ≤ F z)
    (hr : 0 < r) (hs : 0 < s) (hR : r+s < 1)
    (hLa : L a < 1) (hLb : L b = 1) (hLz : L z = 1)
    (hL : ∀ x ∈ K, L x ≤ 1) :
    ∃ x ∈ K, r < F x ∧ G x < r+(1-r-s)*t ∧
      x ∉ AffineMap.homothety a (1-r) '' K := by
  let lo := r+(1-r-s)*t
  let v := (r+lo)/2
  have hr1 : r < 1 := by linarith only [hs,hR]
  have hlo : r < lo := by dsimp [lo]; nlinarith only [mul_pos (by linarith : 0 < 1-r-s) ht]
  have hv : r < v := by dsimp [v]; linarith only [hlo]
  have hvlo : v < lo := by dsimp [v]; linarith only [hlo]
  have hlo1 : lo < 1 := by
    have hh := mul_lt_mul_of_pos_left ht1 (by linarith : 0 < 1-r-s)
    dsimp [lo]; nlinarith only [hh,hs]
  have hvr : v < r+(1-r)*t := by
    have hh : 0 < s*t := mul_pos hs ht
    dsimp [lo] at hvlo
    nlinarith only [hvlo,hh]
  have hzt : t ≤ F z := by
    have hh := mul_nonneg (sub_pos.mpr ht1).le hFb
    linarith only [hFz,hh]
  by_cases hvt : v ≤ t
  · let u := v/t
    have hu0 : 0 ≤ u := div_nonneg (hr.le.trans hv.le) ht.le
    have hu1 : u ≤ 1 := (div_le_one ht).mpr hvt
    let x := b+u • (z-b)
    have hx : x ∈ K := hK.add_smul_sub_mem hb hz ⟨hu0,hu1⟩
    have hGx : G x = v := by
      dsimp [x]; rw [ray_eval,hGb,hGz]; dsimp [u]
      field_simp
      ring
    have hFx : v ≤ F x := by
      have hh := mul_le_mul_of_nonneg_left hzt hu0
      have hh' := mul_nonneg (sub_nonneg.mpr hu1) hFb
      have hut : u*t = v := div_mul_cancel₀ _ ht.ne'
      dsimp [x]; rw [ray_eval]
      nlinarith only [hh,hh',hut]
    have hLx : L x = 1 := by dsimp [x]; rw [ray_eval,hLb,hLz]; ring
    refine ⟨x,hx,hv.trans_le hFx,hGx ▸ hvlo,?_⟩
    intro hmem
    have hh := homothety_support L a hr1.le hL hmem
    rw [hLx] at hh
    have hh' := mul_pos hr (sub_pos.mpr hLa)
    nlinarith only [hh,hh']
  · let u := (v-t)/(1-t)
    have htv : t < v := lt_of_not_ge hvt
    have hu0 : 0 ≤ u := div_nonneg (sub_pos.mpr htv).le (sub_pos.mpr ht1).le
    have hu1 : u ≤ 1 := (div_le_one (sub_pos.mpr ht1)).mpr (by linarith only [hvlo,hlo1])
    have hur : u < r := (div_lt_iff₀ (sub_pos.mpr ht1)).mpr (by nlinarith only [hvr])
    let x := z+u • (a-z)
    have hx : x ∈ K := hK.add_smul_sub_mem hz ha ⟨hu0,hu1⟩
    have hue : u*(1-t) = v-t := div_mul_cancel₀ _ (sub_pos.mpr ht1).ne'
    have hGx : G x = v := by dsimp [x]; rw [ray_eval,hGz,hGa]; linarith only [hue]
    have hFx : v ≤ F x := by
      have hh := mul_le_mul_of_nonneg_left hzt (sub_nonneg.mpr hu1)
      dsimp [x]; rw [ray_eval,hFa]
      nlinarith only [hh,hue]
    have hLx : L x = 1+u*(L a-1) := by dsimp [x]; rw [ray_eval,hLz]
    refine ⟨x,hx,hv.trans_le hFx,hGx ▸ hvlo,?_⟩
    intro hmem
    have hh := homothety_support L a hr1.le hL hmem
    rw [hLx] at hh
    have hh' := mul_pos (sub_pos.mpr hur) (sub_pos.mpr hLa)
    nlinarith only [hh,hh']

/-- A base-centred contraction misses a point just beyond its homothetic
edge endpoint. A positive affine value at the opposite vertex is enough. -/
theorem base_obstruction {K : Set Point} (hK : Convex ℝ K)
    (F G L : Point →ᵃ[ℝ] ℝ) (a c : Point) (ha : a ∈ K) (hc : c ∈ K)
    (hFa : F a = 1) (hFc : 0 < F c)
    (t r s : ℝ) (ht1 : t < 1) (hGa : G a = t) (hGc : G c = 1)
    (hr : 0 < r) (hs : 0 ≤ s) (hR : r+s < 1)
    (hLa : L a < 1) (hLc : L c = 1) (hL : ∀ x ∈ K, L x ≤ 1) :
    ∃ x ∈ K, r < F x ∧ t+s*(1-t) < G x ∧
      x ∉ AffineMap.homothety a (1-r) '' K := by
  let q := 1-r
  let e := min (r/2) (q*F c/2)
  let u := q+e
  have hq : 0 < q := by dsimp [q]; linarith only [hR,hs]
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have her : e ≤ r/2 := min_le_left _ _
  have hef : e ≤ q*F c/2 := min_le_right _ _
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u,q] at *; linarith only [her,hr]
  have huq : q < u := by dsimp [u]; linarith only [he]
  have hus : s < u := by dsimp [q] at huq; linarith only [huq,hR]
  let x := a+u • (c-a)
  have hx : x ∈ K := hK.add_smul_sub_mem ha hc ⟨hu0,hu1⟩
  have hFx : r < F x := by
    have hh := mul_nonneg he.le hFc.le
    have hh' := mul_pos hq hFc
    dsimp [x]; rw [ray_eval,hFa]
    dsimp [u,q] at *
    nlinarith only [hef,hh,hh']
  have hGx : t+s*(1-t) < G x := by
    dsimp [x]; rw [ray_eval,hGa,hGc]
    nlinarith only [mul_pos (sub_pos.mpr hus) (sub_pos.mpr ht1)]
  refine ⟨x,hx,hFx,hGx,?_⟩
  intro hmem
  have hh := homothety_support L a (by dsimp [q] at hq; linarith only [hq]) hL hmem
  dsimp [x] at hh
  rw [ray_eval,hLc] at hh
  have hh' := mul_pos (sub_pos.mpr huq) (sub_pos.mpr hLa)
  dsimp [q] at hh'
  nlinarith only [hh,hh']

theorem eval_x (F : Point →ᵃ[ℝ] ℝ) (x : ℝ) :
    F (x,0) = F 0+x*(F (1,0)-F 0) := by
  simpa using ray_eval F 0 (1,0) x

theorem eval_y (F : Point →ᵃ[ℝ] ℝ) (y : ℝ) :
    F (0,y) = F 0+y*(F (0,1)-F 0) := by
  simpa using ray_eval F 0 (0,1) y

theorem some_x_ge (S : Shape) (F : Point →ᵃ[ℝ] ℝ) :
    ∃ i : Bool, F 0 ≤ F (S.X i,0) := by
  by_cases h : 0 ≤ F (1,0)-F 0
  · refine ⟨true,?_⟩
    rw [eval_x]; simp only [Shape.X,if_true]
    exact le_add_of_nonneg_right (mul_nonneg S.ha.le h)
  · refine ⟨false,?_⟩
    rw [eval_x]; simp only [Shape.X,Bool.false_eq_true,if_false]
    exact le_add_of_nonneg_right (mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr S.hc.le) (le_of_not_ge h))

theorem some_y_ge (S : Shape) (F : Point →ᵃ[ℝ] ℝ) :
    ∃ j : Bool, F 0 ≤ F (0,S.Y j) := by
  by_cases h : 0 ≤ F (0,1)-F 0
  · refine ⟨true,?_⟩
    rw [eval_y]; simp only [Shape.Y,if_true]
    exact le_add_of_nonneg_right (mul_nonneg S.hb.le h)
  · refine ⟨false,?_⟩
    rw [eval_y]; simp only [Shape.Y,Bool.false_eq_true,if_false]
    exact le_add_of_nonneg_right (mul_nonneg_of_nonpos_of_nonpos
      (neg_nonpos.mpr S.hd.le) (le_of_not_ge h))

def xLevel (S : Shape) (i : Bool) : Point →ᵃ[ℝ] ℝ :=
  if i then (S.a+S.c)⁻¹ • direction (1,0)+AffineMap.const ℝ Point (S.c/(S.a+S.c))
  else -(S.a+S.c)⁻¹ • direction (1,0)+AffineMap.const ℝ Point (S.a/(S.a+S.c))

theorem xLevel_apply (S : Shape) (i : Bool) (x : Point) :
    xLevel S i x = if i then (x.1+S.c)/(S.a+S.c) else (S.a-x.1)/(S.a+S.c) := by
  cases i <;> simp [xLevel,dot,div_eq_mul_inv] <;> ring

theorem level_pos (S : Shape) (i : Bool) : 0 < xLevel S i 0 := by
  cases i <;> simp only [xLevel_apply,if_true,Bool.false_eq_true,if_false,
    Prod.fst_zero,zero_add,sub_zero]
  · exact div_pos S.ha (add_pos S.ha S.hc)
  · exact div_pos S.hc (add_pos S.ha S.hc)

theorem level_lt_one (S : Shape) (i : Bool) : xLevel S i 0 < 1 := by
  cases i <;> simp only [xLevel_apply,if_true,Bool.false_eq_true,if_false,
    Prod.fst_zero,zero_add,sub_zero] <;> apply (div_lt_one (add_pos S.ha S.hc)).mpr <;>
    linarith [S.ha,S.hc]

theorem level_vertex (S : Shape) (i : Bool) : xLevel S i (S.X i,0) = 1 := by
  cases i <;> simp [xLevel_apply,Shape.X,ne_of_gt (add_pos S.ha S.hc)]

theorem level_opposite (S : Shape) (i : Bool) : xLevel S i (S.X (!i),0) = 0 := by
  cases i <;> simp [xLevel_apply,Shape.X]

theorem level_y (S : Shape) (i j : Bool) : xLevel S i (0,S.Y j) = xLevel S i 0 := by
  simp only [xLevel_apply,Prod.fst_zero]

theorem zero_x_mix (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (i : Bool) :
    F 0 = xLevel S i 0*F (S.X i,0)+(1-xLevel S i 0)*F (S.X (!i),0) := by
  rw [eval_x F (S.X i),eval_x F (S.X (!i))]
  cases i <;> simp only [xLevel_apply,Shape.X,if_true,Bool.false_eq_true,if_false,
    Bool.not_false,Bool.not_true,Prod.fst_zero,zero_add,sub_zero]
  all_goals field_simp [(add_pos S.ha S.hc).ne']; ring

theorem zero_pos_of_y (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (j : Bool)
    (hF : F (0,S.Y j) = 1) (hopp : 0 ≤ F (0,S.Y (!j))) : 0 < F 0 := by
  rw [eval_y] at hF hopp
  cases j <;> simp only [Shape.Y,if_true,Bool.false_eq_true,if_false,
    Bool.not_false,Bool.not_true] at hF hopp
  · have hh := mul_nonneg S.hd.le hopp
    have hh' := congrArg (fun z : ℝ => S.b*z) hF
    nlinarith only [hh,hh',S.hb,S.hd]
  · have hh := mul_nonneg S.hb.le hopp
    have hh' := congrArg (fun z : ℝ => S.d*z) hF
    nlinarith only [hh,hh',S.hb,S.hd]

def edge (S : Shape) (i j : Bool) : Point →ᵃ[ℝ] ℝ :=
  direction ((S.X i)⁻¹,(S.Y j)⁻¹)

theorem edge_apply (S : Shape) (i j : Bool) (x : Point) :
    edge S i j x = x.1/S.X i+x.2/S.Y j := by
  simp [edge,dot,div_eq_mul_inv,mul_comm]

theorem edge_bound (S : Shape) (i j : Bool) : ∀ x ∈ S.body, edge S i j x ≤ 1 := by
  intro x hx
  rw [edge_apply]
  exact body_support S i j hx

theorem edge_x (S : Shape) (i j : Bool) : edge S i j (S.X i,0) = 1 := by
  simp [edge_apply,S.X_ne]

theorem edge_y (S : Shape) (i j : Bool) : edge S i j (0,S.Y j) = 1 := by
  simp [edge_apply,S.Y_ne]

theorem edge_x_opposite (S : Shape) (i j : Bool) : edge S (!i) j (S.X i,0) < 1 := by
  rw [edge_apply,zero_div,add_zero]
  have hh : S.X i/S.X (!i) < 0 := by
    cases i <;> simp only [Shape.X,if_true,Bool.false_eq_true,if_false,Bool.not_false,Bool.not_true]
    · exact div_neg_of_neg_of_pos (neg_neg_of_pos S.hc) S.ha
    · exact div_neg_of_pos_of_neg S.ha (neg_neg_of_pos S.hc)
  linarith only [hh]

theorem edge_y_opposite (S : Shape) (i j : Bool) : edge S i (!j) (0,S.Y j) < 1 := by
  rw [edge_apply,zero_div,zero_add]
  have hh : S.Y j/S.Y (!j) < 0 := by
    cases j <;> simp only [Shape.Y,if_true,Bool.false_eq_true,if_false,Bool.not_false,Bool.not_true]
    · exact div_neg_of_neg_of_pos (neg_neg_of_pos S.hd) S.hb
    · exact div_neg_of_pos_of_neg S.hb (neg_neg_of_pos S.hd)
  linarith only [hh]

/-- The physical second band obtained by contracting a tight vertical band. -/
def band (S : Shape) (a : Point) (r s : ℝ) : Set Point :=
  {x | r*a.1-s*S.c ≤ x.1 ∧ x.1 ≤ r*a.1+s*S.a}

theorem band_apex_lower (S : Shape) (i : Bool) (r s : ℝ) {x : Point}
    (hx : x ∈ band S (S.X i,0) r s) :
    r+(1-r-s)*xLevel S i 0 ≤ xLevel S i x := by
  have hd := add_pos S.ha S.hc
  cases i
  · change r*(-S.c)-s*S.c ≤ x.1 ∧ x.1 ≤ r*(-S.c)+s*S.a at hx
    simp only [xLevel_apply,Bool.false_eq_true,if_false,Prod.fst_zero,sub_zero]
    calc
      r+(1-r-s)*(S.a/(S.a+S.c)) = (S.a-(-r*S.c+s*S.a))/(S.a+S.c) := by field_simp; ring
      _ ≤ (S.a-x.1)/(S.a+S.c) := div_le_div_of_nonneg_right (by linarith only [hx.2]) hd.le
  · change r*S.a-s*S.c ≤ x.1 ∧ x.1 ≤ r*S.a+s*S.a at hx
    simp only [xLevel_apply,if_true,Prod.fst_zero,zero_add]
    calc
      r+(1-r-s)*(S.c/(S.a+S.c)) = (r*S.a-s*S.c+S.c)/(S.a+S.c) := by field_simp; ring
      _ ≤ (x.1+S.c)/(S.a+S.c) := div_le_div_of_nonneg_right (by linarith only [hx.1]) hd.le

theorem band_base_upper (S : Shape) (i j : Bool) (r s : ℝ) {x : Point}
    (hx : x ∈ band S (0,S.Y j) r s) :
    xLevel S i x ≤ xLevel S i 0+s*(1-xLevel S i 0) := by
  change r*0-s*S.c ≤ x.1 ∧ x.1 ≤ r*0+s*S.a at hx
  have hd := add_pos S.ha S.hc
  cases i
  · simp only [xLevel_apply,Bool.false_eq_true,if_false,Prod.fst_zero,sub_zero]
    calc
      (S.a-x.1)/(S.a+S.c) ≤ (S.a+s*S.c)/(S.a+S.c) :=
        div_le_div_of_nonneg_right (by linarith only [hx.1]) hd.le
      _ = S.a/(S.a+S.c)+s*(1-S.a/(S.a+S.c)) := by field_simp; ring
  · simp only [xLevel_apply,if_true,Prod.fst_zero,zero_add]
    calc
      (x.1+S.c)/(S.a+S.c) ≤ (s*S.a+S.c)/(S.a+S.c) :=
        div_le_div_of_nonneg_right (by linarith only [hx.2]) hd.le
      _ = S.c/(S.a+S.c)+s*(1-S.c/(S.a+S.c)) := by field_simp; ring

/-- No positive support strip can complete the cover needed by a second
tight diagonal strip on a genuine quadrilateral. This is a set obstruction,
not merely a scalar inequality. -/
theorem no_cover (S : Shape) (F : Point →ᵃ[ℝ] ℝ) (a : Point)
    (ha : a ∈ S.vertices) (hFa : F a = 1) (hF : ∀ x ∈ S.body, 0 ≤ F x)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hR : r+s < 1) :
    ¬S.body ⊆ ({x | 0 ≤ F x ∧ F x ≤ r} ∪ band S a r s) ∪
      (AffineMap.homothety a (1-r) '' S.body) := by
  have hapex (i : Bool) (hi : a = (S.X i,0)) :
      ∃ x ∈ S.body, r < F x ∧ x ∉ band S a r s ∧
        x ∉ AffineMap.homothety a (1-r) '' S.body := by
    subst a
    obtain ⟨j,hj⟩ := some_y_ge S F
    have hm := zero_x_mix S F i
    rw [hFa,mul_one] at hm
    obtain ⟨x,hx,hFx,hGx,hHx⟩ := apex_obstruction (convex_body S) F (xLevel S i)
      (edge S (!i) j) (S.X i,0) (S.X (!i),0) (0,S.Y j)
      (vertexX_mem S i) (vertexX_mem S (!i)) (vertexY_mem S j) hFa
      (hF _ (vertexX_mem S (!i))) (level_vertex S i) (level_opposite S i)
      (xLevel S i 0) r s (level_pos S i) (level_lt_one S i) (level_y S i j)
      (by rwa [← hm]) hr hs hR (edge_x_opposite S i j) (edge_x S (!i) j)
      (edge_y S (!i) j) (edge_bound S (!i) j)
    exact ⟨x,hx,hFx,fun hh => (not_lt_of_ge (band_apex_lower S i r s hh)) hGx,hHx⟩
  have hbase (j : Bool) (hj : a = (0,S.Y j)) :
      ∃ x ∈ S.body, r < F x ∧ x ∉ band S a r s ∧
        x ∉ AffineMap.homothety a (1-r) '' S.body := by
    subst a
    have hf0 := zero_pos_of_y S F j hFa (hF _ (vertexY_mem S (!j)))
    obtain ⟨i,hi⟩ := some_x_ge S F
    obtain ⟨x,hx,hFx,hGx,hHx⟩ := base_obstruction (convex_body S) F (xLevel S i)
      (edge S i (!j)) (0,S.Y j) (S.X i,0) (vertexY_mem S j) (vertexX_mem S i)
      hFa (hf0.trans_le hi) (xLevel S i 0) r s (level_lt_one S i)
      (level_y S i j) (level_vertex S i) hr hs.le hR (edge_y_opposite S i j)
      (edge_x S i (!j)) (edge_bound S i (!j))
    exact ⟨x,hx,hFx,fun hh => (not_lt_of_ge (band_base_upper S i j r s hh)) hGx,hHx⟩
  have hex : ∃ x ∈ S.body, r < F x ∧ x ∉ band S a r s ∧
      x ∉ AffineMap.homothety a (1-r) '' S.body := by
    rcases ha with h | h | h | h
    · exact hapex true h
    · exact hbase true h
    · exact hapex false h
    · exact hbase false h
  obtain ⟨x,hx,hFx,hBx,hHx⟩ := hex
  intro hcover
  rcases hcover hx with (hf | hb) | hh
  · exact (not_lt_of_ge hf.2) hFx
  · exact hBx hb
  · exact hHx hh

end Quant.CrossedQuadrilateralSupportGeometry

/-- info: 'Quant.CrossedQuadrilateralSupportGeometry.no_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralSupportGeometry.no_cover
