/- A geometric parametrization of the balanced cyclic equality family.
Choose an interior barycentric point. The three calibrated vertex bands
have relative widths proportional to the reciprocals of its coordinates.
This is an attainment theorem; global exhaustiveness is not asserted. -/
module

public import Plank.Proofs.Quant.CyclicEqualityFamily

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Quant.CyclicCevianFamily

open MeasureTheory CyclicWeightedThresholdGeometry CyclicThresholdCaps
  CyclicAnchorAlgebra SixTriangleAlgebra
open scoped BigOperators

def da (_u v w : ℝ) : ℝ := w / (v+w)
def db (u _v w : ℝ) : ℝ := u / (w+u)
def dc (u v _w : ℝ) : ℝ := v / (u+v)

def shares (u v w : ℝ) : Fin 3 → ℝ :=
  ![v*w/(u*v+v*w+w*u), u*w/(u*v+v*w+w*u), u*v/(u*v+v*w+w*u)]

def lower (u v w R : ℝ) (i : Fin 3) : ℝ :=
  (1-R*shares u v w i)*direction (da u v w) (db u v w) (dc u v w) i

def upper (u v w R : ℝ) (i : Fin 3) : ℝ :=
  lower u v w R i+R*shares u v w i

theorem directions_internal {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    (0 < da u v w ∧ da u v w < 1) ∧
    (0 < db u v w ∧ db u v w < 1) ∧
    (0 < dc u v w ∧ dc u v w < 1) := by
  refine ⟨⟨div_pos hw (add_pos hv hw), ?_⟩,
    ⟨div_pos hu (add_pos hw hu), ?_⟩, ⟨div_pos hv (add_pos hu hv), ?_⟩⟩
  · exact (div_lt_one (add_pos hv hw)).mpr (by linarith)
  · exact (div_lt_one (add_pos hw hu)).mpr (by linarith)
  · exact (div_lt_one (add_pos hu hv)).mpr (by linarith)

theorem balanced {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    da u v w*db u v w*dc u v w =
      (1-da u v w)*(1-db u v w)*(1-dc u v w) := by
  dsimp [da,db,dc]
  field_simp [(add_pos hv hw).ne', (add_pos hw hu).ne', (add_pos hu hv).ne']
  ring

/-- These are the three lines from a vertex through the chosen interior
point, in the existing cyclic affine coordinates. -/
theorem concurrent {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hsum : u+v+w = 1) (i : Fin 3) :
    value (da u v w) (db u v w) (dc u v w) i (u,v) =
      direction (da u v w) (db u v w) (dc u v w) i := by
  have hA := (add_pos hv hw).ne'
  have hB := (add_pos hw hu).ne'
  have hC := (add_pos hu hv).ne'
  fin_cases i <;> dsimp [value,direction,da,db,dc]
  · field_simp [hA]
    nlinarith only [hsum,congrArg (fun t : ℝ => v*t) hsum]
  · field_simp [hB]
    nlinarith only [hsum,congrArg (fun t : ℝ => u*t) hsum]
  · field_simp [hC]
    ring

/-- The positive shares sum to one, and share times barycentric coordinate
is independent of the vertex: equivalently the shares are proportional
to the reciprocal barycentric coordinates. -/
theorem shares_spec {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    (∀ i, 0 < shares u v w i) ∧ (∑ i, shares u v w i) = 1 ∧
      shares u v w 0*u = shares u v w 1*v ∧
      shares u v w 1*v = shares u v w 2*w := by
  have hS : 0 < u*v+v*w+w*u := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> dsimp [shares] <;> positivity
  · simp only [Fin.sum_univ_three]
    dsimp [shares]
    field_simp [hS.ne']
    ring
  · dsimp [shares]; ring
  · dsimp [shares]; ring

theorem shares_reciprocal {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (i : Fin 3) : shares u v w i = (![1/u,1/v,1/w] i)/(1/u+1/v+1/w) := by
  have hS : u*v+v*w+w*u ≠ 0 := ne_of_gt (by positivity)
  have hD : 1/u+1/v+1/w ≠ 0 := ne_of_gt (by positivity)
  fin_cases i <;> dsimp [shares] <;>
    field_simp [hu.ne',hv.ne',hw.ne',hS,hD] <;> ring

theorem anchor_calibration {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (i : Fin 3) :
    lowerAnchor (da u v w) (db u v w) (dc u v w) i =
        (1-shares u v w i)*direction (da u v w) (db u v w) (dc u v w) i ∧
      upperAnchor (da u v w) (db u v w) (dc u v w) i =
        (1-shares u v w i)*direction (da u v w) (db u v w) (dc u v w) i+
          shares u v w i := by
  have hA := (add_pos hv hw).ne'
  have hB := (add_pos hw hu).ne'
  have hC := (add_pos hu hv).ne'
  have hS : u*v+v*w+w*u ≠ 0 := ne_of_gt (by positivity)
  have hT : u+v+w ≠ 0 := ne_of_gt (by positivity)
  have hp : p (da u v w) (db u v w) (dc u v w) =
      (u+v+w)*(u*v+v*w+w*u)/((v+w)*(w+u)*(u+v)) := by
    dsimp [p,da,db,dc]
    field_simp [hA,hB,hC]
    ring
  have hq := (CyclicEqualityFamily.p_eq_q (balanced hu hv hw)).symm
  fin_cases i <;>
    simp only [lowerAnchor,upperAnchor,direction,weight,Fin.add_def] <;>
    rw [hq,hp] <;>
    dsimp [da,db,dc,k0,k1,k2,shares] <;> constructor <;>
    field_simp [hA,hB,hC,hS,hT] <;> ring

/-- The six endpoints are the elementary one-plank calibrated endpoints;
all the older rational anchor expressions have disappeared. -/
theorem endpoints_eq {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (R : ℝ) :
    lower u v w R = CyclicEqualityFamily.lower (da u v w) (db u v w) (dc u v w) R ∧
      upper u v w R = CyclicEqualityFamily.upper (da u v w) (db u v w) (dc u v w) R := by
  constructor <;> funext i
  · rw [CyclicEqualityFamily.lower,(anchor_calibration hu hv hw i).1]
    dsimp [lower]
    ring
  · rw [CyclicEqualityFamily.upper,(anchor_calibration hu hv hw i).2]
    dsimp [upper,lower]
    ring

/-- Actual uncovered area for the geometric cevian construction. No
clipping, covering, stationarity or scalar-area hypothesis is required. -/
theorem uncovered_area {u v w R : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hR : 0 < R) (hR1 : R < 1) :
    (volume (CyclicExteriorAssembly.uncovered (da u v w) (db u v w) (dc u v w)
      (lower u v w R) (upper u v w R))).toReal = (1-R)^2/2 := by
  obtain ⟨ha,hb,hc⟩ := directions_internal hu hv hw
  rw [(endpoints_eq hu hv hw R).1,(endpoints_eq hu hv hw R).2]
  exact CyclicEqualityFamily.area_family ha hb hc (balanced hu hv hw) hR hR1

theorem total_width {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (R : ℝ) :
    (∑ i, (upper u v w R i-lower u v w R i)) = R := by
  simp only [upper,add_sub_cancel_left]
  rw [← Finset.mul_sum,(shares_spec hu hv hw).2.1,mul_one]

/-- Every balanced strict cyclic direction triple comes from exactly the
kind of interior point used above. Thus this geometric parametrization
does not discard any member of the previously proved balanced family. -/
theorem exists_barycentric {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (_hc : 0 < c ∧ c < 1)
    (hbal : a*b*c = (1-a)*(1-b)*(1-c)) :
    ∃ u v w : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u+v+w = 1 ∧
      a = da u v w ∧ b = db u v w ∧ c = dc u v w := by
  let k := 1-b+a*b
  have hk : 0 < k := add_pos (sub_pos.mpr hb.2) (mul_pos ha.1 hb.1)
  let u := a*b/k
  let v := (1-a)*(1-b)/k
  let w := a*(1-b)/k
  have hu : 0 < u := div_pos (mul_pos ha.1 hb.1) hk
  have hv : 0 < v := div_pos (mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hb.2)) hk
  have hw : 0 < w := div_pos (mul_pos ha.1 (sub_pos.mpr hb.2)) hk
  have hsum : u+v+w = 1 := by
    dsimp [u,v,w]
    field_simp [hk.ne']
    dsimp [k]
    ring
  have hA : v+w = (1-b)/k := by dsimp [v,w]; ring
  have hB : w+u = a/k := by dsimp [w,u]; ring
  have hC : u+v = (a*b+(1-a)*(1-b))/k := by dsimp [u,v]; ring
  have hD : a*b+(1-a)*(1-b) ≠ 0 := ne_of_gt (add_pos (mul_pos ha.1 hb.1)
    (mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hb.2)))
  refine ⟨u,v,w,hu,hv,hw,hsum,?_,?_,?_⟩
  · rw [da,hA]
    dsimp [w]
    field_simp [hk.ne',(sub_pos.mpr hb.2).ne']
  · rw [db,hB]
    dsimp [u]
    field_simp [hk.ne',ha.1.ne']
  · rw [dc,hC]
    dsimp [v]
    field_simp [hk.ne',hD]
    nlinarith only [hbal]

/-- An actual-area geometric catalogue for the entire no-clipping cyclic
stratum: choose an interior point and the total width; no direction-balance
equation remains to be solved. The regional premise is explicit. -/
theorem equality_iff_cevians {a b c : ℝ} (ha : 0 < a ∧ a < 1)
    (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (l h : Fin 3 → ℝ) (H : CyclicUnclippedEquality.NoClippingRegion a b c l h)
    (hδ : 0 < SixTriangleResidual.deficit l h) :
    (volume (CyclicExteriorAssembly.uncovered a b c l h)).toReal =
        (SixTriangleResidual.deficit l h)^2/2 ↔
      ∃ u v w R : ℝ, 0 < u ∧ 0 < v ∧ 0 < w ∧ u+v+w = 1 ∧
        a = da u v w ∧ b = db u v w ∧ c = dc u v w ∧
        0 < R ∧ R < 1 ∧ l = lower u v w R ∧ h = upper u v w R := by
  rw [CyclicEqualityFamily.area_equality_iff_family ha hb hc l h H hδ]
  constructor
  · rintro ⟨hbal,R,hR,hR1,hl,hh⟩
    obtain ⟨u,v,w,hu,hv,hw,hsum,ha',hb',hc'⟩ := exists_barycentric ha hb hc hbal
    refine ⟨u,v,w,R,hu,hv,hw,hsum,ha',hb',hc',hR,hR1,?_,?_⟩
    · rw [hl,ha',hb',hc',(endpoints_eq hu hv hw R).1]
    · rw [hh,ha',hb',hc',(endpoints_eq hu hv hw R).2]
  · rintro ⟨u,v,w,R,hu,hv,hw,_,ha',hb',hc',hR,hR1,hl,hh⟩
    rw [ha',hb',hc']
    exact ⟨balanced hu hv hw,R,hR,hR1,
      hl.trans (endpoints_eq hu hv hw R).1,hh.trans (endpoints_eq hu hv hw R).2⟩

end Quant.CyclicCevianFamily

/-- info: 'Quant.CyclicCevianFamily.concurrent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicCevianFamily.concurrent
/-- info: 'Quant.CyclicCevianFamily.uncovered_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicCevianFamily.uncovered_area
/-- info: 'Quant.CyclicCevianFamily.equality_iff_cevians' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CyclicCevianFamily.equality_iff_cevians
