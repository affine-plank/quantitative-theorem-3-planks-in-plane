/- Strict separation of adjacent cyclic bands follows from actual equality. -/
module
public import Plank.Proofs.Quant.TriangleCyclicEdgeSeeds
public import Plank.Proofs.Quant.CyclicBadThresholds

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleCyclicCompatibility
open Set CommonVertex OrdinalArea CyclicArea TriangleEqualityReductions
open TriangleCyclicEdgeSeeds CyclicBadThresholds CyclicThresholdCaps

theorem below_of_gap (p : Plank) (z : ℝ × ℝ) (hn : z ∉ p.set)
    (hh : dot p.u z ≤ p.hi) : dot p.u z < p.lo := by
  exact lt_of_not_ge (fun hl => hn ⟨hl,hh⟩)

theorem above_of_gap (p : Plank) (z : ℝ × ℝ) (hn : z ∉ p.set)
    (hl : p.lo ≤ dot p.u z) : p.hi < dot p.u z := by
  exact lt_of_not_ge (fun hh => hn ⟨hl,hh⟩)

theorem edge_inequalities (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    0 < (1-b)*(1-(C.plank 1).hi)-(1-a)*(C.plank 0).hi+(1-a)*b ∧
    0 < (1-c)*(C.plank 0).lo+b*(C.plank 2).lo ∧
    0 < c*(C.plank 1).lo-a*(C.plank 2).hi := by
  obtain ⟨hm0,hm1,hm2⟩ := TriangleCyclicStrictVertices.abc_strict_middle
    C hb ha hc hu0 hu1 hu2 hp hδ he
  have hn {z : ℝ × ℝ} (hz : z ∈ C.uncovered) (i : Fin 3) :
      z ∉ (C.plank i).set := fun h => hz.2 (mem_iUnion.mpr ⟨i,h⟩)
  refine ⟨?_,?_,?_⟩
  · obtain ⟨z,hz,hedge⟩ := every_edge_has_gap C hb ha hc hu0 hu1 hu2 hδ he 2
    have hT := hz.1
    rw [Proofs.Quant.stdTriangle_set_eq] at hT
    change z.1+z.2=1 at hedge
    have hbz : b*(z.1+z.2)=b := by rw [hedge,mul_one]
    have haz : a*(z.1+z.2)=a := by rw [hedge,mul_one]
    have h0 := above_of_gap (C.plank 0) z (hn hz 0) (by
      rw [hu0]
      dsimp [dot]
      nlinarith only [hm0.1,hbz,mul_nonneg (sub_nonneg.mpr hb.2.le) hT.1])
    have h1 := above_of_gap (C.plank 1) z (hn hz 1) (by
      rw [hu1]
      dsimp [dot]
      nlinarith only [hm1.1,haz,mul_nonneg (sub_nonneg.mpr ha.2.le) hT.2.1])
    rw [hu0] at h0
    rw [hu1] at h1
    dsimp [dot] at h0 h1
    have hid : (1-a)*(z.1+b*z.2)+(1-b)*(a*z.1+z.2)=1-a*b := by
      calc
        _ = (1-a*b)*(z.1+z.2) := by ring
        _ = 1-a*b := by rw [hedge,mul_one]
    nlinarith only [hid,mul_lt_mul_of_pos_left h0 (sub_pos.mpr ha.2),
      mul_lt_mul_of_pos_left h1 (sub_pos.mpr hb.2)]
  · obtain ⟨z,hz,hedge⟩ := every_edge_has_gap C hb ha hc hu0 hu1 hu2 hδ he 1
    have hT := hz.1
    rw [Proofs.Quant.stdTriangle_set_eq] at hT
    change z.1=0 at hedge
    have hy : z.2 ≤ 1 := by linarith only [hT.2.2,hedge]
    have h0 := below_of_gap (C.plank 0) z (hn hz 0) (by
      rw [hu0]
      dsimp [dot]
      rw [hedge]
      nlinarith only [hm0.2,mul_le_mul_of_nonneg_left hy hb.1.le])
    have h2 := below_of_gap (C.plank 2) z (hn hz 2) (by
      rw [hu2]
      dsimp [dot]
      rw [hedge]
      nlinarith only [hm2.2,mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hc.2.le) hT.2.1])
    rw [hu0] at h0
    rw [hu2] at h2
    dsimp [dot] at h0 h2
    rw [hedge] at h0 h2
    nlinarith only [mul_lt_mul_of_pos_left h0 (sub_pos.mpr hc.2),
      mul_lt_mul_of_pos_left h2 hb.1]
  · obtain ⟨z,hz,hedge⟩ := every_edge_has_gap C hb ha hc hu0 hu1 hu2 hδ he 0
    have hT := hz.1
    rw [Proofs.Quant.stdTriangle_set_eq] at hT
    change z.2=0 at hedge
    have hx : z.1 ≤ 1 := by linarith only [hT.2.2,hedge]
    have h1 := below_of_gap (C.plank 1) z (hn hz 1) (by
      rw [hu1]
      dsimp [dot]
      rw [hedge]
      nlinarith only [hm1.2,mul_le_mul_of_nonneg_left hx ha.1.le])
    have h2 := above_of_gap (C.plank 2) z (hn hz 2) (by
      rw [hu2]
      dsimp [dot]
      rw [hedge]
      nlinarith only [hm2.1,mul_nonneg hc.1.le hT.1])
    rw [hu1] at h1
    rw [hu2] at h2
    dsimp [dot] at h1 h2
    rw [hedge] at h1 h2
    nlinarith only [mul_lt_mul_of_pos_left h1 hc.1,
      mul_lt_mul_of_pos_left h2 ha.1]

theorem endpoint_compatible (C : Config) {b a c : ℝ}
    (hb : 0 < b ∧ b < 1) (ha : 0 < a ∧ a < 1) (hc : 0 < c ∧ c < 1)
    (hu0 : (C.plank 0).u=(1,b)) (hu1 : (C.plank 1).u=(a,1))
    (hu2 : (C.plank 2).u=(c,c-1))
    (hp : ∀ i, 0 < C.relW i) (hδ : 0 < C.deficit) (he : Equality C) :
    ∀ i, 0 < (1-direction (1-a) b c (i+1))*lowerLevels C c i-
      direction (1-a) b c i*upperLevels C c (i+1)+
      direction (1-a) b c i*direction (1-a) b c (i+1) := by
  have hg := edge_inequalities C hb ha hc hu0 hu1 hu2 hp hδ he
  intro i
  fin_cases i <;> dsimp [direction,lowerLevels,upperLevels] <;>
    nlinarith only [hg.1,hg.2.1,hg.2.2]

end Quant.TriangleCyclicCompatibility

/-- info: 'Quant.TriangleCyclicCompatibility.endpoint_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleCyclicCompatibility.endpoint_compatible
