/- Exact removal of a sharp band on the far edge of a triangle. -/
module
public import Plank.Proofs.Quant.TriangleFarEndpoint
public import Plank.Proofs.Quant.TriangleMixedPair
public import Plank.Proofs.Quant.TriangleEdgeReduction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.TriangleFarReduction
open Set MeasureTheory Proofs.Basic Proofs.Transport
open CrossedQuadrilateralAttainment CommonMiddleNullWindow
open Plank.Convex.DeficientHeightTilt
open scoped BigOperators

def farTriangle : Triangle :=
  ⟨stdTriangle.B,stdTriangle.C,stdTriangle.A,by
    have he : ({stdTriangle.B,stdTriangle.C,stdTriangle.A} : Set Point)=
        {stdTriangle.A,stdTriangle.B,stdTriangle.C} := by
      ext z
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto
    rw [he]
    exact stdTriangle.not_collinear⟩

theorem farTriangle_set : farTriangle.set=stdTriangle.set := by
  ext z
  change (∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+b+c=1 ∧
    z=a • stdTriangle.B+b • stdTriangle.C+c • stdTriangle.A) ↔
    (∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+b+c=1 ∧
    z=a • stdTriangle.A+b • stdTriangle.B+c • stdTriangle.C)
  constructor
  · rintro ⟨a,b,c,ha,hb,hc,hs,hz⟩
    exact ⟨c,a,b,hc,ha,hb,by linarith only [hs],by rw [hz]; abel⟩
  · rintro ⟨a,b,c,ha,hb,hc,hs,hz⟩
    exact ⟨b,c,a,hb,hc,ha,by linarith only [hs],by rw [hz]; abel⟩

def farForm : Point →ᵃ[ℝ] ℝ := AffineMap.const ℝ Point 1-direction (1,1)

theorem farForm_apply (z : Point) : farForm z=1-(z.1+z.2) := by
  simp [farForm,dot]

theorem range_normalized (u : Point) (hu : 0 ≤ u.1 ∧ 0 ≤ u.2)
    (hm : max u.1 u.2=1) : rangeWidth stdTriangle.set (direction u)=1 := by
  have hx : u.1 ≤ 1 := hm ▸ le_max_left u.1 u.2
  have hy : u.2 ≤ 1 := hm ▸ le_max_right u.1 u.2
  have hb {z : Point} (hz : z ∈ stdTriangle.set) : 0 ≤ dot u z ∧ dot u z ≤ 1 := by
    rw [Proofs.Quant.stdTriangle_set_eq] at hz
    constructor
    · exact add_nonneg (mul_nonneg hu.1 hz.1) (mul_nonneg hu.2 hz.2.1)
    · calc
        dot u z ≤ z.1+z.2 := add_le_add
          (by nlinarith only [hx,hz.1]) (by nlinarith only [hy,hz.2.1])
        _ ≤ 1 := hz.2.2
  have hreal : ∃ z ∈ stdTriangle.set, dot u z=1 := by
    rcases le_total u.1 u.2 with h | h
    · refine ⟨stdTriangle.C,mem_C stdTriangle,?_⟩
      simpa [stdTriangle,dot,max_eq_right h] using hm
    · refine ⟨stdTriangle.B,mem_B stdTriangle,?_⟩
      simpa [stdTriangle,dot,max_eq_left h] using hm
  obtain ⟨z,hz,he⟩ := hreal
  have hw := Plank.Body.width_eq_of_realisers (f := direction u) hz (mem_A stdTriangle)
    (fun x hx => by change dot u x ≤ dot u z; rw [he]; exact (hb hx).2)
    (fun x hx => by simpa [stdTriangle,dot] using (hb hx).1)
  change rangeWidth stdTriangle.set (direction u)=dot u z-dot u stdTriangle.A at hw
  rw [he] at hw
  simpa [stdTriangle,dot] using hw

def pulled (p : Plank) (t : ℝ) (ht : t < 1) : Plank where
  u := p.u
  u_ne_zero := p.u_ne_zero
  lo := p.lo/(1-t)
  hi := p.hi/(1-t)
  lo_le_hi := (div_le_div_iff_of_pos_right (sub_pos.mpr ht)).mpr p.lo_le_hi

theorem pulled_width (p : Plank) (t : ℝ) (ht : t < 1) :
    (pulled p t ht).relWidth stdTriangle=p.relWidth stdTriangle/(1-t) := by
  simp only [Plank.relWidth,pulled]
  ring

theorem edge_width (C : Config) (hu2 : (C.plank 2).u=(1,1))
    (hh : (C.plank 2).hi=1) : C.relW 2=1-(C.plank 2).lo := by
  simp [Config.relW,Plank.relWidth,hu2,hh,Proofs.Transport.stdTriangle_width_eq]

/-- With the third band ending at the far edge, sharpness is exactly
sharpness of the original other two bands pulled through the remaining
triangle's homothety. Their individual widths scale by the same ratio. -/
theorem equality_iff_pulled (C : Config)
    (hu : ∀ i : Fin 2, 0 ≤ (C.plank i.castSucc).u.1 ∧ 0 ≤ (C.plank i.castSucc).u.2)
    (hm : ∀ i : Fin 2, max (C.plank i.castSucc).u.1 (C.plank i.castSucc).u.2=1)
    (hu2 : (C.plank 2).u=(1,1)) (hh : (C.plank 2).hi=1)
    (hδ : 0 < C.deficit) (ht : C.relW 2 < 1) :
    TriangleEqualityReductions.Equality C ↔
      pairGap (pulled (C.plank 0) (C.relW 2) ht) (pulled (C.plank 1) (C.relW 2) ht) =
        (1-((C.relW 0)/(1-C.relW 2)+(C.relW 1)/(1-C.relW 2)))^2*(1/2) := by
  have hw (i : Fin 2) : stdTriangle.width (C.plank i.castSucc).u=1 := by
    rw [Proofs.Transport.stdTriangle_width_eq,hm i,
      min_eq_left (le_min (hu i).1 (hu i).2)]
    norm_num
  have hwidth (i : Fin 2) : rangeWidth farTriangle.set (direction (C.plank i.castSucc).u)=1 := by
    rw [farTriangle_set]
    exact range_normalized _ (hu i) (hm i)
  have hrel (i : Fin 2) : C.relW i.castSucc=(C.plank i.castSucc).hi-(C.plank i.castSucc).lo := by
    simp only [Config.relW,Plank.relWidth,hw,div_one]
  have hsum : (∑ i : Fin 2, ((C.plank i.castSucc).hi-(C.plank i.castSucc).lo)/
      rangeWidth farTriangle.set (direction (C.plank i.castSucc).u))=C.relW 0+C.relW 1 := by
    simp only [hwidth,div_one,← hrel,Fin.sum_univ_two]
    rfl
  have hd : C.deficit=1-(C.relW 2+(C.relW 0+C.relW 1)) := by
    simp only [Config.deficit,Config.sumRelW,Fin.sum_univ_three]
    ring
  have hred := TriangleEdgeReduction.equality_iff_pulled farTriangle
    (farTriangle_set.symm ▸ Proofs.GapCells.isCompact_stdTriangle) farForm
    (by simp [farForm_apply,farTriangle,stdTriangle])
    (by simp [farForm_apply,farTriangle,stdTriangle])
    (by simp [farForm_apply,farTriangle,stdTriangle])
    (fun i : Fin 2 => direction (C.plank i.castSucc).u)
    (fun i => (C.plank i.castSucc).lo) (fun i => (C.plank i.castSucc).hi)
    (fun i => (C.plank i.castSucc).lo_le_hi) (by intro i; rw [hwidth]; norm_num)
    (C.relW 2) (by rw [edge_width C hu2 hh]; linarith [(C.plank 2).lo_le_hi])
    (by rw [hsum]; linarith only [hδ,hd])
  have hband : {z : Point | 0 ≤ farForm z ∧ farForm z ≤ C.relW 2}=(C.plank 2).set := by
    ext z
    change (0 ≤ farForm z ∧ farForm z ≤ C.relW 2) ↔
      ((C.plank 2).lo ≤ dot (C.plank 2).u z ∧ dot (C.plank 2).u z ≤ (C.plank 2).hi)
    rw [farForm_apply,edge_width C hu2 hh,hu2,hh]
    simp only [dot,one_mul]
    constructor <;> intro h <;> constructor <;> linarith only [h.1,h.2]
  have hgap : farTriangle.set \ ({z | 0 ≤ farForm z ∧ farForm z ≤ C.relW 2} ∪
      ⋃ i : Fin 2, {z | (C.plank i.castSucc).lo ≤ direction (C.plank i.castSucc).u z ∧
        direction (C.plank i.castSucc).u z ≤ (C.plank i.castSucc).hi})=C.uncovered := by
    rw [farTriangle_set,hband]
    ext z
    simp only [Config.uncovered,mem_sdiff,mem_union,mem_iUnion,Fin.exists_fin_succ,
      Fin.exists_fin_zero,or_false]
    change (z ∈ stdTriangle.set ∧ ¬(z ∈ (C.plank 2).set ∨
      z ∈ (C.plank 0).set ∨ z ∈ (C.plank 1).set)) ↔
      (z ∈ stdTriangle.set ∧ ¬(z ∈ (C.plank 0).set ∨
        z ∈ (C.plank 1).set ∨ z ∈ (C.plank 2).set))
    tauto
  have harea : (volume farTriangle.set).toReal=1/2 := by
    rw [farTriangle_set,Proofs.Quant.volume_stdTriangle,ENNReal.toReal_ofReal (by norm_num)]
  have hzero (i : Fin 2) : direction (C.plank i.castSucc).u farTriangle.C=0 := by
    simp [farTriangle,stdTriangle,dot]
  rw [hgap,hsum,harea] at hred
  simp only [hzero,mul_zero,sub_zero,hwidth,div_one] at hred
  rw [farTriangle_set] at hred
  have hsplit : (∑ i : Fin 2, ((C.plank i.castSucc).hi/(1-C.relW 2)-
      (C.plank i.castSucc).lo/(1-C.relW 2)))=
      C.relW 0/(1-C.relW 2)+C.relW 1/(1-C.relW 2) := by
    simp only [← sub_div,← hrel,Fin.sum_univ_two]
    rfl
  rw [hsplit] at hred
  have hpull : (stdTriangle.set \ ⋃ i : Fin 2,
      {z | (C.plank i.castSucc).lo/(1-C.relW 2) ≤ direction (C.plank i.castSucc).u z ∧
        direction (C.plank i.castSucc).u z ≤ (C.plank i.castSucc).hi/(1-C.relW 2)}) =
      stdTriangle.set \ ((pulled (C.plank 0) (C.relW 2) ht).set ∪
        (pulled (C.plank 1) (C.relW 2) ht).set) := by
    ext z
    simp only [mem_sdiff,mem_iUnion,Fin.exists_fin_two,mem_union]
    rfl
  rw [hpull] at hred
  have hleft : TriangleEqualityReductions.Equality C ↔
      C.gapArea=(1-C.relW 2-(C.relW 0+C.relW 1))^2*(1/2) := by
    unfold TriangleEqualityReductions.Equality
    rw [max_eq_right hδ.le,hd]
    congr 2
    ring
  exact hleft.trans hred

end Quant.TriangleFarReduction

/-- info: 'Quant.TriangleFarReduction.equality_iff_pulled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.TriangleFarReduction.equality_iff_pulled
