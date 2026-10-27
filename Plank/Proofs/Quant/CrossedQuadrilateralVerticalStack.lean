/- Three parallel pieces: exact adjacency and calibrated outer endpoints. -/
module
public import Plank.Proofs.Quant.CrossedQuadrilateralBandPresentation
public import Plank.Proofs.Quant.CrossedQuadrilateralCommonSupportCatalogue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Quant.CrossedQuadrilateralVerticalStack
open Set MeasureTheory CrossedQuadrilateralAttainment CrossedQuadrilateralPlacement
open CrossedQuadrilateralCommonSupport CrossedQuadrilateralDiagonalSplit CommonMiddleAffineTransport
open scoped BigOperators

def total (S : Shape) (l u : Fin 3 → ℝ) : ℝ := ∑ i, (u i-l i)/(S.a+S.c)
def family (l u : Fin 3 → ℝ) (ho : ∀ i, l i ≤ u i) : Fin 3 → Plank :=
  fun i => axisPlank false (l i) (u i) (ho i)

/-- The intervals tile the calibrated band with outer endpoints `-c R,a R`. -/
def Stack (S : Shape) (l u : Fin 3 → ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), l (σ 0) = -S.c*total S l u ∧
    u (σ 0) = l (σ 1) ∧ u (σ 1) = l (σ 2) ∧ u (σ 2) = S.a*total S l u

theorem family_budget (S : Shape) (l u : Fin 3 → ℝ) (ho : ∀ i, l i ≤ u i) :
    (∑ i, relativeWidth S (family l u ho i)) = total S l u := by
  apply Finset.sum_congr rfl
  intro i _
  exact (axisPlank_relative_width S (l i) (u i) 0 0 (ho i) le_rfl).1

theorem common (S : Shape) (l u : Fin 3 → ℝ) (ho : ∀ i, l i ≤ u i) :
    ∀ i, CommonSupports S (family l u ho i) := by
  intro i j
  cases j <;> dsimp [CommonExtremes,family,axisPlank,vector,half,Shape.Y,dot]
  all_goals constructor <;> linarith only [S.ha,S.hc]

theorem lower_axis (S : Shape) (l u : ℝ) (ho : l ≤ u) :
    lower (half S true) (axisPlank false l u ho) = (l+S.c)/(S.a+S.c) := by
  simp [lower,span,half,axisPlank,vector,dot]

theorem upper_axis (S : Shape) (l u : ℝ) (ho : l ≤ u) :
    upper (half S true) (axisPlank false l u ho) = (u+S.c)/(S.a+S.c) := by
  simp [upper,span,half,axisPlank,vector,dot]

theorem lower_calibrated (S : Shape) (x R : ℝ) :
    (x+S.c)/(S.a+S.c) = (1-R)*(S.c/(S.a+S.c)) ↔ x = -S.c*R := by
  rw [← mul_div_assoc,div_left_inj' (add_pos S.ha S.hc).ne']
  constructor <;> intro h <;> nlinarith only [h]

theorem upper_calibrated (S : Shape) (x R : ℝ) :
    (x+S.c)/(S.a+S.c) = (1-R)*(S.c/(S.a+S.c))+R ↔ x = S.a*R := by
  rw [div_eq_iff (add_pos S.ha S.hc).ne']
  have hc : ((1-R)*(S.c/(S.a+S.c))+R)*(S.a+S.c) = S.c+S.a*R := by
    field_simp [(add_pos S.ha S.hc).ne']
    ring
  rw [hc]
  constructor <;> intro h <;> linarith only [h]

theorem adjacent_iff_stack (S : Shape) (l u : Fin 3 → ℝ) (ho : ∀ i, l i ≤ u i) :
    CrossedQuadrilateralCommonSupportCatalogue.Adjacent S (family l u ho) ↔ Stack S l u := by
  unfold CrossedQuadrilateralCommonSupportCatalogue.Adjacent
  rw [family_budget]
  constructor
  · rintro ⟨_,σ,hl,ha,hb,hu⟩
    simp only [family,lower_axis,upper_axis] at hl ha hb hu
    exact ⟨σ,(lower_calibrated S _ _).mp hl,
      add_right_cancel ((div_left_inj' (add_pos S.ha S.hc).ne').mp ha),
      add_right_cancel ((div_left_inj' (add_pos S.ha S.hc).ne').mp hb),
      (upper_calibrated S _ _).mp hu⟩
  · rintro ⟨σ,hl,ha,hb,hu⟩
    refine ⟨fun _ => rfl,σ,?_,?_,?_,?_⟩
    all_goals simp only [family,lower_axis,upper_axis]
    · exact (lower_calibrated S _ _).mpr hl
    · rw [ha]
    · rw [hb]
    · exact (upper_calibrated S _ _).mpr hu

/-- Necessity and actual-area sufficiency, with arbitrary initial order and overlap. -/
theorem equality_iff_stack (S : Shape) (l u : Fin 3 → ℝ) (ho : ∀ i, l i < u i)
    (hR : total S l u < 1) :
    (volume (S.body \ ⋃ i, band false (l i) (u i))).toReal =
      (1-total S l u)^2*(volume S.body).toReal ↔ Stack S l u := by
  have hw (i) : 0 < relativeWidth S (family l u (fun i => (ho i).le) i) := by
    change 0 < relativeWidth S (axisPlank false (l i) (u i) (ho i).le)
    rw [(axisPlank_relative_width S (l i) (u i) 0 0 (ho i).le le_rfl).1]
    exact div_pos (sub_pos.mpr (ho i)) (add_pos S.ha S.hc)
  have hh := CrossedQuadrilateralCommonSupportCatalogue.equality_iff_adjacent S
    (family l u (fun i => (ho i).le)) (common S l u _) hw (by rwa [family_budget])
  rw [adjacent_iff_stack,family_budget] at hh
  simpa only [family,axisPlank_set] using hh

end Quant.CrossedQuadrilateralVerticalStack

/-- info: 'Quant.CrossedQuadrilateralVerticalStack.equality_iff_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Quant.CrossedQuadrilateralVerticalStack.equality_iff_stack
