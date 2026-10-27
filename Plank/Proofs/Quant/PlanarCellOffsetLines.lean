/- Affine endpoint interpolation and closed feasibility for actual sign cells. -/
module

public import Plank.Proofs.Quant.PlanarInactiveCellMotion

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.PlanarCellOffsetLines

open Set PlanarQuantitative PlanarGapCells PlanarCellArea PlanarPlankCellCharts

variable {κ : Type*}

theorem cutOffsets_mix (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ)
    (p q : EndpointSpace κ) (a b : ℝ) (hab : a+b=1) :
    cutOffsets f (a • p+b • q).1 (a • p+b • q).2 s =
      a • cutOffsets f p.1 p.2 s+b • cutOffsets f q.1 q.2 s := by
  classical
  ext i
  by_cases hs : i ∈ s <;> simp only [cutOffsets,hs,if_true,if_false,
    Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  all_goals
    have hf : (a+b)*f i 0 = f i 0 := by rw [hab,one_mul]
    nlinarith only [hf]

theorem signCell_line (K : Set Point) (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ)
    (p z : EndpointSpace κ) (t : ℝ) :
    signCell K f (p+t • z).1 (p+t • z).2 s =
      cell K (cutForms f s) (cutOffsets f p.1 p.2 s+t • cutDirection z.1 z.2 s) := by
  rw [signCell_eq_cell]
  exact congrArg (cell K (cutForms f s)) (cutOffsets_motion f p.1 p.2 z.1 z.2 s t)

theorem isClosed_feasible_line [Fintype κ] {K : Set Point} (hK : IsCompact K)
    (f : κ → Point →ᵃ[ℝ] ℝ) (s : Finset κ) (p z : EndpointSpace κ) :
    IsClosed {t : ℝ | (signCell K f (p+t • z).1 (p+t • z).2 s).Nonempty} := by
  simp_rw [signCell_line]
  exact (PlanarInactiveCellMotion.isClosed_feasible hK (cutForms f s)).preimage (by fun_prop)

end Plank.PlanarCellOffsetLines
