/- Four directional realizers align in an interior tight two-plank cover. -/
module
public import Plank.Convex.PlanarTight.TwoPlankAlgebra
public import Plank.Proofs.TwoPlankBody
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Plank.Convex.PlanarTight.TwoPlankContacts
open Plank.TwoPlankBody

/-- With both windows strictly internal and positive, the left/right
realizers have the same height and the bottom/top realizers have the same
horizontal coordinate. The last equations determine those coordinates
from the endpoints. Any choice of actual directional realizers works. -/
theorem realisers {E : Type*} (C : Coords E)
    (hl₁ : 0 < C.l1) (hu₁ : C.h1 < 1) (hl₂ : 0 < C.l2) (hu₂ : C.h2 < 1)
    (hw₂ : C.l2 < C.h2)
    (hsum : (C.h1 - C.l1) + (C.h2 - C.l2) = 1)
    (L R B T : E) (hL : L ∈ C.T) (hR : R ∈ C.T) (hB : B ∈ C.T) (hT : T ∈ C.T)
    (hXL : C.X L = 0) (hXR : C.X R = 1) (hYB : C.Y B = 0) (hYT : C.Y T = 1) :
    C.Y L = C.Y R ∧ C.X B = C.X T ∧
      (C.h1 - C.l1) * C.Y L = C.l2 ∧ (C.h2 - C.l2) * C.X B = C.l1 := by
  have hYL : C.l2 ≤ C.Y L ∧ C.Y L ≤ C.h2 := by
    rcases C.cov L hL with h | h
    · exact False.elim (by rw [hXL] at h; linarith only [h.1, hl₁])
    · exact h
  have hYR := C.in_H hu₁ hR hXR
  have hXB : C.l1 ≤ C.X B ∧ C.X B ≤ C.h1 := by
    rcases C.cov B hB with h | h
    · exact h
    · exact False.elim (by rw [hYB] at h; linarith only [h.1, hl₂])
  have hXT := C.in_V hu₂ hT hYT
  have kRU := C.corner_line hu₁ hu₂ hR hT hXR hYT
  have kLU := C.flipX.corner_line (by change 1 - C.l1 < 1; linarith only [hl₁])
    hu₂ hL hT (by change 1 - C.X L = 1; rw [hXL]; ring) hYT
  have kRD := C.flipY.corner_line hu₁ (by change 1 - C.l2 < 1; linarith only [hl₂])
    hR hB hXR (by change 1 - C.Y B = 1; rw [hYB]; ring)
  have kLD := C.flipX.flipY.corner_line
    (by change 1 - C.l1 < 1; linarith only [hl₁])
    (by change 1 - C.l2 < 1; linarith only [hl₂]) hL hB
    (by change 1 - C.X L = 1; rw [hXL]; ring)
    (by change 1 - C.Y B = 1; rw [hYB]; ring)
  dsimp only [Coords.flipX, Coords.flipY, Coords.swap] at kLU kRD kLD
  have hab : C.l1 + (1 - C.h1) = C.h2 - C.l2 := by linarith only [hsum]
  have hcd : C.l2 + (1 - C.h2) = C.h1 - C.l1 := by linarith only [hsum]
  have hc := TwoPlankAlgebra.contacts C.l1 (1 - C.h1) C.l2 (1 - C.h2)
    (C.Y L - C.l2) (C.Y R - C.l2) (C.X T - C.l1) (C.X B - C.l1)
    hl₁ (sub_pos.mpr hu₁) hl₂ (sub_pos.mpr hu₂)
    (sub_nonneg.mpr hYL.1) (by rw [hab]; linarith only [hYL.2])
    (sub_nonneg.mpr hYR.1) (by rw [hab]; linarith only [hYR.2])
    (sub_nonneg.mpr hXT.1) (by rw [hcd]; linarith only [hXT.2])
    (sub_nonneg.mpr hXB.1) (by rw [hcd]; linarith only [hXB.2])
    (by rw [hab]; nlinarith only [kLU])
    (by rw [hab, hcd]; nlinarith only [kRU])
    (by nlinarith only [kLD])
    (by rw [hcd]; nlinarith only [kRD])
  rw [hab, hcd] at hc
  obtain ⟨hLR, hheight, hbottom, htop⟩ := hc
  refine ⟨by linarith only [hLR], ?_, ?_, ?_⟩
  · have he := mul_left_cancel₀ (sub_pos.mpr hw₂).ne' (hbottom.trans htop.symm)
    linarith only [he]
  · have hwidth : C.h2 - C.l2 = 1 - (C.h1 - C.l1) := by linarith only [hsum]
    rw [hwidth] at hheight
    nlinarith only [hheight]
  · have hwidth : C.h1 - C.l1 = 1 - (C.h2 - C.l2) := by linarith only [hsum]
    rw [hwidth] at hbottom
    nlinarith only [hbottom]

end Plank.Convex.PlanarTight.TwoPlankContacts

/-- info: 'Plank.Convex.PlanarTight.TwoPlankContacts.realisers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plank.Convex.PlanarTight.TwoPlankContacts.realisers
