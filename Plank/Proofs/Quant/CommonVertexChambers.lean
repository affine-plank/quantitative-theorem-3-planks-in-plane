module
/-
# Quantitative chambers C and D share an extreme vertex

The common-vertex area theorem applies after reversing individual normals
and at most two rotations of the triangle. This file names the exact chamber
predicates; no covering theorem or positional restriction is used.
-/
public import Plank.Proofs.Quant.CommonVertex
public import Plank.Quant

@[expose] public section

noncomputable section

namespace Quant.CommonVertex

theorem coherent_rot_or_rot2 (u : ℝ × ℝ) :
    Coherent (rotDual u) ∨ Coherent (rotDual (rotDual u)) := by
  dsimp [Coherent, rotDual]
  by_cases hab : u.1 ≤ u.2
  · by_cases ha : u.1 ≤ 0
    · exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    · exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
  · by_cases ha : 0 ≤ u.1
    · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
    · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)

theorem coherent_rots_of_not {u : ℝ × ℝ} (hu : ¬ Coherent u) :
    Coherent (rotDual u) ∧ Coherent (rotDual (rotDual u)) := by
  by_cases ha : 0 ≤ u.1
  · have hb : u.2 < 0 := lt_of_not_ge fun hb => hu (Or.inl ⟨ha, hb⟩)
    dsimp [Coherent, rotDual]
    exact ⟨Or.inr ⟨by linarith, by linarith⟩,
      Or.inl ⟨by linarith, by linarith⟩⟩
  · have hb : 0 ≤ u.2 := by
      by_contra hb
      exact hu (Or.inr ⟨le_of_not_ge ha, le_of_not_ge hb⟩)
    dsimp [Coherent, rotDual]
    exact ⟨Or.inl ⟨by linarith, by linarith⟩,
      Or.inr ⟨by linarith, by linarith⟩⟩

/-- Two linear functionals always share an extreme vertex of a triangle. -/
theorem two_normals_share_extreme (u v : ℝ × ℝ) :
    (Coherent u ∧ Coherent v) ∨
    (Coherent (rotDual u) ∧ Coherent (rotDual v)) ∨
    (Coherent (rotDual (rotDual u)) ∧ Coherent (rotDual (rotDual v))) := by
  by_cases hu : Coherent u
  · by_cases hv : Coherent v
    · exact Or.inl ⟨hu, hv⟩
    · have hr := coherent_rots_of_not hv
      rcases coherent_rot_or_rot2 u with h | h
      · exact Or.inr (Or.inl ⟨h, hr.1⟩)
      · exact Or.inr (Or.inr ⟨h, hr.2⟩)
  · have hr := coherent_rots_of_not hu
    rcases coherent_rot_or_rot2 v with h | h
    · exact Or.inr (Or.inl ⟨hr.1, h⟩)
    · exact Or.inr (Or.inr ⟨hr.2, h⟩)

theorem coherent_of_boundary {u : ℝ × ℝ} (h : SectorBoundary u) : Coherent u := by
  obtain ⟨c, _, h | h | h⟩ := h <;>
    simpa [Coherent, h] using le_total (0 : ℝ) c

theorem coherent_of_closedAB {u : ℝ × ℝ} (h : ClosedSectorAB u) : Coherent u := by
  obtain ⟨c, b, hc, hb, _, h | h⟩ := h.form
  · exact Or.inl (by simpa [h] using And.intro hc.le (mul_nonneg hc.le hb))
  · exact Or.inr (by simpa [h] using And.intro hc.le (mul_nonneg hc.le hb))

theorem coherent_of_closedAC {u : ℝ × ℝ} (h : ClosedSectorAC u) : Coherent u := by
  obtain ⟨c, b, hc, hb, _, h | h⟩ := h.form
  · exact Or.inl (by simpa [h] using And.intro (mul_nonneg hc.le hb) hc.le)
  · exact Or.inr (by simpa [h] using And.intro (mul_nonneg hc.le hb) hc.le)

def CoherentRotation (C : Config) : Prop :=
  (∀ i, Coherent (C.plank i).u) ∨
  (∀ i, Coherent (rotDual (C.plank i).u)) ∨
  (∀ i, Coherent (rotDual (rotDual (C.plank i).u)))

theorem coherentRotation_of_chamberC {C : Config} (h : C.ChamberC) :
    CoherentRotation C := by
  obtain ⟨i, hi⟩ := h
  have h₀ := coherent_of_boundary hi
  have h₁ := coherent_of_boundary hi.dual.1
  have h₂ := coherent_of_boundary hi.dual.1.dual.1
  fin_cases i
  · rcases two_normals_share_extreme (C.plank 1).u (C.plank 2).u with
      ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl (Proofs.Symmetry.forall_fin_three h₀ ha hb)
    · exact Or.inr (Or.inl (Proofs.Symmetry.forall_fin_three h₁ ha hb))
    · exact Or.inr (Or.inr (Proofs.Symmetry.forall_fin_three h₂ ha hb))
  · rcases two_normals_share_extreme (C.plank 0).u (C.plank 2).u with
      ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl (Proofs.Symmetry.forall_fin_three ha h₀ hb)
    · exact Or.inr (Or.inl (Proofs.Symmetry.forall_fin_three ha h₁ hb))
    · exact Or.inr (Or.inr (Proofs.Symmetry.forall_fin_three ha h₂ hb))
  · rcases two_normals_share_extreme (C.plank 0).u (C.plank 1).u with
      ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Or.inl (Proofs.Symmetry.forall_fin_three ha hb h₀)
    · exact Or.inr (Or.inl (Proofs.Symmetry.forall_fin_three ha hb h₁))
    · exact Or.inr (Or.inr (Proofs.Symmetry.forall_fin_three ha hb h₂))

theorem coherentRotation_of_chamberD {C : Config} (h : C.ChamberD) :
    CoherentRotation C := by
  rcases h.2 with h | h | h
  · left
    intro i
    rcases h i with hi | hi
    · exact coherent_of_closedAB (Or.inl hi)
    · exact coherent_of_closedAC (Or.inl hi)
  · right; left
    intro i
    rcases h i with hi | hi
    · exact coherent_of_closedAC (Or.inl hi.rotDual)
    · exact coherent_of_closedAB (Or.inl hi.rotDual)
  · right; right
    intro i
    rcases h i with hi | hi
    · exact coherent_of_closedAB (Or.inl hi.rotDual.rotDual)
    · exact coherent_of_closedAC (Or.inl hi.rotDual.rotDual)

theorem rotDual_ne_zero {u : ℝ × ℝ} (hu : u ≠ 0) : rotDual u ≠ 0 := by
  intro h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [rotDual] at h₁ h₂
  exact hu (Prod.ext (by change u.1 = 0; linarith) (by change u.2 = 0; linarith))

def rotate (C : Config) : Config :=
  ⟨fun i => ⟨rotDual (C.plank i).u,
    (C.plank i).lo - (C.plank i).u.1,
    (C.plank i).hi - (C.plank i).u.1,
    rotDual_ne_zero (C.plank i).u_ne_zero,
    sub_le_sub_right (C.plank i).lo_le_hi _⟩⟩

theorem rotate_equiv (C : Config) : C.Equiv (rotate C) :=
  Relation.EqvGen.rel _ _ (Move.rot C (fun i => rotDual_ne_zero (C.plank i).u_ne_zero))

theorem sqBound_of_coherentRotation (C : Config) (h : CoherentRotation C)
    (hs : C.sumRelW ≤ 1) : C.SqBound := by
  rcases h with h | h | h
  · exact config_coherent_sqBound C h hs
  · have e := rotate_equiv C
    apply e.sqBound_iff.mpr
    apply config_coherent_sqBound (rotate C) h
    rw [← e.sumRelW_eq]
    exact hs
  · have e : C.Equiv (rotate (rotate C)) :=
      (rotate_equiv C).trans _ _ _ (rotate_equiv (rotate C))
    apply e.sqBound_iff.mpr
    apply config_coherent_sqBound (rotate (rotate C)) h
    rw [← e.sumRelW_eq]
    exact hs

/-- The full quantitative chamber-C statement, with arbitrary plank positions. -/
theorem chamberC_sqBound (C : Config) (h : C.ChamberC)
    (hs : C.sumRelW ≤ 1) : C.SqBound :=
  sqBound_of_coherentRotation C (coherentRotation_of_chamberC h) hs

/-- The full quantitative chamber-D statement, with arbitrary plank positions. -/
theorem chamberD_sqBound (C : Config) (h : C.ChamberD)
    (hs : C.sumRelW ≤ 1) : C.SqBound :=
  sqBound_of_coherentRotation C (coherentRotation_of_chamberD h) hs

theorem positive_square_bound_of_coherentRotation (C : Config)
    (h : CoherentRotation C) : (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea := by
  by_cases hs : C.sumRelW ≤ 1
  · have hb := sqBound_of_coherentRotation C h hs
    have hd : 0 ≤ C.deficit := by unfold Config.deficit; linarith
    rw [max_eq_right hd]
    change C.deficit ^ 2 * (1 / 2) ≤ C.gapArea at hb
    linarith
  · have hd : C.deficit ≤ 0 := by unfold Config.deficit; linarith
    rw [max_eq_left hd]
    simp [Config.gapArea]

theorem chamberC_positive_square_bound (C : Config) (h : C.ChamberC) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea :=
  positive_square_bound_of_coherentRotation C (coherentRotation_of_chamberC h)

theorem chamberD_positive_square_bound (C : Config) (h : C.ChamberD) :
    (max 0 C.deficit) ^ 2 / 2 ≤ C.gapArea :=
  positive_square_bound_of_coherentRotation C (coherentRotation_of_chamberD h)

/-- The unfolded `Quant.Cover.ChamberCArm` interface, without importing its
large assembly module. -/
theorem chamberC_moveOrbit_sqBound :
    ∀ C : Config, (∃ D, C.Equiv D ∧ D.ChamberC) ∧ C.sumRelW < 1 → C.SqBound := by
  rintro C ⟨⟨D, e, hD⟩, hs⟩
  apply e.sqBound_iff.mpr
  apply chamberC_sqBound D hD
  rw [← e.sumRelW_eq]
  exact hs.le

/-- The unfolded `Quant.Cover.ChamberDArm` interface. -/
theorem chamberD_moveOrbit_sqBound :
    ∀ C : Config, (∃ D, C.Equiv D ∧ D.ChamberD) ∧ C.sumRelW < 1 → C.SqBound := by
  rintro C ⟨⟨D, e, hD⟩, hs⟩
  apply e.sqBound_iff.mpr
  apply chamberD_sqBound D hD
  rw [← e.sumRelW_eq]
  exact hs.le

theorem coherentRotation_of_chamberT {C : Config} (h : C.ChamberT) :
    CoherentRotation C := by
  rcases h with h | h | h
  · exact Or.inl fun i => coherent_of_closedAB (Or.inl (h i))
  · exact Or.inl fun i => coherent_of_closedAC (Or.inl (h i))
  · exact Or.inr (Or.inl fun i => coherent_of_closedAB (Or.inl (h i).rotDual))

/-- The unrestricted sharp area bound is now reduced to the single open ABC
chamber. The ABC hypothesis remains substantive and is not proved here. -/
theorem sqPos_of_chamberE
    (hE : ∀ C : Config, C.ChamberE → C.sumRelW ≤ 1 → C.SqBound) :
    ∀ C : Config, Quant.SqPos C := by
  intro C
  apply Quant.sqPos_of_lt_one
  intro hs
  obtain ⟨D, e, hT | hC | hD | hDE⟩ := Config.exists_chamber C
  · apply e.sqBound_iff.mpr
    apply sqBound_of_coherentRotation D (coherentRotation_of_chamberT hT)
    rw [← e.sumRelW_eq]
    exact hs.le
  · apply e.sqBound_iff.mpr
    apply chamberC_sqBound D hC
    rw [← e.sumRelW_eq]
    exact hs.le
  · apply e.sqBound_iff.mpr
    apply chamberD_sqBound D hD
    rw [← e.sumRelW_eq]
    exact hs.le
  · apply e.sqBound_iff.mpr
    apply hE D hDE
    rw [← e.sumRelW_eq]
    exact hs.le

end Quant.CommonVertex
