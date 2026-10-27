/- Extreme-point selection on the compact set of minimizers. -/
module

public import Mathlib.Analysis.Convex.KreinMilman

@[expose] public section
set_option autoImplicit false
open Set

namespace ResearchFormalized.CompactMinimum

/-- If the boundary values exceed one value inside a compact domain, a minimum
can be chosen in its interior with no nonzero symmetric displacement among
minimizers. This is the extreme value theorem followed by the Krein--Milman
lemma on the minimum level set; neither the domain nor the function need be convex. -/
theorem exists_interior_minimum_no_motion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set E} (hD : IsCompact D) {f : E → ℝ} (hf : Continuous f) {b : ℝ}
    (hboundary : ∀ p ∈ D, p ∉ interior D → b ≤ f p)
    {p₀ : E} (hp₀ : p₀ ∈ D) (hbad : f p₀ < b) :
    ∃ p ∈ interior D, f p < b ∧ (∀ e ∈ D, f p ≤ f e) ∧
      ∀ z, p-z ∈ D ∩ f ⁻¹' {f p} → p+z ∈ D ∩ f ⁻¹' {f p} → z = 0 := by
  obtain ⟨a, ha, hamin⟩ := hD.exists_isMinOn ⟨p₀, hp₀⟩ hf.continuousOn
  have hZ : IsCompact (D ∩ f ⁻¹' {f a}) :=
    hD.inter_right (isClosed_singleton.preimage hf)
  obtain ⟨p, hp, hextreme⟩ := hZ.extremePoints_nonempty ⟨a, ha, rfl⟩
  have heq : f p = f a := hp.2
  have hneg : f p < b := (heq.trans_le (hamin hp₀)).trans_lt hbad
  refine ⟨p, by_contra fun hn => hneg.not_ge (hboundary p hp.1 hn), hneg,
    fun _ he => heq.trans_le (hamin he), ?_⟩
  intro z hm hp'
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  exact sub_eq_self.mp (hextreme ⟨hm.1, hm.2.trans heq⟩ ⟨hp'.1, hp'.2.trans heq⟩
    (mem_openSegment_sub_add (𝕜 := ℝ) p z))

end ResearchFormalized.CompactMinimum
