import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # Analytic sequence-valued slices

Continuity in the sequence norm upgrades scalar output analyticity on
an affine complex line to analyticity of the entire sequence-valued slice.
The result holds on the complete open preimage of the parameter domain.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {r : ℝ≥0∞} [Fact (1 ≤ r)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Scalar output analyticity at every center and continuity in norm give
sequence-valued analyticity along a fixed complex linear direction. -/
theorem analyticOnNhd_sequenceSlice
    (f : E → Coeff r) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (L : ℂ →L[ℂ] E)
    (ha : ∀ b ∈ U, ∀ n : ℤ, AnalyticAt ℂ (fun t : ℂ => f (b+L t) n) 0)
    (a : E) :
    AnalyticOnNhd ℂ (fun t : ℂ => f (a+L t)) ((fun t : ℂ => a+L t) ⁻¹' U) := by
  have hline : Continuous (fun t : ℂ => a+L t) := continuous_const.add L.continuous
  apply analyticOnNhd_of_coordinatewise_of_continuousOn _ (hU.preimage hline) _
    (hf.comp hline.continuousOn (fun _ ht => ht))
  intro n t ht
  have ht0 : AnalyticAt ℂ (fun v : ℂ => f (a+L t+L v) n) (t-t) := by
    simpa only [sub_self] using ha (a+L t) ht n
  have hshift : AnalyticAt ℂ (fun v : ℂ => v-t) t := analyticAt_id.sub analyticAt_const
  have he (v : ℂ) : a+L t+L (v-t) = a+L v := by rw [map_sub]; abel
  simpa only [Function.comp_def,he] using ht0.comp (f := fun v : ℂ => v-t) hshift

/-- The analytic line restriction at its center, in the full target norm. -/
theorem analyticAt_sequenceSlice
    (f : E → Coeff r) (U : Set E) (hU : IsOpen U) (hf : ContinuousOn f U)
    (L : ℂ →L[ℂ] E)
    (ha : ∀ b ∈ U, ∀ n : ℤ, AnalyticAt ℂ (fun t : ℂ => f (b+L t) n) 0)
    (a : E) (haU : a ∈ U) : AnalyticAt ℂ (fun t : ℂ => f (a+L t)) 0 :=
  analyticOnNhd_sequenceSlice f U hU hf L ha a 0 (by simpa using haU)

end NLS.Coeff
