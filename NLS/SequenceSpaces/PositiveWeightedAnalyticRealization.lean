import NLS.SequenceSpaces.PositiveScalarExtension
import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! Analytic positive-index coefficients with uniformly bounded actual
weighted realizations give a full Banach-valued analytic zero extension. -/
noncomputable section
open Set NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_positive_realization_of_bound (w : Weight) (f : E → ℕ+ → ℂ)
    {U : Set E} (hU : IsOpen U) (ha : ∀ n, AnalyticOnNhd ℂ (fun a => f a n) U)
    (M : ℝ) (hb : ∀ a ∈ U, ∃ b : WeightedCoeff w p,
      (∀ k, b.val k = positiveScalarExtension (f a) k) ∧ ‖b‖ ≤ M) :
    AnalyticOnNhd ℂ (fun a => ofFunctionOrZero w p (positiveScalarExtension (f a))) U := by
  apply (analytic_realization_of_bound w (fun a => positiveScalarExtension (f a)) hU ?_ M hb).1
  intro k
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨n,rfl⟩ := hk
    change AnalyticOnNhd ℂ (fun a => positiveScalarExtension (f a) ((n:ℕ):ℤ)) U
    simpa only [positiveScalarExtension_apply] using ha n
  · have he (a : E) : positiveScalarExtension (f a) k = 0 :=
      positiveScalarExtension_zero_of_not_mem_range (f a) k hk
    simp only [he]
    exact analyticOnNhd_const

end NLS.WeightedCoeff
