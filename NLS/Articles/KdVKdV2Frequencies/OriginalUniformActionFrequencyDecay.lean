import NLS.Articles.KdVKdV2Frequencies.UniformFrequencyActionModel
import NLS.Articles.KdVKdV2Frequencies.OriginalSharpActionFrequencyBounds

/-! Uniform sharp tails of the FULL corrected frequency in the ORIGINAL
raw weighted action norm and on full complex neighborhoods. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_original_uniform_action_frequency_decay
    (D : GlobalRoughAbelianForwardData) (t α : ℝ) (ht : 0<t) (ht1 : t<2/3) (hαt : 2*t-1=α)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a₀ : WeightedCoeff (Weight.sobolev α) 1) (ha₀ : a₀∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev α) 1), IsOpen U ∧ a₀∈U ∧
      (∀ a∈U, weakActionEnumeration (weakActionNormalization
        (WeightedCoeff.sobolevInclusion (by rw [← hαt];linarith : -1≤α) a))∈V) ∧
      (∀ n, AnalyticOnNhd ℂ (originalSobolevRenormalizedFrequency α (by rw [← hαt];linarith) G n) U) ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        Weight.sobolev (3*t-1) (n:ℤ)*‖originalSobolevRenormalizedFrequency α
          (by rw [← hαt];linarith) G n a‖≤ε := by
  have hα : -1≤α := by rw [← hαt];linarith
  exact exists_uniform_frequency_action_model_decay D t α ht ht1 hαt G V hV hCV hG hrec
    (sobolevActionEnumeration α) (originalSobolevRenormalizedFrequency α hα G)
    (fun n a => originalSobolevRenormalizedFrequency_eq_normalized α hα G n a)
    (fun a => weakActionEnumeration (weakActionNormalization (WeightedCoeff.sobolevInclusion hα a)))
    (fun a => normalizedSobolevWeakActionInclusion_enumeration α hα a) a₀
    (sobolevActionEnumeration_nonnegative α a₀ ha₀.1)

end NLS.Articles.KdVKdV2Frequencies
