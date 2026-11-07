import NLS.Articles.KdVKdV2Frequencies.UniformSobolevActionFrequencyDecay

/-! Exact Banach action models inherit uniform tails of the same
global weak frequency. The source model stays opaque to kernel checking. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_uniform_frequency_action_model_decay
    (D : GlobalRoughAbelianForwardData) (t α : ℝ) (ht : 0<t) (ht1 : t<2/3) (hαt : 2*t-1=α)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (N : E →L[ℂ] Coeff 1) (f : ℕ+ → E → ℂ)
    (hfreq : ∀ n a, f n a=normalizedSobolevRenormalizedFrequency α (by rw [← hαt];linarith) G n (N a))
    (W : E → Coeff 1)
    (hweak : ∀ a, normalizedSobolevWeakActionInclusion α (by rw [← hαt];linarith) (N a)=W a)
    (a₀ : E) (ha₀ : N a₀∈Coeff.nonnegativeLocus 1) :
    ∃ U : Set E, IsOpen U ∧ a₀∈U ∧ (∀ a∈U, W a∈V) ∧
      (∀ n, AnalyticOnNhd ℂ (f n) U) ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        Weight.sobolev (3*t-1) (n:ℤ)*‖f n a‖≤ε := by
  have hα : -1≤α := by rw [← hαt];linarith
  obtain ⟨T,hT,haT,hTV,hFa,hb⟩ := exists_uniform_sobolev_action_frequency_decay
    D t α ht ht1 hαt G V hV hCV hG hrec (N a₀) ha₀
  obtain ⟨U,hU,haU,hUT,hUa,hUb⟩ := Coeff.exists_linear_uniform_frequency_tail_pullback N f
    (normalizedSobolevRenormalizedFrequency α hα G) hfreq T hT hFa a₀ haT (Weight.sobolev (3*t-1)) hb
  refine ⟨U,hU,haU,?_,hUa,hUb⟩
  intro a ha
  rw [← hweak]
  exact hTV (hUT ha)

end NLS.Articles.KdVKdV2Frequencies
