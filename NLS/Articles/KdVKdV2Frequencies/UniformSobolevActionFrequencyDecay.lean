import NLS.Articles.KdVKdV2Frequencies.SobolevUniformFrequencyPairCharts
import NLS.Articles.KdVKdV2Frequencies.ComplexSobolevFrequencyAgreement
import NLS.SequenceSpaces.UniformFrequencyTransfer

/-! The SAME global weak frequency has sharp uniform corrected tails
on full complex normalized Sobolev action neighborhoods, including zero
coordinates and arbitrary infinite supports. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_uniform_sobolev_action_frequency_decay
    (D : GlobalRoughAbelianForwardData) (t α : ℝ) (ht : 0<t) (ht1 : t<2/3) (hαt : 2*t-1=α)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a₀ : Coeff 1) (ha₀ : a₀∈Coeff.nonnegativeLocus 1) :
    ∃ U : Set (Coeff 1), IsOpen U ∧ a₀∈U ∧
      U⊆normalizedSobolevWeakActionInclusion α (by rw [← hαt];linarith) ⁻¹' V ∧
      (∀ n, AnalyticOnNhd ℂ (normalizedSobolevRenormalizedFrequency α (by rw [← hαt];linarith) G n) U) ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs →
        Weight.sobolev (3*t-1) (n:ℤ)*‖normalizedSobolevRenormalizedFrequency α
          (by rw [← hαt];linarith) G n a‖≤ε := by
  subst α
  obtain ⟨z₀,hzr,hza,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (q := 1)
    (by norm_num) a₀ ha₀
  obtain ⟨P,hzP⟩ := exists_sobolevUniformFrequencyPairChart D t ht ht1 z₀ hzr
  obtain ⟨ρ,hρ,hsub,hqV,hagree⟩ := exists_complex_sobolev_frequency_agreement D P.physical t ht.le
    G V hV hCV hG hrec P.roughPotential P.domain P.domain_open P.rough_real P.rough_zero P.rough_mem
    P.rough_signed P.correction P.analytic_correction P.actual_correction z₀ hzP hzr
  obtain ⟨U,hU,haU,himage,hb⟩ := Coeff.quadratic_action_image_uniform_frequency_tail
    (ball z₀ ρ) isOpen_ball z₀ (mem_ball_self hρ) P.correction
    (normalizedSobolevRenormalizedFrequency (2*t-1) (by linarith) G) hagree
    (Weight.sobolev (3*t-1)) (by
      intro ε hε
      obtain ⟨K,hK⟩ := P.uniform_tail ε hε
      exact ⟨K,fun z hz n hn => hK z (hsub hz) n hn⟩)
  have hUV : U⊆normalizedSobolevWeakActionInclusion (2*t-1) (by linarith) ⁻¹' V := by
    intro a ha
    rw [himage] at ha
    obtain ⟨z,hz,rfl⟩ := ha
    exact hqV z hz
  rw [hza] at haU
  exact ⟨U,hU,haU,hUV,(fun n => (normalizedSobolevRenormalizedFrequency_analytic
    (2*t-1) (by linarith) G V hG n).mono hUV),hb⟩

end NLS.Articles.KdVKdV2Frequencies
