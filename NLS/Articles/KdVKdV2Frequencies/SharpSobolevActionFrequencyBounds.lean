import NLS.Articles.KdVKdV2Frequencies.ComplexSobolevFrequencyAgreement
import NLS.Articles.KdVKdV2Frequencies.SobolevSharpFrequencyPairCharts
import NLS.SequenceSpaces.QuadraticFrequencyDecayTransfer

/-! The SAME global weak physical frequency has its sharp bounds
on full COMPLEX Sobolev action neighborhoods at EVERY nonnegative base.
All infinite action supports and all closed coordinates are included. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_sharp_sobolev_action_frequency_bounds
    (D : GlobalRoughAbelianForwardData) (t θ α : ℝ) (ht : 0≤t) (hθ : 0≤θ) (hθ1 : θ≤2/3) (hθt : θ≤t) (hαt : 2*t-1=α)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a₀ : Coeff 1) (ha₀ : a₀∈Coeff.nonnegativeLocus 1) :
    ∃ U : Set (Coeff 1), IsOpen U ∧ a₀∈U ∧
      U⊆normalizedSobolevWeakActionInclusion (α) (by rw [← hαt];linarith) ⁻¹' V ∧
      (∀ n, AnalyticOnNhd ℂ (normalizedSobolevRenormalizedFrequency (α) (by rw [← hαt];linarith) G n) U) ∧
      ∃ K : ℕ, ∃ M : ℝ, 0≤M ∧
        (∀ a∈U, ∀ n : ℕ+, K≤(n:ℤ).natAbs → Weight.sobolev (3*θ-1) (n:ℤ)*
          ‖normalizedSobolevRenormalizedFrequency (α) (by rw [← hαt];linarith) G n a‖≤M) ∧
        (θ<2/3 → ∀ a∈U, Tendsto (fun n : ℕ => Weight.sobolev (3*θ-1) ((n+1:ℕ):ℤ)*
          ‖normalizedSobolevRenormalizedFrequency (α) (by rw [← hαt];linarith) G ⟨n+1,by omega⟩ a‖) atTop (𝓝 0)) := by
  subst α
  obtain ⟨z₀,hzr,hza,_hnorm⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (q := 1)
    (by norm_num) a₀ ha₀
  obtain ⟨P,hzP⟩ := exists_sobolevSharpFrequencyPairChart D t θ ht hθ hθ1 hθt z₀ hzr
  obtain ⟨ρ,hρ,hsub,hqV,hagree⟩ := exists_complex_sobolev_frequency_agreement D P.physical t ht
    G V hV hCV hG hrec P.roughPotential P.domain P.domain_open P.rough_real P.rough_zero P.rough_mem
    P.rough_signed P.correction P.analytic_correction P.actual_correction z₀ hzP hzr
  obtain ⟨U,hU,haU,himage,hb,hd⟩ := Coeff.quadratic_action_image_frequency_decay
    (ball z₀ ρ) isOpen_ball z₀ (mem_ball_self hρ) P.correction
    (normalizedSobolevRenormalizedFrequency (2*t-1) (by linarith) G) hagree
    (Weight.sobolev (3*θ-1)) P.cutoff P.bound
    (fun z hz n hn => P.frequency_bound z (hsub hz) n hn)
  have hUV : U⊆normalizedSobolevWeakActionInclusion (2*t-1) (by linarith) ⁻¹' V := by
    intro a ha
    rw [himage] at ha
    obtain ⟨z,hz,rfl⟩ := ha
    exact hqV z hz
  rw [hza] at haU
  exact ⟨U,hU,haU,hUV,(fun n => (normalizedSobolevRenormalizedFrequency_analytic
    (2*t-1) (by linarith) G V hG n).mono hUV),P.cutoff,P.bound,P.bound_nonneg,hb,
    (fun ht2 => hd (fun z hz => P.pointwise_tail ht2 z (hsub hz)))⟩

end NLS.Articles.KdVKdV2Frequencies
