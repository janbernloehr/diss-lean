import NLS.Articles.KdVPseudomeasures.SourceLemma29OperatorNorm
import NLS.Articles.KdVPseudomeasures.SourceWeightedDiagonalTransport
import NLS.KdV.HillWideDiagonalOppositeNorm

/-! Corrected Lemma 2.9(i): replace the printed unweighted potential norm
by its weighted norm. Both literal shifted operator norms, the entire 12n
strip, and one cutoff before every weight and potential in a norm ball are retained. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest
namespace NLS.Articles.KdVPseudomeasures

theorem sourceLemma2_9_i_weighted_at (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r) (n : ℕ) (hn : 2 ≤ n)
    (Q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hq0 : Q.val (mode 0)=0) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖Q‖ ≤ 1/2) :
    ‖(sourceEndpointEntries r hr n (sourceForgetWeight w r Q,z)).1‖ ≤
      2*wideEndpointShiftedOperatorNorm w r hr.1 hr.2 n hn z hz
        (sourceWeightedEndpointCoefficients w r Q) (n:ℤ)*‖Q‖ ∧
    ‖(sourceEndpointEntries r hr n (sourceForgetWeight w r Q,z)).1‖ ≤
      2*wideEndpointShiftedOperatorNorm w r hr.1 hr.2 n hn z hz
        (sourceWeightedEndpointCoefficients w r Q) (-(n:ℤ))*‖Q‖ := by
  have hqzero : (sourceWeightedEndpointCoefficients w r Q).val 0=0 := by
    simpa only [sourceWeightedEndpointCoefficients_apply,neg_zero] using hq0
  have hsmall : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*
      ‖sourceWeightedEndpointCoefficients w r Q‖ ≤ 1/2 := by
    rwa [norm_sourceWeightedEndpointCoefficients]
  rw [sourceEndpointDiagonal_forgetWeight]
  constructor
  · simpa only [norm_sourceWeightedEndpointCoefficients] using
      wideEndpointDiagonal_opNorm_le_weighted_opposite w r hr.1 hr.2 n hn z hz
        (sourceWeightedEndpointCoefficients w r Q) hsmall hqzero
  · simpa only [norm_sourceWeightedEndpointCoefficients] using
      wideEndpointDiagonal_opNorm_le_weighted w r hr.1 hr.2 n hn z hz
        (sourceWeightedEndpointCoefficients w r Q) hsmall hqzero

theorem sourceLemma2_9_i_weighted (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (w : SpectralWeight)
      (Q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤), ‖Q‖ ≤ R →
      Q.val (mode 0)=0 → ∀ (n : ℕ) (hn : 2 ≤ n), N ≤ n → ∀ (z : ℂ) (hz : z ∈ wideHillStrip n),
      AnalyticAt ℂ (fun p : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ × ℂ =>
        sourceEndpointEntries r hr n (sourceForgetWeight w r p.1,p.2)) (Q,z) ∧
      ‖(sourceEndpointEntries r hr n (sourceForgetWeight w r Q,z)).1‖ ≤
        2*wideEndpointShiftedOperatorNorm w r hr.1 hr.2 n hn z hz
          (sourceWeightedEndpointCoefficients w r Q) (n:ℤ)*‖Q‖ ∧
      ‖(sourceEndpointEntries r hr n (sourceForgetWeight w r Q,z)).1‖ ≤
        2*wideEndpointShiftedOperatorNorm w r hr.1 hr.2 n hn z hz
          (sourceWeightedEndpointCoefficients w r Q) (-(n:ℤ))*‖Q‖ := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro w Q hQ hq0 n hn hNn z hz
  have hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖Q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hQ
      (mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
        (Real.rpow_nonneg (by positivity) _))).trans (hcut n hNn)
  exact ⟨analyticAt_sourceWeightedEndpointEntries_wide w r hr n hn Q z hz hs,
    sourceLemma2_9_i_weighted_at w r hr n hn Q hq0 z hz hs⟩

end NLS.Articles.KdVPseudomeasures
