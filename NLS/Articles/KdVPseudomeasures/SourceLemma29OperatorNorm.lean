import NLS.Articles.KdVPseudomeasures.SourceWeightedSpectral
import NLS.KdV.PseudomeasureWideOperatorErrors
import NLS.KdV.PseudomeasureWideAnalyticCoefficients

/-! The literal off-diagonal operator-norm estimates of Lemma 2.9(ii),
with the original weighted distributions and complete printed strip. -/
noncomputable section
open Set NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem analyticAt_sourceWeightedEndpointEntries_wide
    (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (n : ℕ) (hn : 2 ≤ n) (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (z : ℂ) (hz : z ∈ wideHillStrip n)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    AnalyticAt ℂ (fun p : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ × ℂ =>
      sourceEndpointEntries r hr n (sourceForgetWeight w r p.1,p.2)) (q,z) := by
  let P := ((sourceEndpointCoefficientsCLM r).comp (sourceForgetWeight w r)).prodMap
    (ContinuousLinearMap.id ℂ ℂ)
  have hsmall : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖(P (q,z)).1‖ ≤ 1/2 := by
    change 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*
      ‖sourceEndpointCoefficients r (sourceForgetWeight w r q)‖ ≤ 1/2
    rw [norm_sourceEndpointCoefficients]
    apply le_trans _ hs
    apply mul_le_mul_of_nonneg_left (norm_sourceForgetWeight_le w r q)
    exact mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
      (Real.rpow_nonneg (by positivity) _)
  obtain ⟨ha,hb,hc⟩ := analyticAt_endpointCoefficients_wide r hr.1 hr.2 n hn (P (q,z)) hz hsmall
  exact (ha.prod (hb.prod hc)).comp (f := P) (P.analyticAt (q,z))

/-- One cutoff precedes every source weight, every original complex
potential in its norm ball, and every parameter on the full printed strip.
The right sides use the actual conjugated operator norms. -/
theorem sourceLemma2_9_ii (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ (w : SpectralWeight)
      (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤), ‖q‖ ≤ R →
      ∀ (n : ℕ) (hn : 2 ≤ n), N ≤ n → ∀ (z : ℂ) (hz : z ∈ wideHillStrip n),
        AnalyticAt ℂ (fun p : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ × ℂ =>
          sourceEndpointEntries r hr n (sourceForgetWeight w r p.1,p.2)) (q,z) ∧
        w.negativeSobolev r (2*(n:ℤ))*
            ‖(sourceEndpointEntries r hr n (sourceForgetWeight w r q,z)).2.1-
              q.val (mode (-(2*(n:ℤ))))‖ ≤
          2*wideEndpointShiftedOperatorNorm w r hr.1 hr.2 n hn z hz
            (sourceWeightedEndpointCoefficients w r q) (n:ℤ)*‖q‖ ∧
        w.negativeSobolev r (2*(n:ℤ))*
            ‖(sourceEndpointEntries r hr n (sourceForgetWeight w r q,z)).2.2-
              q.val (mode (2*(n:ℤ)))‖ ≤
          2*wideEndpointShiftedOperatorNorm w r hr.1 hr.2 n hn z hz
            (sourceWeightedEndpointCoefficients w r q) (-(n:ℤ))*‖q‖ := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro w q hq n hn hNn z hz
  have hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hq
      (mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
        (Real.rpow_nonneg (by positivity) _))).trans (hcut n hNn)
  refine ⟨analyticAt_sourceWeightedEndpointEntries_wide w r hr n hn q z hz hs,?_⟩
  have h := wideEndpointCouplings_opNorm_errors w r hr.1 hr.2 n hn z hz
    (sourceWeightedEndpointCoefficients w r q) (by rwa [norm_sourceWeightedEndpointCoefficients])
  simpa only [sourceEndpointEntries, sourceEndpointCoefficients_forgetWeight,
    sourceWeightedEndpointCoefficients_apply, norm_sourceWeightedEndpointCoefficients, neg_neg] using h

end NLS.Articles.KdVPseudomeasures
