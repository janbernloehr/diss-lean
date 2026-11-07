import NLS.Articles.KdVPseudomeasures.SourceWideStripContraction
import NLS.Articles.KdVPseudomeasures.SpectralResolvent
import NLS.KdV.PseudomeasureWideReduction

/-! Lemma 2.7 on the complete printed strip, with a uniform cutoff and
the full original H1 eigenvector domain. -/
noncomputable section
open Set NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem sourceLemma2_7_wide (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2≤N ∧
      ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖≤R →
      ∀ (n : ℕ) (hn : 2≤n), N≤n → ∀ (z : ℂ) (hz : z ∈ printedHillStrip n),
      ∃ hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2,
        (wideEndpointHillReducedOperator r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q) hs).toLinearMap.det=0 ↔
          ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f≠0 ∧
            singularHillOperator (sourceComplexHminusOne r hr q) f=z • singularHillDomainInclusion f := by
  obtain ⟨N,hN,hcut⟩ := exists_wideEndpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn hNn z hz
  have hC : 0 ≤ 13*endpointHillConstant r*(n:ℝ)^(r-1/2) :=
    mul_nonneg (mul_nonneg (by norm_num) (endpointHillConstant_pos r hr.2).le)
      (Real.rpow_nonneg (by positivity) _)
  have hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    rw [norm_sourceEndpointCoefficients]
    exact (mul_le_mul_of_nonneg_left hq hC).trans (hcut n hNn)
  refine ⟨hs,?_⟩
  simpa only [sourceEndpointCoefficients_HminusOne_complex r hr] using
    wideEndpointHillReduced_det_eq_zero_iff r hr.1 hr.2 n hn z hz (sourceEndpointCoefficients r q) hs

end NLS.Articles.KdVPseudomeasures
