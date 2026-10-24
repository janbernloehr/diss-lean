import NLS.FunctionalAnalysis.RealPoissonKernel

/-! # Bounds for large heights and distant Poisson centers -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Set
namespace NLS.FunctionalAnalysis

/-- At positive height the kernel is bounded by its inverse height. -/
theorem realPoissonKernel_le_inv_height (x ε t : ℝ) (hε : 0 < ε) :
    realPoissonKernel x ε t ≤ 1/ε := by
  have hd : 0 < (x-t)^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  apply (div_le_div_iff₀ hd hε).mpr
  nlinarith [sq_nonneg (x-t)]

/-- A positive distance from the center bounds the kernel uniformly in height. -/
theorem realPoissonKernel_le_of_distance (x ε t δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (ht : δ ≤ |x-t|) : realPoissonKernel x ε t ≤ 1/(2*δ) := by
  have hd : 0 < (x-t)^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have hs : δ^2 ≤ (x-t)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hδ.le (abs_nonneg _)).mpr ht
  apply (div_le_div_iff₀ hd (by positivity)).mpr
  nlinarith [sq_nonneg (δ-ε)]

/-- The total mass controls Poisson integrals at large height. -/
theorem integral_realPoissonKernel_le_inv_height (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x ε : ℝ) (hε : 0 < ε) :
    (∫ t, realPoissonKernel x ε t ∂μ) ≤ μ.real univ / ε := by
  have h := integral_mono (integrable_realPoissonKernel μ x ε hε)
    (integrable_const (1/ε : ℝ)) (fun t => realPoissonKernel_le_inv_height x ε t hε)
  simpa only [integral_const,smul_eq_mul,div_eq_mul_inv,one_mul] using h

/-- Almost-everywhere distance of the support controls all positive heights. -/
theorem integral_realPoissonKernel_le_of_ae_distance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (ht : ∀ᵐ t ∂μ, δ ≤ |x-t|) :
    (∫ t, realPoissonKernel x ε t ∂μ) ≤ μ.real univ / (2*δ) := by
  have h := integral_mono_ae (integrable_realPoissonKernel μ x ε hε)
    (integrable_const (1/(2*δ) : ℝ))
    (ht.mono (fun t ht => realPoissonKernel_le_of_distance x ε t δ hε hδ ht))
  simpa only [integral_const,smul_eq_mul,div_eq_mul_inv,one_mul] using h

end NLS.FunctionalAnalysis
