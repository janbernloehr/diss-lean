import NLS.SequenceSpaces.Convolution
import NLS.SequenceSpaces.SobolevEmbedding

/-!
# Potential multiplication on the Fourier coefficient domain

For `1 ≤ p < ∞`, a scalar potential in `Coeff p` multiplies a one-derivative
coefficient sequence into `Coeff p`, with a bound linear in both factors.

This is the Fourier-side multiplication estimate needed for the off-diagonal
part of the Zakharov–Shabat operator. Identification with physical-space
multiplication, and the full two-component operator, are separate milestones.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar one-derivative domain in Fourier coordinates. -/
abbrev ScalarDomain (p : ℝ≥0∞) := WeightedCoeff (Weight.sobolev 1) p

/-- Multiplication by a scalar potential, constructed by discrete convolution. -/
def potentialMul (hp : p ≠ ⊤) (φ : Coeff p) : ScalarDomain p →L[ℂ] Coeff p :=
  (Coeff.convolutionCLM φ).comp (WeightedCoeff.sobolevToL1CLM p hp)

/-- Coefficients of the product have the usual convolution formula. -/
theorem potentialMul_apply (hp : p ≠ ⊤) (φ : Coeff p) (f : ScalarDomain p) (n : ℤ) :
    potentialMul hp φ f n = ∑' k : ℤ, φ (n - k) * f.val k := by
  simp only [potentialMul, ContinuousLinearMap.comp_apply, Coeff.convolutionCLM_apply,
    Coeff.convolution_apply, WeightedCoeff.sobolevToL1CLM_apply]

/-- The multiplication estimate from Appendix A.8, with explicit dependence on `p`. -/
theorem norm_potentialMul_apply_le (hp : p ≠ ⊤) (φ : Coeff p) (f : ScalarDomain p) :
    ‖potentialMul hp φ f‖ ≤ WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖ * ‖f‖ := by
  calc
    ‖potentialMul hp φ f‖ ≤ ‖φ‖ * ‖WeightedCoeff.sobolevToL1CLM p hp f‖ :=
      Coeff.norm_convolution_le _ _
    _ ≤ ‖φ‖ * (WeightedCoeff.sobolevEmbeddingConstant p hp * ‖f‖) :=
      mul_le_mul_of_nonneg_left (WeightedCoeff.norm_sobolevToL1CLM_le p hp f) (norm_nonneg _)
    _ = _ := by ring

/-- The potential operator norm depends linearly on the potential norm. -/
theorem norm_potentialMul_le (hp : p ≠ ⊤) (φ : Coeff p) :
    ‖potentialMul hp φ‖ ≤ WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp) (norm_nonneg φ))
  exact norm_potentialMul_apply_le hp φ

/-- The constant unit potential leaves the input coefficients unchanged. -/
theorem potentialMul_unit_apply (hp : p ≠ ⊤) (f : ScalarDomain p) (n : ℤ) :
    potentialMul hp (lp.single p 0 1) f n = f.val n := by
  simp [potentialMul_apply, lp.single_apply, Pi.single_apply, sub_eq_zero]

end NLS.ZakharovShabat
