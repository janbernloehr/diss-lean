import NLS.SequenceSpaces.CoefficientComplexification
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Compactness under coefficient complexification

A compact real-linear map on real coefficient sequences has compact
complexification. Conversely, a complex-linear operator is determined by
its restriction to real sequences, so compactness of that restriction is
enough. The proof uses the actual bounded real and imaginary projections.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Coeff.Complexification
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem isCompactOperator_complexifyLinear (f : RealCoeff p →L[ℝ] F)
    (hf : IsCompactOperator f) : IsCompactOperator (complexifyLinear f) := by
  have h := (hf.comp_clm (Coeff.reCLM p)).add
    ((hf.comp_clm (imCLM p)).smul I)
  exact h

/-- Restriction to the real coefficient form followed by complexification recovers the map. -/
theorem complexifyLinear_restriction (A : Coeff p →L[ℂ] F) :
    complexifyLinear ((A.restrictScalars ℝ).comp (RealCoeff.complexCLM p)) = A := by
  ext h
  change A (RealCoeff.complexCLM p (Coeff.reCLM p h)) +
    I • A (RealCoeff.complexCLM p (imCLM p h)) = A h
  rw [← map_smul, ← map_add]
  congr 1
  ext n
  change ((h n).re : ℂ) + I * ((h n).im : ℂ) = h n
  simpa only [mul_comm] using Complex.re_add_im (h n)

/-- Compactness on real coefficient directions implies compactness on all complex directions. -/
theorem isCompactOperator_of_real_restriction (A : Coeff p →L[ℂ] F)
    (hA : IsCompactOperator ((A.restrictScalars ℝ).comp (RealCoeff.complexCLM p))) :
    IsCompactOperator A := by
  rw [← complexifyLinear_restriction A]
  exact isCompactOperator_complexifyLinear _ hA

end NLS.Coeff.Complexification
