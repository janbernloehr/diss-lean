import NLS.Fourier.PeriodicSobolevConjugation
import NLS.SequenceSpaces.HilbertProductTame

/-!
# Explicit quadratic form bound for native H-minus-one potentials

All inputs and products are original periodic distributions. The true
H-minus-one norm and full H1 domain are used throughout. The shared
multiplicative Hilbert embedding controls the original quadratic product.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)]

/-- The original H1 distribution's unweighted normalized L2 coefficients. -/
def h1L2Coefficients (f : FourierLebesgueSpace L 1 2) : Coeff 2 :=
  WeightedCoeff.sobolevToL2 (by norm_num) (sobolevCoefficients 1 2 f)

@[simp] theorem h1L2Coefficients_apply (f : FourierLebesgueSpace L 1 2) (k : ℤ) :
    h1L2Coefficients f k = f.val (mode (-k)) := by
  simp only [h1L2Coefficients,WeightedCoeff.sobolevToL2_apply,sobolevCoefficients_apply]

/-- Forgetting one derivative decreases the exact original coefficient norm. -/
theorem norm_h1L2Coefficients_le (f : FourierLebesgueSpace L 1 2) : ‖h1L2Coefficients f‖ ≤ ‖f‖ := by
  simpa only [h1L2Coefficients,LinearIsometryEquiv.norm_map] using
    WeightedCoeff.norm_sobolevToL2_le (by norm_num) (sobolevCoefficients 1 2 f)

/-- The original H1 distribution's absolutely summable Fourier coefficients. -/
def h1L1Coefficients (f : FourierLebesgueSpace L 1 2) : Coeff 1 :=
  WeightedCoeff.sobolevToL1CLM 2 (by norm_num) (sobolevCoefficients 1 2 f)

@[simp] theorem h1L1Coefficients_apply (f : FourierLebesgueSpace L 1 2) (k : ℤ) :
    h1L1Coefficients f k = f.val (mode (-k)) := by
  simp only [h1L1Coefficients,WeightedCoeff.sobolevToL1CLM_apply,sobolevCoefficients_apply]

/-- Native physical conjugation agrees with the shared weighted coefficient conjugation. -/
theorem sobolevCoefficients_conjugation (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : FourierLebesgueSpace L s p) :
    sobolevCoefficients s p (sobolevConjugation s p f) =
      WeightedCoeff.conjugateReflection _ (Weight.sobolev_neg s) (sobolevCoefficients s p f) := by
  apply Subtype.ext
  funext k
  simp only [sobolevCoefficients_apply,sobolevConjugation_coefficient,
    WeightedCoeff.conjugateReflection_apply,neg_neg,Complex.star_def]

/-- Physical conjugation preserves the absolute Fourier sum. -/
theorem norm_h1L1Coefficients_conjugation (f : FourierLebesgueSpace L 1 2) :
    ‖h1L1Coefficients (sobolevConjugation 1 2 f)‖ = ‖h1L1Coefficients f‖ := by
  unfold h1L1Coefficients
  rw [sobolevCoefficients_conjugation,WeightedCoeff.norm_sobolevToL1_conjugateReflection]

/-- The shared Agmon estimate on the actual original H1 distribution. -/
theorem norm_h1L1Coefficients_sq_le (f : FourierLebesgueSpace L 1 2) :
    ‖h1L1Coefficients f‖^2 ≤ 12*‖h1L2Coefficients f‖*‖f‖ := by
  simpa only [h1L1Coefficients,h1L2Coefficients,LinearIsometryEquiv.norm_map] using
    WeightedCoeff.norm_sobolevToL1_sq_le (sobolevCoefficients 1 2 f)

/-- The native quadratic product has the tame original H1 bound. -/
theorem norm_h1Product_conjugate_le (f : FourierLebesgueSpace L 1 2) :
    ‖h1Product f (sobolevConjugation 1 2 f)‖ ≤ 3*‖f‖*‖h1L1Coefficients f‖ := by
  unfold h1Product
  rw [LinearIsometryEquiv.norm_map,sobolevCoefficients_conjugation]
  simpa only [LinearIsometryEquiv.norm_map,h1L1Coefficients] using
    WeightedCoeff.norm_sobolevConvolution_conjugate_le (by norm_num) (sobolevCoefficients 1 2 f)

/-- Full original duality bounds the native singular quadratic form by its tame product. -/
theorem norm_hminusOne_quadratic_le (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) :
    ‖sobolevDualIsometry 1 (by norm_num) (hminusOneProduct q f) (sobolevConjugation 1 2 f)‖ ≤
      3*‖q‖*‖f‖*‖h1L1Coefficients f‖ := by
  rw [hminusOneProduct_duality]
  apply ((sobolevDualIsometry 1 (by norm_num) q).le_opNorm _).trans
  rw [LinearIsometryEquiv.norm_map]
  exact (mul_le_mul_of_nonneg_left (norm_h1Product_conjugate_le f) (norm_nonneg q)).trans_eq (by ring)

/-- Every native H-minus-one potential admits this quarter-H1 form bound
on its entire original H1 domain, with an explicit quartic norm constant. -/
theorem norm_hminusOne_quadratic_le_quarter (q : FourierLebesgueSpace L (-1) 2)
    (f : FourierLebesgueSpace L 1 2) :
    ‖sobolevDualIsometry 1 (by norm_num) (hminusOneProduct q f) (sobolevConjugation 1 2 f)‖ ≤
      ‖f‖^2/4+93312*‖q‖^4*‖h1L2Coefficients f‖^2 := by
  have hform := norm_hminusOne_quadratic_le q f
  have hag := mul_le_mul_of_nonneg_left (norm_h1L1Coefficients_sq_le f) (show 0 ≤ 18*‖q‖^2 by positivity)
  have hfirst := sq_nonneg (‖f‖-12*‖q‖*‖h1L1Coefficients f‖)
  have hsecond := sq_nonneg (‖f‖-864*‖q‖^2*‖h1L2Coefficients f‖)
  nlinarith

end NLS.Fourier.PeriodicFourierLebesgue
