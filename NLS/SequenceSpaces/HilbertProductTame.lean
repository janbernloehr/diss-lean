import NLS.SequenceSpaces.SobolevConvolutionBounds
import NLS.SequenceSpaces.HilbertAgmon
import NLS.SequenceSpaces.ConjugateReflection

/-! # Tame original H1 multiplication and conjugate quadratic products -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One factor retains its absolute Fourier sum in the H1 product estimate. -/
theorem norm_sobolevConvolution_le_tame (hp : p ≠ ⊤)
    (a b : WeightedCoeff (Weight.sobolev 1) p) :
    ‖sobolevConvolution hp a b‖ ≤ 2*‖a‖*‖sobolevToL1CLM p hp b‖ +
      ‖b‖*‖sobolevToL1CLM p hp a‖ := by
  have hbase : ‖scalarInclusion (sobolevConvolution hp a b)‖ ≤ ‖a‖*‖sobolevToL1CLM p hp b‖ := by
    rw [scalarInclusion_sobolevConvolution]
    exact (Coeff.norm_convolution_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_scalarInclusion_le a) (norm_nonneg _))
  have hder : ‖derivative (sobolevConvolution hp a b)‖ ≤
      Real.pi*‖a‖*‖sobolevToL1CLM p hp b‖ + Real.pi*‖b‖*‖sobolevToL1CLM p hp a‖ := by
    rw [derivative_sobolevConvolution]
    apply (norm_add_le _ _).trans
    apply (add_le_add (Coeff.norm_convolution_le _ _) (Coeff.norm_youngConvolution_le _ _ _)).trans
    have ha := norm_derivative_le a
    have hb := norm_derivative_le b
    nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg (sobolevToL1CLM p hp b)),
      mul_le_mul_of_nonneg_left hb (norm_nonneg (sobolevToL1CLM p hp a))]
  apply (norm_sobolev_le_base_add_derivative _).trans
  apply (add_le_add hbase (mul_le_mul_of_nonneg_left hder (by positivity))).trans_eq
  field_simp
  ring

/-- Native coefficient conjugation preserves the absolute Fourier sum. -/
theorem norm_sobolevToL1_conjugateReflection (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    ‖sobolevToL1CLM p hp (conjugateReflection _ (Weight.sobolev_neg 1) a)‖ =
      ‖sobolevToL1CLM p hp a‖ := by
  have he : sobolevToL1CLM p hp (conjugateReflection _ (Weight.sobolev_neg 1) a) =
      star (Coeff.reflection (sobolevToL1CLM p hp a)) := by
    ext k
    change (sobolevToL1CLM p hp (conjugateReflection _ (Weight.sobolev_neg 1) a)) k =
      star (Coeff.reflection (sobolevToL1CLM p hp a) k)
    simp only [sobolevToL1CLM_apply,conjugateReflection_apply,Coeff.reflection_apply,Complex.star_def]
  rw [he,norm_star,Coeff.reflection.norm_map]

/-- The quadratic conjugate product has only one absolute Fourier-sum factor. -/
theorem norm_sobolevConvolution_conjugate_le (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    ‖sobolevConvolution hp a (conjugateReflection _ (Weight.sobolev_neg 1) a)‖ ≤
      3*‖a‖*‖sobolevToL1CLM p hp a‖ := by
  have h := norm_sobolevConvolution_le_tame hp a (conjugateReflection _ (Weight.sobolev_neg 1) a)
  rw [norm_conjugateReflection,norm_sobolevToL1_conjugateReflection] at h
  nlinarith

end NLS.WeightedCoeff
