import NLS.SequenceSpaces.NegativeModulation
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Convolution between opposite Sobolev orders

A regular Wiener factor of order r multiplies an endpoint distribution of
order -r, with no loss of order. The construction is an absolutely summable
series in the original weighted Banach space, including infinity.
-/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted l1 norm for an arbitrary positive weight. -/
theorem hasSum_weighted_norm (w : Weight) (b : WeightedCoeff w 1) :
    HasSum (fun k => w k*‖b.val k‖) ‖b‖ := by
  have h := lp.hasSum_norm (p := 1) (by simp) (weightEquiv w 1 b)
  simpa only [weightEquiv_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (w.positive _), ENNReal.toReal_one, Real.rpow_one, ← norm_eq] using h

/-- Absolute Banach-space convergence of multiplication by a regular Wiener factor. -/
theorem summable_norm_signedSobolevConvolution_terms (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b : WeightedCoeff (Weight.sobolev r) 1) :
    Summable (fun k : ℤ => ‖b.val k • SpectralWeight.one.negativeModulation r hr k a‖) := by
  apply ((hasSum_weighted_norm _ b).summable.mul_right ‖a‖).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro k
  rw [norm_smul]
  calc
    _ ≤ ‖b.val k‖*(Weight.sobolev r k*‖a‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [SpectralWeight.one_apply, one_mul] using
        SpectralWeight.one.norm_negativeModulation_le r hr k a
    _ = _ := by ring

/-- Multiplication in signed Sobolev orders, defined by a genuine Banach series. -/
def signedSobolevConvolution (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b : WeightedCoeff (Weight.sobolev r) 1) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) p :=
  ∑' k : ℤ, b.val k • SpectralWeight.one.negativeModulation r hr k a

/-- The raw coefficients are the usual convergent convolution coefficients. -/
theorem signedSobolevConvolution_apply (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b : WeightedCoeff (Weight.sobolev r) 1) (n : ℤ) :
    (signedSobolevConvolution r hr a b).val n = ∑' k : ℤ, a.val (n-k)*b.val k := by
  change evalCLM _ p n (∑' k : ℤ, b.val k • SpectralWeight.one.negativeModulation r hr k a) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_norm_signedSobolevConvolution_terms r hr a b).of_norm]
  apply tsum_congr
  intro k
  simp only [map_smul, evalCLM_apply, SpectralWeight.negativeModulation_apply, smul_eq_mul]
  exact mul_comm _ _

/-- Exact opposite-order Young bound, including the infinity exponent. -/
theorem norm_signedSobolevConvolution_le (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b : WeightedCoeff (Weight.sobolev r) 1) :
    ‖signedSobolevConvolution r hr a b‖ ≤ ‖a‖*‖b‖ := by
  apply (norm_tsum_le_tsum_norm (summable_norm_signedSobolevConvolution_terms r hr a b)).trans
  calc
    _ ≤ ∑' k : ℤ, (Weight.sobolev r k*‖b.val k‖)*‖a‖ := by
      apply Summable.tsum_le_tsum _ (summable_norm_signedSobolevConvolution_terms r hr a b)
        ((hasSum_weighted_norm _ b).summable.mul_right ‖a‖)
      intro k
      rw [norm_smul]
      have h := mul_le_mul_of_nonneg_left
        (SpectralWeight.one.norm_negativeModulation_le r hr k a) (norm_nonneg (b.val k))
      simpa only [SpectralWeight.one_apply, one_mul, mul_left_comm, mul_assoc] using h
    _ = _ := by rw [tsum_mul_right, (hasSum_weighted_norm _ b).tsum_eq, mul_comm]

/-- The regular multiplier input acts linearly in the original signed space. -/
theorem signedSobolevConvolution_add_right (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b c : WeightedCoeff (Weight.sobolev r) 1) :
    signedSobolevConvolution r hr a (b+c) =
      signedSobolevConvolution r hr a b + signedSobolevConvolution r hr a c := by
  simp only [signedSobolevConvolution, add_val, add_smul]
  exact (summable_norm_signedSobolevConvolution_terms r hr a b).of_norm.tsum_add
    (summable_norm_signedSobolevConvolution_terms r hr a c).of_norm

/-- Complex linearity in the regular multiplier input. -/
theorem signedSobolevConvolution_smul_right (r : ℝ) (hr : 0 ≤ r) (c : ℂ)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b : WeightedCoeff (Weight.sobolev r) 1) :
    signedSobolevConvolution r hr a (c • b) = c • signedSobolevConvolution r hr a b := by
  simp only [signedSobolevConvolution, smul_val, mul_smul]
  exact (summable_norm_signedSobolevConvolution_terms r hr a b).of_norm.tsum_const_smul c

/-- Multiplication by a fixed negative-order distribution on the regular Wiener predual. -/
def signedSobolevConvolutionCLM (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p) :
    WeightedCoeff (Weight.sobolev r) 1 →L[ℂ]
      WeightedCoeff (SpectralWeight.one.negativeSobolev r) p :=
  LinearMap.mkContinuous
    { toFun := signedSobolevConvolution r hr a
      map_add' := signedSobolevConvolution_add_right r hr a
      map_smul' := fun c b => signedSobolevConvolution_smul_right r hr c a b }
    ‖a‖ (norm_signedSobolevConvolution_le r hr a)

@[simp] theorem signedSobolevConvolutionCLM_apply (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b : WeightedCoeff (Weight.sobolev r) 1) :
    signedSobolevConvolutionCLM r hr a b = signedSobolevConvolution r hr a b := rfl

/-- Linearity also holds in the distribution input of the actual Banach series. -/
theorem signedSobolevConvolution_add_left (r : ℝ) (hr : 0 ≤ r)
    (a c : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b : WeightedCoeff (Weight.sobolev r) 1) :
    signedSobolevConvolution r hr (a+c) b =
      signedSobolevConvolution r hr a b + signedSobolevConvolution r hr c b := by
  simp only [signedSobolevConvolution, map_add, smul_add]
  exact (summable_norm_signedSobolevConvolution_terms r hr a b).of_norm.tsum_add
    (summable_norm_signedSobolevConvolution_terms r hr c b).of_norm

/-- Complex linearity in the distribution input. -/
theorem signedSobolevConvolution_smul_left (r : ℝ) (hr : 0 ≤ r) (c : ℂ)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p)
    (b : WeightedCoeff (Weight.sobolev r) 1) :
    signedSobolevConvolution r hr (c • a) b = c • signedSobolevConvolution r hr a b := by
  simp only [signedSobolevConvolution, map_smul, smul_comm (b.val _) c]
  exact (summable_norm_signedSobolevConvolution_terms r hr a b).of_norm.tsum_const_smul c

/-- Bounded bilinear multiplication on opposite orders, retaining infinity. -/
def signedSobolevConvolutionBilinear (r : ℝ) (hr : 0 ≤ r) :
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) p →L[ℂ]
      WeightedCoeff (Weight.sobolev r) 1 →L[ℂ]
        WeightedCoeff (SpectralWeight.one.negativeSobolev r) p :=
  (LinearMap.mk₂ ℂ (signedSobolevConvolution r hr) (signedSobolevConvolution_add_left r hr)
    (fun c a b => signedSobolevConvolution_smul_left r hr c a b)
    (signedSobolevConvolution_add_right r hr)
    (fun c a b => signedSobolevConvolution_smul_right r hr c a b)).mkContinuous₂ 1
      (fun a b => by simpa only [LinearMap.mk₂_apply, one_mul] using
        norm_signedSobolevConvolution_le r hr a b)

/-- The analytic bilinear realization is exactly the existing fixed-input operator. -/
theorem signedSobolevConvolutionBilinear_eq (r : ℝ) (hr : 0 ≤ r)
    (a : WeightedCoeff (SpectralWeight.one.negativeSobolev r) p) :
    signedSobolevConvolutionBilinear r hr a = signedSobolevConvolutionCLM r hr a := by
  ext b
  rfl

end NLS.WeightedCoeff
