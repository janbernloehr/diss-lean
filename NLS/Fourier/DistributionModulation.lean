import NLS.Fourier.DistributionPeriodicity
import NLS.Fourier.AbsoluteContinuousCoefficients

/-!
# Actual smooth multiplication and Fourier shifts

Every physical Fourier wave is a smooth multiplier of Schwartz space. Mathlib's
multiplication of tempered distributions by that wave agrees with the existing
coefficient shift, with all signs in the period-two convention.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform ContDiff
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All orders of smoothness are available for the physical Fourier waves. -/
@[fun_prop] theorem contDiff_wave_infty (n : ℤ) : ContDiff ℝ ∞ (wave n) := by
  have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  unfold wave
  fun_prop

/-- Iterated physical derivatives retain the exact power of `iπn`. -/
theorem iteratedDeriv_wave (n : ℤ) (k : ℕ) :
    iteratedDeriv k (wave n) = fun x => (Complex.I * (Real.pi : ℂ) * n) ^ k * wave n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', deriv_wave]
    funext x
    rw [iteratedDeriv_const_mul_field, ih]
    simp [pow_succ, mul_assoc, mul_comm]

/-- Fourier waves have temperate growth, so distribution multiplication is genuine. -/
theorem wave_hasTemperateGrowth (n : ℤ) : (wave n).HasTemperateGrowth := by
  refine ⟨contDiff_wave_infty n, fun k => ⟨0, ‖Complex.I * (Real.pi : ℂ) * n‖ ^ k, ?_⟩⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_wave]
  simp [norm_pow, wave, Complex.norm_exp]

/-- Multiplication of a Schwartz test shifts its signed half-integer Fourier samples. -/
theorem fourier_sample_wave_mul (g : 𝓢(ℝ, ℂ)) (k n : ℤ) :
    (𝓕 (SchwartzMap.smulLeftCLM ℂ (wave k) g)) (-(n : ℝ) / 2) =
      (𝓕 g) (-((n + k : ℤ) : ℝ) / 2) := by
  rw [fourier_sample_eq_integral_wave, fourier_sample_eq_integral_wave]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [SchwartzMap.smulLeftCLM_apply_apply (wave_hasTemperateGrowth k), smul_eq_mul,
    wave_add, mul_assoc]

/-- The coefficient shift is precisely Mathlib's multiplication by the physical wave. -/
theorem distributionSynthesis_shift (a : Coeff p) (k : ℤ) :
    distributionSynthesis (Coeff.shift k a) =
      TemperedDistribution.smulLeftCLM ℂ (wave k) (distributionSynthesis a) := by
  ext g
  rw [TemperedDistribution.smulLeftCLM_apply_apply]
  simp only [distributionSynthesis_apply, Coeff.shift_apply, fourier_sample_wave_mul]
  have h := ((Equiv.addRight k).tsum_eq
    (fun n : ℤ => a (n - k) * (𝓕 g) (-(n : ℝ) / 2))).symm
  change (∑' n : ℤ, a (n - k) * (𝓕 g) (-(n : ℝ) / 2)) =
    ∑' n : ℤ, a ((n + k) - k) * (𝓕 g) (-((n + k : ℤ) : ℝ) / 2) at h
  simpa only [add_sub_cancel_right] using h

/-- A single right convolution factor multiplies the actual distribution by its wave. -/
theorem distributionSynthesis_convolution_single (a : Coeff p) (k : ℤ) (c : ℂ) :
    distributionSynthesis (Coeff.convolution a (lp.single 1 k c)) =
      c • TemperedDistribution.smulLeftCLM ℂ (wave k) (distributionSynthesis a) := by
  rw [Coeff.convolution_single_right]
  change distributionSynthesisCLM (c • Coeff.shift k a) = _
  rw [map_smul]
  exact congrArg (fun T : 𝓢'(ℝ, ℂ) => c • T) (distributionSynthesis_shift a k)

/-- A finite Fourier polynomial in the physical period-two variable. -/
def fourierPolynomial (s : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ s, b k * wave k x

theorem fourierPolynomial_hasTemperateGrowth (s : Finset ℤ) (b : ℤ → ℂ) :
    (fourierPolynomial s b).HasTemperateGrowth :=
  Function.HasTemperateGrowth.sum (fun k _ =>
    (Function.HasTemperateGrowth.const (b k)).mul (wave_hasTemperateGrowth k))

/-- The physical Fourier polynomial is exactly the continuous synthesis of truncated data. -/
theorem fourierPolynomial_eq_continuousSynthesis (s : Finset ℤ) (b : Coeff 1) (x : ℝ) :
    fourierPolynomial s b x = continuousSynthesis (Coeff.truncate s b) (x : AddCircle (2 : ℝ)) := by
  classical
  rw [continuousSynthesis_apply]
  simp only [Coeff.truncate_apply, ite_mul, zero_mul]
  rw [tsum_eq_sum (s := s) (by intro n hn; simp [hn])]
  exact Finset.sum_congr rfl (fun n hn => by simp [hn]) |>.symm

/-- Every finite Fourier multiplier agrees with ordinary smooth distribution multiplication. -/
theorem distributionSynthesis_convolution_truncate (a : Coeff p) (b : Coeff 1) (s : Finset ℤ) :
    distributionSynthesis (Coeff.convolution a (Coeff.truncate s b)) =
      TemperedDistribution.smulLeftCLM ℂ (fourierPolynomial s b) (distributionSynthesis a) := by
  classical
  have hc : Coeff.convolution a (Coeff.truncate s b) = ∑ k ∈ s, b k • Coeff.shift k a := by
    simp only [Coeff.convolution, Coeff.truncate_apply, ite_smul, zero_smul]
    rw [tsum_eq_sum (s := s) (by intro n hn; simp [hn])]
    exact Finset.sum_congr rfl (fun n hn => by simp [hn])
  rw [hc]
  change distributionSynthesisCLM (∑ k ∈ s, b k • Coeff.shift k a) = _
  rw [map_sum]
  simp only [map_smul, distributionSynthesisCLM_apply, distributionSynthesis_shift]
  unfold fourierPolynomial
  rw [TemperedDistribution.smulLeftCLM_sum (F := ℂ) (s := s)
    (g := fun k x => b k * wave k x)
    (fun k _ => (Function.HasTemperateGrowth.const (b k)).mul (wave_hasTemperateGrowth k))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (fun x : ℝ => b k * wave k x) = b k • wave k := rfl
  rw [he, TemperedDistribution.smulLeftCLM_smul (wave_hasTemperateGrowth k)]
  rfl

end NLS.Fourier
