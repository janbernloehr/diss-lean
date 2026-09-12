import NLS.Fourier.IntervalKernelLp
import NLS.SequenceSpaces.Convolution

/-!
# Ordinary and shifted discrete Hilbert kernels

The source convention is `Σ a(k)/(k-n)`. As a convolution kernel this is
`-1/j`, with its value at zero set to zero. Its difference from the shifted
kernel is absolutely summable, hence harmless for every Banach `ℓp` exponent.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier

/-- The ordinary discrete Hilbert convolution kernel, with zero diagonal. -/
def hilbertKernel (j : ℤ) : ℂ := -(j : ℂ)⁻¹

/-- The unnormalized shifted kernel obtained from interval extension. -/
def shiftedKernel (j : ℤ) : ℂ := -2 / (2 * j + 1)

/-- The absolutely summable correction from shifted to ordinary kernel. -/
def hilbertCorrection (j : ℤ) : ℂ := hilbertKernel j - shiftedKernel j

@[simp] theorem hilbertKernel_zero : hilbertKernel 0 = 0 := by simp [hilbertKernel]
@[simp] theorem hilbertCorrection_zero : hilbertCorrection 0 = 2 := by norm_num [hilbertCorrection, shiftedKernel]

theorem hilbertKernel_neg (j : ℤ) : hilbertKernel (-j) = -hilbertKernel j := by simp [hilbertKernel]

/-- Away from zero, subtraction improves the decay by one power. -/
theorem hilbertCorrection_of_ne_zero (j : ℤ) (hj : j ≠ 0) :
    hilbertCorrection j = -1 / ((j : ℂ) * (2 * j + 1)) := by
  have hj' : (j : ℂ) ≠ 0 := by exact_mod_cast hj
  have ho : 2 * (j : ℂ) + 1 ≠ 0 := by exact_mod_cast (show 2 * j + 1 ≠ 0 by omega)
  unfold hilbertCorrection hilbertKernel shiftedKernel
  rw [show -(j : ℂ)⁻¹ = (-1 : ℂ) / j by simp [div_eq_mul_inv], div_sub_div _ _ hj' ho]
  congr 1
  ring

/-- A reciprocal envelope puts the ordinary kernel in every `ℓp`, `p>1`. -/
theorem norm_hilbertKernel_le (j : ℤ) : ‖hilbertKernel j‖ ≤ 2 * (1 + |(j : ℝ)|)⁻¹ := by
  by_cases hj : j = 0
  · subst j
    norm_num
  have ha : 1 ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  rw [hilbertKernel, norm_neg, norm_inv, ← Complex.ofReal_intCast,
    Complex.norm_real, Real.norm_eq_abs, ← div_eq_mul_inv]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  linarith

theorem hilbertKernel_memlp {p : ℝ≥0∞} (hp : 1 < p) : Memℓp hilbertKernel p := by
  apply ((Weight.inverse_sobolev_one_memlp hp).norm.const_mul (2 : ℝ)).mono
  intro n
  simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, Weight.sobolev_apply,
    Real.rpow_one, abs_of_pos (by positivity : 0 < 1 + |(n : ℝ)|)] using norm_hilbertKernel_le n

/-- An explicit square-decay envelope for the kernel correction. -/
theorem norm_hilbertCorrection_le (j : ℤ) :
    ‖hilbertCorrection j‖ ≤ 4 / (1 + |(j : ℝ)|) ^ 2 := by
  by_cases hj : j = 0
  · subst j
    norm_num
  have ha : 1 ≤ |(j : ℝ)| := by exact_mod_cast Int.one_le_abs hj
  have hb : |(j : ℝ)| ≤ |((2 * j + 1 : ℤ) : ℝ)| := by
    have hi : |j| ≤ |2 * j + 1| := by
      by_cases h : 0 ≤ j
      · rw [abs_of_nonneg h, abs_of_nonneg (by omega)]
        omega
      · rw [abs_of_neg (by omega : j < 0), abs_of_neg (by omega : 2 * j + 1 < 0)]
        omega
    exact_mod_cast hi
  rw [hilbertCorrection_of_ne_zero j hj, norm_div, norm_neg, norm_one, norm_mul]
  have he : (2 * (j : ℂ) + 1) = ((2 * j + 1 : ℤ) : ℂ) := by push_cast; rfl
  rw [he, ← Complex.ofReal_intCast j, ← Complex.ofReal_intCast (2 * j + 1),
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  apply (div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by positivity)).mpr
  nlinarith

/-- The correction belongs to `ℓ1`, unlike either Hilbert kernel separately. -/
theorem hilbertCorrection_memlp_one : Memℓp hilbertCorrection 1 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one]
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) norm_hilbertCorrection_le
  simpa only [Real.rpow_two, mul_one_div] using
    (summable_inverse_bracket (by norm_num : (1 : ℝ) < 2)).mul_left 4

/-- The correction as a genuine absolutely summable sequence. -/
def hilbertCorrectionCoeffs : Coeff 1 := ⟨hilbertCorrection, hilbertCorrection_memlp_one⟩

@[simp] theorem hilbertCorrectionCoeffs_apply (j : ℤ) :
    hilbertCorrectionCoeffs j = hilbertCorrection j := rfl

/-- The same correction is bounded at all Banach exponents, including both endpoints. -/
def hilbertCorrectionCLM {p : ℝ≥0∞} [Fact (1 ≤ p)] : Coeff p →L[ℂ] Coeff p :=
  Coeff.convolutionCLM.flip hilbertCorrectionCoeffs

theorem norm_hilbertCorrectionCLM_apply_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : Coeff p) :
    ‖hilbertCorrectionCLM a‖ ≤ ‖a‖ * ‖hilbertCorrectionCoeffs‖ := Coeff.norm_convolution_le _ _

end NLS.Fourier
