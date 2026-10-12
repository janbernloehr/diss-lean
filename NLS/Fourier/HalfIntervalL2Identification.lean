import NLS.Fourier.HalfIntervalBoundedness
import NLS.Fourier.PhysicalIntervalL2
import NLS.Fourier.ArbitraryPeriodBilinearParseval

/-!
# The completed half-interval map on arbitrary physical L² data

The normalized half-interval integral is represented by a bounded Hilbert
functional. Parseval identifies it on arbitrary interval L² functions, and
density of finite Fourier polynomials identifies it with the completed
half-interval coefficient map. No endpoint matching is required.
-/

noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate ENNReal
namespace NLS.Fourier

/-- Actual normalized unit-interval Fourier coefficients of arbitrary L² data. -/
def unitIntervalMemLpCoefficients (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) : Coeff 2 :=
  fourierBasis.repr (intervalL2Class (by norm_num : (0 : ℝ) < 1) f hf)

/-- Every coefficient is the original physical integral on the unit interval. -/
@[simp] theorem unitIntervalMemLpCoefficients_apply (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    unitIntervalMemLpCoefficients f hf n = intervalFourierCoefficient 1 f n := by
  rw [unitIntervalMemLpCoefficients, fourierBasis_repr, fourierCoeff_intervalL2Class]

/-- Finite period-one Fourier polynomials recover their exact raw coefficients. -/
theorem unitIntervalMemLpCoefficients_polynomial (a : ℤ →₀ ℂ) :
    unitIntervalMemLpCoefficients (polynomial a) (memLp_two_interval (continuous_polynomial a) 0 1 (by norm_num)) =
      Coeff.ofFinsupp a := by
  apply lp.ext
  funext n
  rw [unitIntervalMemLpCoefficients_apply,
    intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num), fourierCoeffOn_one, halfCoefficient_polynomial_even]
  change 2 * ((1/2 : ℂ) * a n) = a n
  ring

/-- A bounded Hilbert functional representing the normalized half-interval coefficient. -/
def halfCoefficientL2CLM (n : ℤ) : Coeff 2 →L[ℂ] ℂ :=
  (1/2 : ℂ) • innerSL ℂ (unitIntervalMemLpCoefficients (wave n)
    (memLp_two_interval (continuous_wave n) 0 1 (by norm_num)))

/-- Parseval identifies the functional with the actual physical half coefficient. -/
theorem halfCoefficientL2CLM_ofFunction (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    halfCoefficientL2CLM n (unitIntervalMemLpCoefficients f hf) = halfCoefficient f n := by
  let hw := memLp_two_interval (continuous_wave n) 0 1 (by norm_num : (0 : ℝ) ≤ 1)
  have hi := lp.hasSum_inner (𝕜 := ℂ) (unitIntervalMemLpCoefficients (wave n) hw)
    (unitIntervalMemLpCoefficients f hf)
  simp only [RCLike.inner_apply', unitIntervalMemLpCoefficients_apply, mul_comm] at hi
  have hp := hasSum_sesquilinear_intervalFourierCoefficient (by norm_num : (0 : ℝ) < 1) hf hw
  have he := hi.unique hp
  simp only [Complex.ofReal_one, inv_one, one_mul, ← wave_neg] at he
  change (1/2 : ℂ) * inner ℂ (unitIntervalMemLpCoefficients (wave n) hw)
    (unitIntervalMemLpCoefficients f hf) = _
  rw [he]
  rfl

/-- Density identifies the completed half-interval map with the Hilbert functional. -/
theorem halfIntervalCoeffs_two_apply (a : Coeff 2) (n : ℤ) :
    halfIntervalCoeffs (by norm_num : (1 : ℝ≥0∞) < 2) (by simp) a n = halfCoefficientL2CLM n a := by
  have h : (fun a : Coeff 2 => halfIntervalCoeffs (by norm_num) (by simp) a n) = halfCoefficientL2CLM n := by
    apply (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp (halfIntervalCoeffs (by norm_num) (by simp)).continuous)
      (halfCoefficientL2CLM n).continuous
    funext c
    change halfIntervalCoeffs (by norm_num) (by simp) (Coeff.ofFinsupp c) n =
      halfCoefficientL2CLM n (Coeff.ofFinsupp c)
    rw [halfIntervalCoeffs_finite_integral, ← unitIntervalMemLpCoefficients_polynomial c,
      halfCoefficientL2CLM_ofFunction]
  exact congrFun h a

/-- The completed map agrees with actual half-interval integrals for every L² input. -/
theorem halfIntervalCoeffs_two_ofFunction (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    halfIntervalCoeffs (by norm_num : (1 : ℝ≥0∞) < 2) (by simp) (unitIntervalMemLpCoefficients f hf) n =
      halfCoefficient f n := by
  rw [halfIntervalCoeffs_two_apply, halfCoefficientL2CLM_ofFunction]

end NLS.Fourier
