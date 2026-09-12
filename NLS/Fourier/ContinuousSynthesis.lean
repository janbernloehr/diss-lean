import NLS.Fourier.IntervalParseval
import NLS.SequenceSpaces.Basic

/-!
# Continuous period-two Fourier synthesis

Absolutely summable coefficients define a uniformly convergent Fourier series.
The resulting continuous function has exactly the prescribed normalized Fourier
integrals. The circle has period two, so all integer modes, including odd ones,
are retained.
-/

noncomputable section
open MeasureTheory
namespace NLS.Fourier

instance periodTwoPositive : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

/-- Absolute convergence in the uniform norm. -/
theorem summable_norm_fourierTerms (a : Coeff 1) :
    Summable (fun n : ℤ => ‖a n • (fourier n : C(AddCircle (2 : ℝ), ℂ))‖) := by
  simpa only [norm_smul, fourier_norm, mul_one] using (lp.memℓp a).norm.summable_of_one

/-- The continuous sum of an absolutely convergent period-two Fourier series. -/
def continuousSynthesis (a : Coeff 1) : C(AddCircle (2 : ℝ), ℂ) :=
  ∑' n : ℤ, a n • fourier n

theorem hasSum_continuousSynthesis (a : Coeff 1) :
    HasSum (fun n : ℤ => a n • fourier n) (continuousSynthesis a) :=
  (summable_norm_fourierTerms a).of_norm.hasSum

/-- The uniform norm is bounded by the sum of the absolute coefficients. -/
theorem norm_continuousSynthesis_le (a : Coeff 1) : ‖continuousSynthesis a‖ ≤ ‖a‖ := by
  calc
    ‖continuousSynthesis a‖ ≤ ∑' n : ℤ, ‖a n • (fourier n : C(AddCircle (2 : ℝ), ℂ))‖ :=
      norm_tsum_le_tsum_norm (summable_norm_fourierTerms a)
    _ = ‖a‖ := by
      simpa only [norm_smul, fourier_norm, mul_one, ENNReal.toReal_one, Real.rpow_one] using
        (lp.hasSum_norm (p := 1) (by simp) a).tsum_eq

/-- Fourier synthesis as a bounded complex-linear map. -/
def continuousSynthesisCLM : Coeff 1 →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  LinearMap.mkContinuous
    { toFun := continuousSynthesis
      map_add' := fun a b => by
        change (∑' n, (a n + b n) • fourier n) = _
        simp_rw [add_smul]
        exact (summable_norm_fourierTerms a).of_norm.tsum_add
          (summable_norm_fourierTerms b).of_norm
      map_smul' := fun c a => by
        change (∑' n, (c * a n) • fourier n) = _
        simp_rw [mul_smul]
        exact (summable_norm_fourierTerms a).of_norm.tsum_const_smul c }
    1 (fun a => by simpa using norm_continuousSynthesis_le a)

@[simp] theorem continuousSynthesisCLM_apply (a : Coeff 1) :
    continuousSynthesisCLM a = continuousSynthesis a := rfl

/-- Continuous extraction of all square-summable Fourier coefficients. -/
def continuousFourierCLM : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] Coeff 2 :=
  fourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)

@[simp] theorem continuousFourierCLM_apply (f : C(AddCircle (2 : ℝ), ℂ)) (n : ℤ) :
    continuousFourierCLM f n = fourierCoeff f n := by
  exact (fourierBasis_repr _ n).trans (fourierCoeff_toLp f n)

/-- Fourier coefficients determine a continuous function everywhere. -/
theorem continuousFourierCLM_injective : Function.Injective continuousFourierCLM := by
  intro f g h
  apply ContinuousMap.toLp_injective (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ)
  apply fourierBasis.repr.injective
  exact h

/-- Every coefficient is recovered from the sum, with normalized Haar measure. -/
@[simp] theorem fourierCoeff_continuousSynthesis (a : Coeff 1) (n : ℤ) :
    fourierCoeff (continuousSynthesis a) n = a n := by
  let F := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp continuousFourierCLM
  have hF (f : C(AddCircle (2 : ℝ), ℂ)) : F f = fourierCoeff f n :=
    continuousFourierCLM_apply f n
  rw [← hF, continuousSynthesis, F.map_tsum (summable_norm_fourierTerms a).of_norm]
  simp only [hF, ContinuousMap.coe_smul, fourierCoeff.const_smul,
    fourierCoeff_fourier, Pi.single_apply, smul_eq_mul]
  simp

/-- Distinct absolutely summable coefficient sequences give distinct functions. -/
theorem continuousSynthesis_injective : Function.Injective continuousSynthesis := by
  intro a b h
  ext n
  simpa only [fourierCoeff_continuousSynthesis] using congrArg (fun f : C(AddCircle (2 : ℝ), ℂ) => fourierCoeff f n) h

/-- A single coefficient synthesizes to the corresponding period-two wave. -/
@[simp] theorem continuousSynthesis_single (n : ℤ) (c : ℂ) :
    continuousSynthesis (lp.single 1 n c) = c • fourier n := by
  classical
  simp [continuousSynthesis, lp.single_apply, Pi.single_apply]

/-- The circle convention agrees with the physical wave `exp(i π n x)`. -/
theorem fourier_two_eq_wave (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2 : ℝ)) = wave n x := by
  rw [fourier_coe_apply]
  unfold wave
  congr 1
  push_cast
  ring

/-- Pointwise evaluation agrees with the absolutely convergent physical series. -/
theorem continuousSynthesis_apply (a : Coeff 1) (x : ℝ) :
    continuousSynthesis a (x : AddCircle (2 : ℝ)) = ∑' n : ℤ, a n * wave n x := by
  change (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))) (∑' n, a n • fourier n) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_norm_fourierTerms a).of_norm]
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
    fourier_two_eq_wave]

/-- Coefficients computed over `[0,2]` agree with normalized circle coefficients. -/
theorem periodTwoCoefficient_circle (f : C(AddCircle (2 : ℝ), ℂ)) (n : ℤ) :
    periodTwoCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))) n = fourierCoeff f n := by
  rw [fourierCoeff_eq_intervalIntegral f n 0]
  simp only [zero_add, fourier_two_eq_wave, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, periodTwoCoefficient]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  exact mul_comm _ _

/-- Actual interval integrals recover the prescribed coefficients. -/
@[simp] theorem periodTwoCoefficient_continuousSynthesis (a : Coeff 1) (n : ℤ) :
    periodTwoCoefficient (fun x : ℝ => continuousSynthesis a (x : AddCircle (2 : ℝ))) n =
      a n := by
  rw [periodTwoCoefficient_circle, fourierCoeff_continuousSynthesis]

end NLS.Fourier
