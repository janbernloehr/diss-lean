import NLS.Fourier.SchwartzPeriodization
import NLS.Fourier.DistributionDerivative
import NLS.Fourier.DistributionModulation
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Smooth periodization and differentiation of every order

The derivative Fourier series is absolutely summable for every Schwartz test.
Termwise differentiation therefore identifies the physical derivative with the
periodization of the Schwartz derivative. Iteration provides all smooth orders.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform ContDiff
namespace NLS.Fourier

/-- Absolutely summable differentiated coefficients give the classical derivative everywhere. -/
theorem hasDerivAt_continuousSynthesis_of_coefficients (a b : Coeff 1)
    (h : ∀ n : ℤ, b n = Complex.I * (Real.pi : ℂ) * n * a n) (x : ℝ) :
    HasDerivAt (fun y : ℝ => continuousSynthesis a (y : AddCircle (2 : ℝ)))
      (continuousSynthesis b (x : AddCircle (2 : ℝ))) x := by
  have hb := (lp.memℓp b).norm.summable_of_one
  have hd (n : ℤ) (y : ℝ) :
      HasDerivAt (fun t => a n * wave n t) (b n * wave n y) y := by
    convert! (hasDerivAt_wave n y).const_mul (a n) using 1
    rw [h n]
    ring
  have hn (n : ℤ) (y : ℝ) : ‖b n * wave n y‖ ≤ ‖b n‖ := by
    simp [wave, Complex.norm_exp]
  have ha : Summable (fun n : ℤ => a n * wave n (0 : ℝ)) := by
    simpa using (lp.memℓp a).summable_of_one
  simpa only [continuousSynthesis_apply] using hasDerivAt_tsum hb hd hn ha x

private def periodizationCoefficients (g : 𝓢(ℝ, ℂ)) : Coeff 1 :=
  (1 / 2 : ℂ) • Coeff.reflection (schwartzSamples (𝓕 g))

private theorem periodizationCoefficients_apply (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    periodizationCoefficients g n = (1 / 2 : ℂ) * (𝓕 g) ((n : ℝ) / 2) := by
  simp [periodizationCoefficients, Coeff.reflection_apply]

private theorem periodizationCoefficients_deriv (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    periodizationCoefficients (SchwartzMap.derivCLM ℂ ℂ g) n =
      Complex.I * (Real.pi : ℂ) * n * periodizationCoefficients g n := by
  rw [periodizationCoefficients_apply, periodizationCoefficients_apply]
  have h := fourier_sample_deriv g (-n)
  simp only [Int.cast_neg, neg_neg] at h
  rw [h]
  push_cast
  ring

/-- Periodization commutes with classical differentiation on the real line. -/
theorem hasDerivAt_periodization (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => periodizationCLM g (y : AddCircle (2 : ℝ)))
      (periodizationCLM (SchwartzMap.derivCLM ℂ ℂ g) (x : AddCircle (2 : ℝ))) x :=
  hasDerivAt_continuousSynthesis_of_coefficients (periodizationCoefficients g)
    (periodizationCoefficients (SchwartzMap.derivCLM ℂ ℂ g))
    (periodizationCoefficients_deriv g) x

/-- Equality of the physical derivative and the periodized Schwartz derivative. -/
theorem deriv_periodization (g : 𝓢(ℝ, ℂ)) :
    deriv (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => periodizationCLM (SchwartzMap.derivCLM ℂ ℂ g) (x : AddCircle (2 : ℝ)) :=
  funext (fun x => (hasDerivAt_periodization g x).deriv)

/-- Every finite order of smoothness of a Schwartz periodization. -/
theorem contDiff_periodization_nat (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ k (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) := by
  induction k generalizing g with
  | zero => exact contDiff_zero.mpr ((periodizationCLM g).continuous.comp continuous_quotient_mk')
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_periodization g x).differentiableAt, ?_, ?_⟩
    · simp
    · rw [deriv_periodization]
      exact ih _

/-- Periodizations are genuinely smooth, not just continuous circle functions. -/
@[fun_prop] theorem contDiff_periodization (g : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) :=
  contDiff_infty.mpr (fun k => contDiff_periodization_nat k g)

/-- Each physical derivative of periodization depends continuously and linearly on the test. -/
def periodizationDerivCLM (k : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  periodizationCLM.comp ((SchwartzMap.derivCLM ℂ ℂ) ^ k)

@[simp] theorem periodizationDerivCLM_zero (g : 𝓢(ℝ, ℂ)) :
    periodizationDerivCLM 0 g = periodizationCLM g := rfl

/-- Taking the input derivative shifts the order by one. -/
theorem periodizationDerivCLM_succ (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    periodizationDerivCLM (k + 1) g =
      periodizationDerivCLM k (SchwartzMap.derivCLM ℂ ℂ g) := by
  simp only [periodizationDerivCLM, pow_succ, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]

/-- All physical derivatives agree with continuous circle-valued periodizations. -/
theorem iteratedDeriv_periodization (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    iteratedDeriv k (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => periodizationDerivCLM k g (x : AddCircle (2 : ℝ)) := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', deriv_periodization, ih]
    simp only [periodizationDerivCLM_succ]

/-- Every derivative is bounded uniformly over the entire real line. -/
theorem norm_iteratedDeriv_periodization_le (k : ℕ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ‖iteratedDeriv k (fun y : ℝ => periodizationCLM g (y : AddCircle (2 : ℝ))) x‖ ≤
      ‖periodizationDerivCLM k g‖ := by
  rw [iteratedDeriv_periodization]
  exact ContinuousMap.norm_coe_le_norm _ _

/-- Smooth periodizations satisfy Mathlib's genuine multiplier condition on Schwartz space. -/
theorem periodization_hasTemperateGrowth (g : 𝓢(ℝ, ℂ)) :
    (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))).HasTemperateGrowth := by
  refine ⟨contDiff_periodization g, fun k => ⟨0, ‖periodizationDerivCLM k g‖, ?_⟩⟩
  intro x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simpa using norm_iteratedDeriv_periodization_le k g x

/-- Fourier coefficients of the first periodized derivative have the physical sign. -/
theorem fourierCoeff_periodization_deriv (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    fourierCoeff (periodizationCLM (SchwartzMap.derivCLM ℂ ℂ g)) n =
      Complex.I * (Real.pi : ℂ) * n * fourierCoeff (periodizationCLM g) n := by
  simpa only [fourierCoeff_periodization, periodizationCoefficients_apply] using
    periodizationCoefficients_deriv g n

/-- Every derivative retains the exact integer power of the Fourier multiplier. -/
theorem fourierCoeff_periodizationDerivCLM (k : ℕ) (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    fourierCoeff (periodizationDerivCLM k g) n =
      (Complex.I * (Real.pi : ℂ) * n) ^ k * fourierCoeff (periodizationCLM g) n := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [periodizationDerivCLM_succ, ih, fourierCoeff_periodization_deriv, pow_succ]
    ring

/-- Fourier coefficients of every periodized derivative are absolutely summable. -/
theorem summable_norm_fourierCoeff_periodizationDeriv (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖fourierCoeff (periodizationDerivCLM k g) n‖) := by
  change Summable (fun n : ℤ => ‖fourierCoeff
    (continuousSynthesis (periodizationCoefficients (((SchwartzMap.derivCLM ℂ ℂ) ^ k) g))) n‖)
  simp only [fourierCoeff_continuousSynthesis]
  exact (lp.memℓp _).norm.summable_of_one

/-- The Fourier series of every physical derivative converges to that derivative. -/
theorem periodizationDerivCLM_apply_tsum (k : ℕ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    periodizationDerivCLM k g (x : AddCircle (2 : ℝ)) =
      ∑' n : ℤ, fourierCoeff (periodizationDerivCLM k g) n * wave n x := by
  change continuousSynthesis (periodizationCoefficients (((SchwartzMap.derivCLM ℂ ℂ) ^ k) g))
    (x : AddCircle (2 : ℝ)) = _
  rw [continuousSynthesis_apply]
  apply tsum_congr
  intro n
  rw [show periodizationDerivCLM k g =
    continuousSynthesis (periodizationCoefficients (((SchwartzMap.derivCLM ℂ ℂ) ^ k) g)) from rfl,
    fourierCoeff_continuousSynthesis]

/-- Differentiating a Fourier polynomial multiplies each mode by the exact symbol power. -/
theorem iteratedDeriv_fourierPolynomial (k : ℕ) (s : Finset ℤ) (b : ℤ → ℂ) :
    iteratedDeriv k (fourierPolynomial s b) =
      fourierPolynomial s (fun n => (Complex.I * (Real.pi : ℂ) * n) ^ k * b n) := by
  funext x
  unfold fourierPolynomial
  have hs (n : ℤ) : ContDiff ℝ k (fun y : ℝ => b n * wave n y) :=
    contDiff_infty.mp (contDiff_const.mul (contDiff_wave_infty n)) k
  rw [iteratedDeriv_fun_sum (fun n _ => (hs n).contDiffAt)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_wave]
  ring

/-- The same Fourier truncations converge uniformly together with each derivative order. -/
theorem tendstoUniformly_iteratedDeriv_periodization (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    TendstoUniformly
      (fun s : Finset ℤ => iteratedDeriv k
        (fourierPolynomial s (fourierCoeff (periodizationCLM g))))
      (iteratedDeriv k (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))))
      Filter.atTop := by
  have hn (n : ℤ) (x : ℝ) :
      ‖fourierCoeff (periodizationDerivCLM k g) n * wave n x‖ ≤
        ‖fourierCoeff (periodizationDerivCLM k g) n‖ := by
    simp [wave, Complex.norm_exp]
  have h := tendstoUniformly_tsum (summable_norm_fourierCoeff_periodizationDeriv k g) hn
  simp only [iteratedDeriv_fourierPolynomial, iteratedDeriv_periodization]
  unfold fourierPolynomial
  simpa only [periodizationDerivCLM_apply_tsum, fourierCoeff_periodizationDerivCLM] using! h

private theorem schwartz_deriv_pow_coe (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ⇑(((SchwartzMap.derivCLM ℂ ℂ) ^ k) g) = iteratedDeriv k (g : ℝ → ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, iteratedDeriv_succ]
    change deriv (⇑(((SchwartzMap.derivCLM ℂ ℂ) ^ k) g)) = _
    rw [ih]

/-- Derivatives of every order have absolutely convergent physical translate sums. -/
theorem summable_norm_iteratedDeriv_periodization (k : ℕ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun n : ℤ => ‖iteratedDeriv k (g : ℝ → ℂ) (x + 2 * n)‖) := by
  simpa only [schwartz_deriv_pow_coe] using
    summable_norm_periodization (((SchwartzMap.derivCLM ℂ ℂ) ^ k) g) x

/-- Classical derivatives also commute with the original physical sum of translates. -/
theorem iteratedDeriv_periodization_eq_tsum (k : ℕ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => periodizationCLM g (y : AddCircle (2 : ℝ))) x =
      ∑' n : ℤ, iteratedDeriv k (g : ℝ → ℂ) (x + 2 * n) := by
  rw [iteratedDeriv_periodization]
  change periodizationCLM (((SchwartzMap.derivCLM ℂ ℂ) ^ k) g)
    (x : AddCircle (2 : ℝ)) = _
  rw [periodization_eq_tsum]
  simp only [schwartz_deriv_pow_coe]

end NLS.Fourier
