import NLS.Fourier.DistributionPeriodicity
import NLS.SequenceSpaces.Reflection
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Period-two periodization of actual Schwartz tests

Poisson summation identifies the sum of translates `Σ_k g(x+2k)` with a
continuous Fourier series on the period-two circle. Its normalized coefficients
are `(1 / 2) (𝓕g)(n/2)`. This bridges genuine Schwartz tests and periodic tests,
with the factor and frequency reflection fixed explicitly.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier

private def doubleArgument : ℝ ≃L[ℝ] ℝ :=
  { LinearEquiv.smulOfNeZero ℝ (M := ℝ) (2 : ℝ) (by norm_num) with
    continuous_toFun := by change Continuous (fun x : ℝ => 2 * x); fun_prop
    continuous_invFun := by change Continuous (fun x : ℝ => (2 : ℝ)⁻¹ * x); fun_prop }

private def doubledTest (g : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ doubleArgument g

private theorem doubledTest_apply (g : 𝓢(ℝ, ℂ)) (x : ℝ) : doubledTest g x = g (2 * x) := rfl

/-- The exact Fourier scaling needed for period-two Poisson summation. -/
private theorem fourier_doubledTest (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (doubledTest g)) ξ = (1 / 2 : ℂ) * (𝓕 g) (ξ / 2) := by
  change (𝓕 (doubledTest g : ℝ → ℂ)) ξ = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ x : ℝ, Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) * g (2 * x)) = _
  have he (x : ℝ) :
      Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) * g (2 * x) =
      (fun y : ℝ => Complex.exp ((-2 * Real.pi * y * (ξ / 2) : ℝ) * Complex.I) * g y) (2 * x) := by
    congr 2
    push_cast
    ring
  simp_rw [he]
  rw [Measure.integral_comp_mul_left
    (fun y : ℝ => Complex.exp ((-2 * Real.pi * y * (ξ / 2) : ℝ) * Complex.I) * g y) 2]
  change _ = (1 / 2 : ℂ) * (𝓕 (g : ℝ → ℂ)) (ξ / 2)
  rw [Real.fourier_real_eq_integral_exp_smul]
  norm_num [smul_eq_mul, Complex.real_smul]

/-- Periodization as a continuous linear map to continuous period-two functions. -/
def periodizationCLM : 𝓢(ℝ, ℂ) →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  continuousSynthesisCLM.comp
    (((1 / 2 : ℂ) • Coeff.reflection.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (schwartzSamplesCLM.comp (FourierTransform.fourierCLM ℂ 𝓢(ℝ, ℂ))))

/-- The normalized Fourier coefficient of periodization. -/
@[simp] theorem fourierCoeff_periodization (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    fourierCoeff (periodizationCLM g) n = (1 / 2 : ℂ) * (𝓕 g) ((n : ℝ) / 2) := by
  change fourierCoeff (continuousSynthesis ((1 / 2 : ℂ) •
    Coeff.reflection (schwartzSamples (𝓕 g)))) n = _
  rw [fourierCoeff_continuousSynthesis]
  simp [Coeff.reflection_apply]

/-- The physical translate sum is absolutely convergent at every real argument. -/
theorem summable_norm_periodization (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    Summable (fun k : ℤ => ‖g (x + 2 * k)‖) := by
  have h := (summable_norm_schwartzSamples
    (doubledTest (doubledTest (SchwartzMap.compSubConstCLM ℂ (-x) g)))).comp_injective
      (neg_injective (G := ℤ))
  have harg (k : ℤ) : 2 * (2 * ((k : ℝ) / 2)) - -x = x + 2 * k := by ring
  simpa only [Function.comp_def, doubledTest_apply, SchwartzMap.compSubConstCLM_apply,
    Int.cast_neg, neg_neg, harg] using h

/-- Period-two Poisson summation, in the physical wave convention. -/
theorem periodization_eq_tsum (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    periodizationCLM g (x : AddCircle (2 : ℝ)) = ∑' k : ℤ, g (x + 2 * k) := by
  have h := (doubledTest g).tsum_eq_tsum_fourier (x / 2)
  have hw (n : ℤ) : fourier n ((x / 2 : ℝ) : UnitAddCircle) = wave n x := by
    rw [fourier_coe_apply]
    unfold wave
    congr 1
    push_cast
    ring
  simp only [doubledTest_apply, fourier_doubledTest, hw] at h
  have hx (k : ℤ) : 2 * (x / 2 + k) = x + 2 * k := by ring
  simp_rw [hx] at h
  change (continuousSynthesis ((1 / 2 : ℂ) • Coeff.reflection (schwartzSamples (𝓕 g))))
    (x : AddCircle (2 : ℝ)) = _
  rw [continuousSynthesis_apply]
  simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Coeff.reflection_apply,
    schwartzSamples_apply, Int.cast_neg, neg_neg] using h.symm

/-- Periodization preserves the integral, with normalized circle coefficients carrying one half. -/
theorem integral_periodization (g : 𝓢(ℝ, ℂ)) :
    (∫ x in (0 : ℝ)..2, periodizationCLM g (x : AddCircle (2 : ℝ))) = ∫ x : ℝ, g x := by
  have h := fourierCoeff_periodization g 0
  rw [← periodTwoCoefficient_circle] at h
  simp only [periodTwoCoefficient, neg_zero, wave_zero, mul_one, Int.cast_zero, zero_div] at h
  have hFT : (𝓕 g) 0 = ∫ x : ℝ, g x := by
    simpa only [Int.cast_zero, neg_zero, zero_div, wave_zero, one_mul] using
      fourier_sample_eq_integral_wave g 0
  rw [hFT] at h
  exact mul_left_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) h

/-- Vanishing of periodization is exactly vanishing of all lattice Fourier samples. -/
theorem periodization_eq_zero_iff (g : 𝓢(ℝ, ℂ)) :
    periodizationCLM g = 0 ↔ ∀ n : ℤ, (𝓕 g) (-(n : ℝ) / 2) = 0 := by
  constructor
  · intro h n
    have he := fourierCoeff_periodization g (-n)
    rw [h] at he
    simp only [ContinuousMap.coe_zero, fourierCoeff, Pi.zero_apply,
      smul_zero, integral_zero, Int.cast_neg] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)
  · intro h
    apply continuousFourierCLM_injective
    ext n
    simp only [continuousFourierCLM_apply, fourierCoeff_periodization, map_zero, lp.coeFn_zero,
      Pi.zero_apply]
    have he := h (-n)
    simpa only [Int.cast_neg, neg_neg, he, mul_zero] using congrArg (fun z : ℂ => (1 / 2) * z) he

/-- A coefficient-extracting test periodizes to the opposite wave, with amplitude one half. -/
@[simp] theorem periodization_coefficientTest (n : ℤ) :
    periodizationCLM (coefficientTest n) = (1 / 2 : ℂ) • fourier (-n) := by
  classical
  apply continuousFourierCLM_injective
  ext m
  simp only [continuousFourierCLM_apply, fourierCoeff_periodization,
    ContinuousMap.coe_smul, fourierCoeff.const_smul, fourierCoeff_fourier,
    coefficientTest, FourierTransform.fourier_fourierInv_eq, smul_eq_mul]
  have h := frequencyTest_sample n (-m)
  simp only [Int.cast_neg, neg_neg] at h
  rw [h]
  by_cases hm : m = -n
  · subst m
    simp
  · have hmn : -m ≠ n := by omega
    simp [hm, hmn]

/-- The zero-frequency test supplies a Schwartz window with constant periodization. -/
theorem tsum_coefficientTest_zero (x : ℝ) :
    (∑' k : ℤ, coefficientTest 0 (x + 2 * k)) = (1 / 2 : ℂ) := by
  rw [← periodization_eq_tsum, periodization_coefficientTest]
  simp

/-- An explicit Schwartz lift of a finite Fourier polynomial. -/
def polynomialTest (s : Finset ℤ) (b : ℤ → ℂ) : 𝓢(ℝ, ℂ) :=
  ∑ n ∈ s, (2 * b n) • coefficientTest (-n)

/-- Every finite Fourier polynomial is exactly the periodization of its Schwartz lift. -/
@[simp] theorem periodization_polynomialTest (s : Finset ℤ) (b : ℤ → ℂ) :
    periodizationCLM (polynomialTest s b) = ∑ n ∈ s, b n • fourier n := by
  simp only [polynomialTest, map_sum, map_smul, periodization_coefficientTest, neg_neg,
    smul_smul]
  congr 1
  funext n
  congr 1
  ring

/-- Testing a lifted polynomial uses the reflected coefficients and the period-two factor. -/
theorem distributionSynthesis_polynomialTest {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p) (s : Finset ℤ) (b : ℤ → ℂ) :
    distributionSynthesis a (polynomialTest s b) = ∑ n ∈ s, 2 * b n * a (-n) := by
  simp only [polynomialTest, map_sum, map_smul, distributionSynthesis_coefficientTest,
    smul_eq_mul]

/-- Schwartz periodizations are dense in the uniform norm on the period-two circle. -/
theorem denseRange_periodization : DenseRange periodizationCLM := by
  have hspan : Submodule.span ℂ (Set.range (@fourier (2 : ℝ))) ≤
      LinearMap.range periodizationCLM.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro f ⟨n, rfl⟩
    refine ⟨(2 : ℂ) • coefficientTest (-n), ?_⟩
    simp [periodization_coefficientTest, smul_smul]
  change Dense (LinearMap.range periodizationCLM.toLinearMap :
    Set C(AddCircle (2 : ℝ), ℂ))
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  rw [← span_fourier_closure_eq_top (T := (2 : ℝ))]
  exact Submodule.topologicalClosure_mono hspan

/-- Periodization is invariant under translation of the Schwartz test by two. -/
theorem periodization_translate_two (g : 𝓢(ℝ, ℂ)) :
    periodizationCLM (SchwartzMap.compSubConstCLM ℂ 2 g) = periodizationCLM g := by
  apply continuousFourierCLM_injective
  ext n
  simp only [continuousFourierCLM_apply, fourierCoeff_periodization]
  have h := fourier_sample_translate g (-n) 2
  have hw : wave (-n) 2 = 1 := by
    convert wave_even_at_one (-n) using 1
    unfold wave
    congr 1
    push_cast
    ring
  simpa only [Int.cast_neg, neg_neg, hw, one_mul] using
    congrArg (fun z : ℂ => (1 / 2) * z) h

/-- Synthesized distributions act only on the periodization of their test. -/
theorem distributionSynthesis_eq_of_periodization_eq {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Coeff p) {g h : 𝓢(ℝ, ℂ)} (he : periodizationCLM g = periodizationCLM h) :
    distributionSynthesis a g = distributionSynthesis a h := by
  simp only [distributionSynthesis_apply]
  apply tsum_congr
  intro n
  have hc := congrArg (fun f : C(AddCircle (2 : ℝ), ℂ) => fourierCoeff f (-n)) he
  simp only [fourierCoeff_periodization, Int.cast_neg] at hc
  rw [mul_left_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) hc]

/-- The kernel of periodization is exactly the common annihilator of synthesized distributions. -/
theorem periodization_eq_zero_iff_distributionSynthesis {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (g : 𝓢(ℝ, ℂ)) :
    periodizationCLM g = 0 ↔ ∀ a : Coeff p, distributionSynthesis a g = 0 := by
  constructor
  · intro h a
    simpa using distributionSynthesis_eq_of_periodization_eq a
      (g := g) (h := 0) (by simpa using h)
  · intro h
    apply (periodization_eq_zero_iff g).mpr
    intro n
    have hn := h (lp.single p n 1)
    simpa [distributionSynthesis_apply, lp.single_apply, Pi.single_apply] using hn

end NLS.Fourier
