import NLS.Fourier.SchwartzSampling
import Mathlib.Analysis.Distribution.TemperedDistribution
import NLS.Fourier.ContinuousSynthesis
import NLS.SequenceSpaces.TestDuality
import NLS.SequenceSpaces.Truncation

/-!
# Distributional Fourier synthesis

Every Banach `ℓᵖ` coefficient sequence defines a genuine tempered distribution
on the real line. It acts on a Schwartz test `g` by the absolutely convergent
sum `∑ n, a n * (𝓕 g) (-n/2)`. This uses the period-two wave convention and is
complex-linear in the test. No integrability of the synthesized potential is
assumed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal SchwartzMap FourierTransform
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Period-two Fourier data synthesized in mathlib's tempered-distribution space. -/
def distributionSynthesis (a : Coeff p) : 𝓢'(ℝ, ℂ) :=
  ((Coeff.testFunctional a).comp
    (schwartzSamplesCLM.comp (FourierTransform.fourierCLM ℂ 𝓢(ℝ, ℂ))))

/-- The defining Fourier sum converges absolutely on every Schwartz test. -/
theorem summable_norm_distributionSynthesis (a : Coeff p) (g : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖a n * (𝓕 g) (-(n : ℝ) / 2)‖) :=
  Coeff.summable_norm_testPairing a (schwartzSamples (𝓕 g))

@[simp] theorem distributionSynthesis_apply (a : Coeff p) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis a g = ∑' n : ℤ, a n * (𝓕 g) (-(n : ℝ) / 2) := rfl

/-- The value on each test is bounded by the coefficient norm. -/
theorem norm_distributionSynthesis_apply_le (a : Coeff p) (g : 𝓢(ℝ, ℂ)) :
    ‖distributionSynthesis a g‖ ≤ ‖a‖ * ‖schwartzSamples (𝓕 g)‖ :=
  Coeff.norm_testPairing_le a (schwartzSamples (𝓕 g))

/-- Continuous linear dependence on the input sequence, including `p = ∞`. -/
def distributionSynthesisCLM : Coeff p →L[ℂ] 𝓢'(ℝ, ℂ) where
  toFun := distributionSynthesis
  map_add' a b := by
    ext g
    exact congrArg (fun T : Coeff 1 →L[ℂ] ℂ => T (schwartzSamples (𝓕 g)))
      (Coeff.testFunctional_add a b)
  map_smul' z a := by
    ext g
    exact congrArg (fun T : Coeff 1 →L[ℂ] ℂ => T (schwartzSamples (𝓕 g)))
      (Coeff.testFunctional_smul z a)
  cont := PointwiseConvergenceCLM.continuous_of_continuous_eval fun g =>
    (ContinuousLinearMap.apply ℂ ℂ (schwartzSamples (𝓕 g))).continuous.comp
      Coeff.testDualityCLM.continuous

@[simp] theorem distributionSynthesisCLM_apply (a : Coeff p) :
    distributionSynthesisCLM a = distributionSynthesis a := rfl

/-- Negative half-integer Fourier samples are precisely tests against our waves. -/
theorem fourier_sample_eq_integral_wave (g : 𝓢(ℝ, ℂ)) (n : ℤ) :
    (𝓕 g) (-(n : ℝ) / 2) = ∫ x : ℝ, wave n x * g x := by
  change (𝓕 (g : ℝ → ℂ)) (-(n : ℝ) / 2) = _
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, wave]
  congr 2
  push_cast
  ring

/-- A single Fourier coefficient gives the ordinary distribution of its wave. -/
@[simp] theorem distributionSynthesis_single (n : ℤ) (c : ℂ) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (lp.single p n c) g =
      c * ∫ x : ℝ, wave n x * g x := by
  change Coeff.testFunctional (lp.single p n c) (schwartzSamples (𝓕 g)) = _
  rw [Coeff.testFunctional_single, schwartzSamples_apply, fourier_sample_eq_integral_wave]

private def frequencyBump (n : ℤ) : ContDiffBump (-(n : ℝ) / 2) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- A compactly supported smooth frequency test isolates a single lattice point. -/
def frequencyTest (n : ℤ) : 𝓢(ℝ, ℂ) :=
  ((frequencyBump n).hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (frequencyBump n).contDiff)

/-- There is no aliasing between distinct positive or negative lattice points. -/
theorem frequencyTest_sample (n m : ℤ) :
    frequencyTest n (-(m : ℝ) / 2) = if m = n then 1 else 0 := by
  change ((frequencyBump n (-(m : ℝ) / 2) : ℝ) : ℂ) = _
  split_ifs with h
  · subst m
    rw [(frequencyBump n).one_of_mem_closedBall]
    · simp
    · simp [Metric.mem_closedBall, frequencyBump]
  · rw [(frequencyBump n).zero_of_le_dist]
    · simp
    · have ha : (1 : ℝ) ≤ |(m : ℝ) - (n : ℝ)| := by
        rw [le_abs]
        rcases lt_or_gt_of_ne h with hlt | hgt
        · right
          have : (m : ℝ) + 1 ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
          linarith
        · left
          have : (n : ℝ) + 1 ≤ m := by exact_mod_cast (show n + 1 ≤ m by omega)
          linarith
      change 1 / 4 ≤ dist (-(m : ℝ) / 2) (-(n : ℝ) / 2)
      rw [Real.dist_eq, show -(m : ℝ) / 2 - -(n : ℝ) / 2 =
        -((m : ℝ) - (n : ℝ)) / 2 by ring, abs_div, abs_neg]
      norm_num
      linarith

/-- A Schwartz test that reads one prescribed Fourier coefficient. -/
def coefficientTest (n : ℤ) : 𝓢(ℝ, ℂ) := 𝓕⁻ (frequencyTest n)

/-- Recover every original coefficient by testing the synthesized distribution. -/
@[simp] theorem distributionSynthesis_coefficientTest (a : Coeff p) (n : ℤ) :
    distributionSynthesis a (coefficientTest n) = a n := by
  classical
  rw [distributionSynthesis_apply, coefficientTest, FourierTransform.fourier_fourierInv_eq]
  simp [frequencyTest_sample]

/-- Distinct coefficient data define distinct genuine tempered distributions. -/
theorem distributionSynthesis_injective : Function.Injective (distributionSynthesis (p := p)) := by
  intro a b h
  ext n
  simpa only [distributionSynthesis_coefficientTest] using
    congrArg (fun T : 𝓢'(ℝ, ℂ) => T (coefficientTest n)) h

/-- Truncated data acts by the corresponding finite Fourier sum. -/
theorem distributionSynthesis_truncate_apply (a : Coeff p) (s : Finset ℤ) (g : 𝓢(ℝ, ℂ)) :
    distributionSynthesis (Coeff.truncate s a) g =
      ∑ n ∈ s, a n * (𝓕 g) (-(n : ℝ) / 2) := by
  classical
  simp only [distributionSynthesis_apply, Coeff.truncate_apply, ite_mul, zero_mul]
  rw [tsum_eq_sum (s := s) (by intro n hn; simp [hn])]
  exact Finset.sum_congr rfl (fun n hn => by simp [hn])

/-- Finite Fourier sums converge as tempered distributions, even at `p = ∞`. -/
theorem tendsto_distributionSynthesis_truncate (a : Coeff p) :
    Filter.Tendsto (fun s : Finset ℤ => distributionSynthesis (Coeff.truncate s a))
      Filter.atTop (nhds (distributionSynthesis a)) := by
  apply PointwiseConvergenceCLM.tendsto_iff_forall_tendsto.mpr
  intro g
  change Filter.Tendsto (fun s : Finset ℤ => distributionSynthesis (Coeff.truncate s a) g)
    Filter.atTop (nhds (distributionSynthesis a g))
  simp_rw [distributionSynthesis_truncate_apply]
  exact (summable_norm_distributionSynthesis a g).of_norm.hasSum

end NLS.Fourier
