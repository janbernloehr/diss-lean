import NLS.Fourier.ArbitraryPeriodDistribution
import NLS.Fourier.SmoothPeriodicDistributionPairing
import NLS.Fourier.IntervalCoefficientScaling

/-! # Corrected scalar distributional pairing on every positive period

The same raw Sobolev coefficients represent the rescaled distribution and
smooth test. The action retains the normalized window and the factor 1/L.
-/
noncomputable section
open scoped ENNReal SchwartzMap ContDiff
namespace NLS.Fourier

theorem periodic_periodTwoDilation (L : ℝ) (f : ℝ → ℂ) (hf : Function.Periodic f L) :
    Function.Periodic (fun x => f ((L/2)*x)) 2 := by
  intro x
  dsimp only
  rw [show (L/2)*(x+2) = (L/2)*x+L by ring]
  exact hf _

theorem distributionDilation_window_action (L : ℝ) (hL : 0 < L) (T : 𝓢'(ℝ, ℂ))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L) :
    distributionDilation (L/2) (by positivity) T
      (SchwartzMap.smulLeftCLM ℂ (fun x => f ((L/2)*x)) (coefficientTest 0)) =
    T (SchwartzMap.smulLeftCLM ℂ f (periodCoefficientTest L hL 0)) := by
  have hff := hasTemperateGrowth_of_smooth_periodic f L hL.ne' hf hp
  have hgg := hasTemperateGrowth_of_smooth_periodic (fun x => f ((L/2)*x)) 2 (by norm_num)
    (hf.comp (by fun_prop)) (periodic_periodTwoDilation L f hp)
  rw [distributionDilation_apply,← smul_eq_mul,← map_smul]
  congr 1
  ext x
  simp only [smul_apply,schwartzDilationCLM_apply,SchwartzMap.smulLeftCLM_apply_apply hgg,
    SchwartzMap.smulLeftCLM_apply_apply hff,periodCoefficientTest,smul_eq_mul]
  rw [mul_inv_cancel_left₀ (by positivity : L/2 ≠ 0)]
  ring

theorem periodicDistribution_sobolevBilinearPairing_arbitraryPeriod {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (L : ℝ) (hL : 0 < L) (s : ℝ) (T : 𝓢'(ℝ, ℂ)) (hT : IsPeriodicDistribution L T)
    (a : WeightedCoeff (Weight.sobolev s) p) (ha : ∀ n, a.val n = T (periodCoefficientTest L hL n))
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L)
    (b : WeightedCoeff (Weight.sobolev (-s)) q) (hb : ∀ n, b.val n = intervalFourierCoefficient L f n) :
    WeightedCoeff.sobolevBilinearPairing s a b =
      T (SchwartzMap.smulLeftCLM ℂ f (periodCoefficientTest L hL 0)) := by
  have hg : ContDiff ℝ ∞ (fun x => f ((L/2)*x)) := hf.comp (by fun_prop)
  have hga (n : ℤ) : a.val n = distributionDilation (L/2) (by positivity) T (coefficientTest n) := by
    rw [distributionDilation_periodCoefficientTest]; exact ha n
  have hgb (n : ℤ) : b.val n = periodTwoCoefficient (fun x => f ((L/2)*x)) n := by
    rw [hb]
    exact (periodTwoCoefficient_intervalDilation hL f n).symm
  rw [periodicDistribution_sobolevBilinearPairing_smooth s _ (isPeriodTwoDistribution_dilation L hL T hT)
    a hga _ hg (periodic_periodTwoDilation L f hp) b hgb,distributionDilation_window_action L hL T f hf hp]

/-- Smooth tests have a unique actual coefficient representative on every positive period,
at every real Sobolev order and every Banach exponent. -/
theorem existsUnique_smooth_arbitraryPeriod_coefficients {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (L : ℝ) (hL : 0 < L) (s : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f L) :
    ∃! b : WeightedCoeff (Weight.sobolev s) q, ∀ n, b.val n = intervalFourierCoefficient L f n := by
  let g := fun x => f ((L/2)*x)
  have hg : ContDiff ℝ ∞ g := hf.comp (by fun_prop)
  have hpg : Function.Periodic g 2 := periodic_periodTwoDilation L f hp
  let b := periodizationSobolevCoefficients (q := q) s (smoothPeriodicTestLift g)
  have hb (n : ℤ) : b.val n = intervalFourierCoefficient L f n := by
    rw [smoothPeriodicTestLift_sobolev_coefficients s g hg hpg]
    exact periodTwoCoefficient_intervalDilation hL f n
  refine ⟨b,hb,fun a ha => ?_⟩
  apply Subtype.ext
  funext n
  exact (ha n).trans (hb n).symm

end NLS.Fourier
