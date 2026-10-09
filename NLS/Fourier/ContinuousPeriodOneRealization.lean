import NLS.Fourier.FinitePeriodOneRealization
import NLS.Fourier.PeriodOneH1Norm

/-! # Coefficient-preserving realization of continuous unit-period profiles

Endpoint-matching continuous interval data is repeated with period one.
Its actual Fourier integrals give Hilbert source coefficients, whose even
period-two insertion reconstructs the original profile almost everywhere.
-/

noncomputable section
open Complex MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Repeat the values on `(0,1]` with period one. -/
def periodOneRepeat (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  AddCircle.liftIoc 1 0 f (x : AddCircle (1 : ℝ))

@[simp] theorem periodOneRepeat_apply {f : ℝ → ℂ} {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    periodOneRepeat f x = f x := AddCircle.liftIoc_zero_coe_apply hx

theorem periodOneRepeat_periodic (f : ℝ → ℂ) : Function.Periodic (periodOneRepeat f) 1 := by
  intro x
  simp only [periodOneRepeat, AddCircle.coe_add_period]

@[fun_prop] theorem continuous_periodOneRepeat (f : ℝ → ℂ) (hf : Continuous f) (hend : f 0 = f 1) :
    Continuous (periodOneRepeat f) :=
  (AddCircle.liftIoc_zero_continuous hend hf.continuousOn).comp (by fun_prop)

/-- Actual unit-period coefficients, realized by reading even frequencies of the repeated profile. -/
def continuousPeriodOneCoefficients (f : ℝ → ℂ) (hf : Continuous f) (hend : f 0 = f 1) : Coeff 2 :=
  Coeff.periodHalve (periodTwoL2Coefficients (periodOneRepeat f)
    (memLp_two_interval (continuous_periodOneRepeat f hf hend) 0 2 (by norm_num)))

@[simp] theorem continuousPeriodOneCoefficients_apply (f : ℝ → ℂ)
    (hf : Continuous f) (hend : f 0 = f 1) (n : ℤ) :
    continuousPeriodOneCoefficients f hf hend n = periodOneCoefficient f n := by
  rw [continuousPeriodOneCoefficients, Coeff.periodHalve_apply, periodTwoL2Coefficients_apply,
    periodTwoCoefficient_periodic_even _ (periodOneRepeat_periodic f)
      ((continuous_periodOneRepeat f hf hend).intervalIntegrable 0 1)]
  apply congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1) ?_) n
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact periodOneRepeat_apply hx

/-- No odd frequencies are introduced by repeating a unit-period profile. -/
theorem periodDouble_continuousPeriodOneCoefficients (f : ℝ → ℂ)
    (hf : Continuous f) (hend : f 0 = f 1) :
    Coeff.periodDouble (continuousPeriodOneCoefficients f hf hend) =
      periodTwoL2Coefficients (periodOneRepeat f)
        (memLp_two_interval (continuous_periodOneRepeat f hf hend) 0 2 (by norm_num)) := by
  ext n
  symm
  apply congrFun (periodTwoCoefficient_eq_periodDouble _ (periodOneRepeat_periodic f)
    ((continuous_periodOneRepeat f hf hend).intervalIntegrable 0 1)
    (continuousPeriodOneCoefficients f hf hend) ?_) n
  intro k
  exact (periodTwoCoefficient_periodic_even _ (periodOneRepeat_periodic f)
    ((continuous_periodOneRepeat f hf hend).intervalIntegrable 0 1) k).symm

/-- The actual Hilbert synthesis recovers the original interval profile. -/
theorem circlePullback_continuousPeriodOneCoefficients (f : ℝ → ℂ)
    (hf : Continuous f) (hend : f 0 = f 1) :
    circlePullback (l2Synthesis (Coeff.periodDouble (continuousPeriodOneCoefficients f hf hend)))
      =ᵐ[volume.restrict (Ioc 0 1)] f := by
  rw [periodDouble_continuousPeriodOneCoefficients]
  have h := ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc_right (by norm_num : (1 : ℝ) ≤ 2))
    (circlePullback_periodTwoL2Coefficients (periodOneRepeat f)
      (memLp_two_interval (continuous_periodOneRepeat f hf hend) 0 2 (by norm_num)))
  filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with x hx hmem
  exact hx.trans (periodOneRepeat_apply hmem)

/-- Parseval uses exactly the unnormalized unit-interval integral. -/
theorem norm_sq_continuousPeriodOneCoefficients (f : ℝ → ℂ)
    (hf : Continuous f) (hend : f 0 = f 1) :
    ‖continuousPeriodOneCoefficients f hf hend‖^2 = ∫ x in (0 : ℝ)..1, ‖f x‖^2 := by
  have hs := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num)
    (continuousPeriodOneCoefficients f hf hend)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, continuousPeriodOneCoefficients_apply] at hs
  exact hs.unique (hasSum_sq_periodOneCoefficient (memLp_two_interval hf 0 1 (by norm_num)))

end NLS.Fourier
