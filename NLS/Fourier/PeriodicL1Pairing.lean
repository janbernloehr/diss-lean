import NLS.Fourier.PeriodicL1Functional
import NLS.Fourier.ArbitraryPeriodDistributionPairing

/-! # The normalized L1 pairing via uniformly convergent smooth Fourier series -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace NLS.Fourier
variable (L : ℝ) [Fact (0 < L)]

/-- The continuous circle test associated to a continuous periodic function. -/
def periodicContinuousTest (g : ℝ → ℂ) (hg : Continuous g) (hp : Function.Periodic g L) :
    C(AddCircle L, ℂ) :=
  ⟨AddCircle.liftIoc L 0 g, AddCircle.liftIoc_zero_continuous
    (by simpa only [zero_add] using (hp 0).symm) hg.continuousOn⟩

theorem periodicContinuousTest_coefficient (g : ℝ → ℂ) (hg : Continuous g)
    (hp : Function.Periodic g L) (n : ℤ) :
    fourierCoeff (periodicContinuousTest L g hg hp) n = intervalFourierCoefficient L g n := by
  change fourierCoeff (AddCircle.liftIoc L 0 g) n = _
  rw [fourierCoeff_liftIoc_eq, intervalFourierCoefficient_eq_fourierCoeffOn (Fact.out : 0 < L)]
  congr 1; simp

theorem periodicL1Functional_continuousTest (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L)
    (g : ℝ → ℂ) (hg : Continuous g) (hp : Function.Periodic g L) :
    periodicL1Functional L f hf (periodicContinuousTest L g hg hp) =
      (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g x := by
  rw [periodicL1Functional_apply]
  congr 1
  apply intervalIntegral.integral_congr_ae
  exact ae_of_all _ fun x hx => by
    change f x * AddCircle.liftIoc L 0 g (x : AddCircle L) = _
    rw [AddCircle.liftIoc_coe_apply]
    simpa only [zero_add, uIoc_of_le (Fact.out : 0 < L).le] using hx

/-- Smooth periodic tests have absolutely summable actual Fourier coefficients. -/
theorem summable_norm_smooth_intervalFourierCoefficient (g : ℝ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g L) :
    Summable (fun n => ‖intervalFourierCoefficient L g n‖) := by
  obtain ⟨b, hb, _⟩ := existsUnique_smooth_arbitraryPeriod_coefficients (q := 1) L Fact.out 0 g hg hp
  have h := b.property.summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  simpa only [Weight.sobolev_zero_apply, Complex.ofReal_one, one_mul,
    ENNReal.toReal_one, Real.rpow_one, hb] using h

/-- Applying a bounded L1 functional to the uniform Fourier expansion gives
an actual convergent series for the normalized physical integral. -/
theorem hasSum_periodicL1_pairing (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g L) :
    HasSum (fun n : ℤ => intervalFourierCoefficient L g n * intervalFourierCoefficient L f (-n))
      ((L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g x) := by
  have hs : Summable (fourierCoeff (periodicContinuousTest L g hg.continuous hp)) := by
    have he : fourierCoeff (periodicContinuousTest L g hg.continuous hp) = intervalFourierCoefficient L g :=
      funext (periodicContinuousTest_coefficient L g hg.continuous hp)
    rw [he]
    exact (summable_norm_smooth_intervalFourierCoefficient L g hg hp).of_norm
  have h := (periodicL1Functional L f hf).hasSum (hasSum_fourier_series_of_summable hs)
  simpa only [map_smul, smul_eq_mul, periodicContinuousTest_coefficient,
    periodicL1Functional_fourier, periodicL1Functional_continuousTest] using h

/-- The unconjugated product uses opposite indices, including for merely L1 input. -/
theorem tsum_periodicL1_pairing (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 L)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hp : Function.Periodic g L) :
    (∑' n : ℤ, intervalFourierCoefficient L f n * intervalFourierCoefficient L g (-n)) =
      (L : ℂ)⁻¹ * ∫ x in (0 : ℝ)..L, f x*g x := by
  rw [← (hasSum_periodicL1_pairing L f hf g hg hp).tsum_eq]
  have h := (Equiv.neg ℤ).tsum_eq
    (fun n : ℤ => intervalFourierCoefficient L g n * intervalFourierCoefficient L f (-n))
  simpa only [Equiv.neg_apply, neg_neg, mul_comm] using h

end NLS.Fourier
