import NLS.Fourier.CircleTranslation
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Physical fractional translation energy and its Fourier diagonalization

Nonnegative integrals of actual `L²` translation increments diagonalize by
Parseval and Tonelli, without assuming that the energy is finite. The singular
fractional kernel on displacements in `[-1,1]` is a special case. Comparison of
its spectral weights with Sobolev weights and the nonperiodic interval extension
remain separate steps toward Appendix A.9.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Nonnegative energy of physical translations, for an arbitrary displacement measure and kernel. -/
def translationEnergy (μ : Measure ℝ) (w : ℝ → ℝ≥0∞) (f : CircleL2) : ℝ≥0∞ :=
  ∫⁻ t, w t * ENNReal.ofReal (‖circleTranslation t f - f‖ ^ 2) ∂μ

/-- The Fourier weight associated with a displacement kernel. -/
def translationSpectralWeight (μ : Measure ℝ) (w : ℝ → ℝ≥0∞) (n : ℤ) : ℝ≥0∞ :=
  ∫⁻ t, w t * ENNReal.ofReal (‖wave n t - 1‖ ^ 2) ∂μ

/-- Parseval for increments as an extended nonnegative sum. -/
theorem ofReal_norm_sq_circleTranslation_sub (t : ℝ) (f : CircleL2) :
    ENNReal.ofReal (‖circleTranslation t f - f‖ ^ 2) =
      ∑' n : ℤ, ENNReal.ofReal (‖wave n t - 1‖ ^ 2) * ENNReal.ofReal (‖fourierCoeff f n‖ ^ 2) := by
  have hs := hasSum_sq_circleTranslation_sub t f
  rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs.summable]
  simp only [ENNReal.ofReal_mul (sq_nonneg _)]

/-- Tonelli gives exact diagonalization even when the energy is infinite. -/
theorem translationEnergy_eq_tsum (μ : Measure ℝ) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (f : CircleL2) :
    translationEnergy μ w f = ∑' n : ℤ,
      translationSpectralWeight μ w n * ENNReal.ofReal (‖fourierCoeff f n‖ ^ 2) := by
  unfold translationEnergy
  simp_rw [ofReal_norm_sq_circleTranslation_sub, ← ENNReal.tsum_mul_left, ← mul_assoc]
  rw [lintegral_tsum (fun n => by fun_prop)]
  apply tsum_congr
  intro n
  exact lintegral_mul_const _ (by fun_prop)

/-- The energy is expressed by ordinary increments of a real-line periodic representative. -/
theorem translationEnergy_eq_physical (μ : Measure ℝ) (w : ℝ → ℝ≥0∞) (f : CircleL2) :
    translationEnergy μ w f = ∫⁻ t, w t * ENNReal.ofReal ((1 / 2 : ℝ) *
      ∫ x in (0 : ℝ)..2, ‖circlePullback f (t + x) - circlePullback f x‖ ^ 2) ∂μ := by
  simp only [translationEnergy, norm_sq_circleTranslation_sub]

/-- The kernel energy is a genuine nonnegative double integral of physical function differences. -/
theorem translationEnergy_eq_double_lintegral (μ : Measure ℝ) (w : ℝ → ℝ≥0∞) (f : CircleL2) :
    translationEnergy μ w f = ENNReal.ofReal (1 / 2 : ℝ) *
      ∫⁻ t, ∫⁻ x in Ioc (0 : ℝ) 2,
        w t * ENNReal.ofReal (‖circlePullback f (t + x) - circlePullback f x‖ ^ 2) ∂volume ∂μ := by
  rw [translationEnergy_eq_physical, ← lintegral_const_mul' _ _ (by simp)]
  apply lintegral_congr
  intro t
  have hfi := (memLp_circlePullback_increment t f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [intervalIntegral.integral_of_le (by norm_num), ENNReal.ofReal_mul (by norm_num),
    ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    lintegral_const_mul'' _ hfi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  ring

@[simp] theorem translationSpectralWeight_zero (μ : Measure ℝ) (w : ℝ → ℝ≥0∞) :
    translationSpectralWeight μ w 0 = 0 := by simp [translationSpectralWeight]

/-- The singular kernel of the fractional Gagliardo seminorm on a period-two circle. -/
def fractionalTranslationKernel (s : ℝ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal |t|) ^ (-(1 + 2 * s))

theorem measurable_fractionalTranslationKernel (s : ℝ) : Measurable (fractionalTranslationKernel s) := by
  unfold fractionalTranslationKernel
  fun_prop

/-- The normalized squared fractional translation seminorm; infinite values are retained. -/
def fractionalTranslationEnergy (s : ℝ) (f : CircleL2) : ℝ≥0∞ :=
  translationEnergy (volume.restrict (Icc (-1) 1)) (fractionalTranslationKernel s) f

/-- The exact frequency weight before comparison with the conventional Sobolev weight. -/
def fractionalSpectralWeight (s : ℝ) (n : ℤ) : ℝ≥0∞ :=
  translationSpectralWeight (volume.restrict (Icc (-1) 1)) (fractionalTranslationKernel s) n

/-- The physical fractional energy is its exact Fourier-weighted nonnegative series. -/
theorem fractionalTranslationEnergy_eq_tsum (s : ℝ) (f : CircleL2) :
    fractionalTranslationEnergy s f = ∑' n : ℤ,
      fractionalSpectralWeight s n * ENNReal.ofReal (‖fourierCoeff f n‖ ^ 2) :=
  translationEnergy_eq_tsum _ _ (measurable_fractionalTranslationKernel s) f

/-- Fractional periodic regularity here is defined by physical increments, not Fourier coefficients. -/
def HasFractionalPeriodicRegularity (s : ℝ) (f : CircleL2) : Prop :=
  fractionalTranslationEnergy s f < ⊤

/-- Finiteness of the physical seminorm is equivalent to finiteness of its exact spectral series. -/
theorem hasFractionalPeriodicRegularity_iff (s : ℝ) (f : CircleL2) :
    HasFractionalPeriodicRegularity s f ↔
      (∑' n : ℤ, fractionalSpectralWeight s n * ENNReal.ofReal (‖fourierCoeff f n‖ ^ 2)) < ⊤ := by
  rw [HasFractionalPeriodicRegularity, fractionalTranslationEnergy_eq_tsum]

@[simp] theorem fractionalSpectralWeight_zero (s : ℝ) : fractionalSpectralWeight s 0 = 0 :=
  translationSpectralWeight_zero _ _

/-- Translation preserves every kernel energy, in particular the fractional seminorm. -/
theorem translationEnergy_circleTranslation (μ : Measure ℝ) (w : ℝ → ℝ≥0∞)
    (hw : Measurable w) (t : ℝ) (f : CircleL2) :
    translationEnergy μ w (circleTranslation t f) = translationEnergy μ w f := by
  rw [translationEnergy_eq_tsum μ w hw, translationEnergy_eq_tsum μ w hw]
  apply tsum_congr
  intro n
  have hn : ‖wave n t‖ = 1 := by
    rw [← fourier_two_eq_wave, fourier_apply, Circle.norm_coe]
  rw [fourierCoeff_circleTranslation, norm_mul, hn, one_mul]

theorem fractionalTranslationEnergy_circleTranslation (s t : ℝ) (f : CircleL2) :
    fractionalTranslationEnergy s (circleTranslation t f) = fractionalTranslationEnergy s f :=
  translationEnergy_circleTranslation _ _ (measurable_fractionalTranslationKernel s) t f

/-- A single mode has exactly its diagonal fractional weight times its squared amplitude. -/
theorem fractionalTranslationEnergy_single (s : ℝ) (n : ℤ) (z : ℂ) :
    fractionalTranslationEnergy s (l2Synthesis (lp.single 2 n z)) =
      fractionalSpectralWeight s n * ENNReal.ofReal (‖z‖ ^ 2) := by
  rw [fractionalTranslationEnergy_eq_tsum]
  rw [tsum_eq_single n (by intro k hk; simp [fourierCoeff_l2Synthesis, lp.single_apply, hk])]
  simp [fourierCoeff_l2Synthesis, lp.single_apply]

/-- Constant functions have zero fractional seminorm, even with a singular kernel. -/
@[simp] theorem fractionalTranslationEnergy_constant (s : ℝ) (z : ℂ) :
    fractionalTranslationEnergy s (l2Synthesis (lp.single 2 0 z)) = 0 := by
  rw [fractionalTranslationEnergy_single, fractionalSpectralWeight_zero, zero_mul]

/-- Positive and negative frequencies have the same fractional energy weight. -/
theorem fractionalSpectralWeight_neg (s : ℝ) (n : ℤ) :
    fractionalSpectralWeight s (-n) = fractionalSpectralWeight s n := by
  unfold fractionalSpectralWeight translationSpectralWeight
  apply lintegral_congr
  intro t
  have he : wave (-n) t - 1 = starRingEnd ℂ (wave n t - 1) := by simp [wave_neg]
  rw [he, Complex.norm_conj]

end NLS.Fourier
