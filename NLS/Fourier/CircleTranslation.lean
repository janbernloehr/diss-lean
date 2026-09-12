import NLS.Fourier.IntervalL2Realization
import NLS.Fourier.PeriodOneCoefficients
import NLS.SequenceSpaces.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral

/-!
# Physical translations in periodic L²

Translation acts on actual almost-everywhere circle functions by a linear
isometry. Its Fourier multiplier is the physical phase `exp(iπnt)`, and
Parseval gives the exact energy of each translation increment.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Actual translation of the periodic `L²` function by a real displacement. -/
def circleTranslation (t : ℝ) : CircleL2 →ₗᵢ[ℂ] CircleL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : AddCircle (2 : ℝ) => (t : AddCircle (2 : ℝ)) + x)
    (measurePreserving_add_left AddCircle.haarAddCircle (t : AddCircle (2 : ℝ)))

/-- The translated equivalence class is represented by the ordinary translated function. -/
theorem coeFn_circleTranslation (t : ℝ) (f : CircleL2) :
    circleTranslation t f =ᵐ[AddCircle.haarAddCircle]
      fun x : AddCircle (2 : ℝ) => f ((t : AddCircle (2 : ℝ)) + x) :=
  Lp.coeFn_compMeasurePreserving _ _

@[simp] theorem norm_circleTranslation (t : ℝ) (f : CircleL2) : ‖circleTranslation t f‖ = ‖f‖ :=
  (circleTranslation t).norm_map f

/-- The period-two covering map gives actual translation on the physical interval. -/
theorem circlePullback_circleTranslation (t : ℝ) (f : CircleL2) :
    circlePullback (circleTranslation t f) =ᵐ[volume.restrict (Ioc 0 2)]
      fun x : ℝ => circlePullback f (t + x) := by
  simpa only [circlePullback, AddCircle.coe_add] using! circle_ae_pullback (coeFn_circleTranslation t f)

private theorem fourier_translate_kernel (n : ℤ) (t : ℝ) (x : AddCircle (2 : ℝ)) :
    fourier (-n) (x - (t : AddCircle (2 : ℝ))) = wave n t * fourier (-n) x := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    change fourier (-n) ((x - t : ℝ) : AddCircle (2 : ℝ)) = _
    rw [fourier_two_eq_wave, fourier_two_eq_wave]
    unfold wave
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- The Fourier coefficient of actual translation has the positive phase sign. -/
theorem fourierCoeff_circleTranslation (t : ℝ) (f : CircleL2) (n : ℤ) :
    fourierCoeff (circleTranslation t f) n = wave n t * fourierCoeff f n := by
  rw [fourierCoeff_congr_ae (coeFn_circleTranslation t f)]
  have hi := integral_add_left_eq_self
    (fun x : AddCircle (2 : ℝ) => fourier (-n) (x - (t : AddCircle (2 : ℝ))) * f x)
    (t : AddCircle (2 : ℝ)) (μ := AddCircle.haarAddCircle)
  simp only [add_sub_cancel_left] at hi
  change (∫ x : AddCircle (2 : ℝ), fourier (-n) x * f ((t : AddCircle (2 : ℝ)) + x)
    ∂AddCircle.haarAddCircle) = _
  rw [hi]
  simp only [fourier_translate_kernel, mul_assoc, integral_const_mul, fourierCoeff, smul_eq_mul]

/-- The Fourier coefficients of a translation increment. -/
theorem fourierCoeff_circleTranslation_sub (t : ℝ) (f : CircleL2) (n : ℤ) :
    fourierCoeff (circleTranslation t f - f) n = (wave n t - 1) * fourierCoeff f n := by
  rw [← fourierBasis_repr, map_sub]
  simp only [lp.coeFn_sub, Pi.sub_apply, fourierBasis_repr, fourierCoeff_circleTranslation]
  ring

/-- Exact normalized Parseval energy for physical translation increments. -/
theorem hasSum_sq_circleTranslation_sub (t : ℝ) (f : CircleL2) :
    HasSum (fun n : ℤ => ‖wave n t - 1‖ ^ 2 * ‖fourierCoeff f n‖ ^ 2)
      (‖circleTranslation t f - f‖ ^ 2) := by
  have hs := lp.hasSum_norm (p := 2) (by norm_num) (fourierBasis.repr (circleTranslation t f - f))
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fourierBasis_repr,
    fourierCoeff_circleTranslation_sub, norm_mul, mul_pow, LinearIsometryEquiv.norm_map] using hs

/-- Translation increments are uniformly controlled without a regularity hypothesis. -/
theorem norm_circleTranslation_sub_le (t : ℝ) (f : CircleL2) :
    ‖circleTranslation t f - f‖ ≤ 2 * ‖f‖ := by
  exact (norm_sub_le _ _).trans (by rw [norm_circleTranslation]; ring_nf; rfl)

@[simp] theorem circleTranslation_zero (f : CircleL2) : circleTranslation 0 f = f := by
  apply fourierBasis.repr.injective
  ext n
  simp [fourierBasis_repr, fourierCoeff_circleTranslation]

/-- Translations compose by addition of physical displacements. -/
theorem circleTranslation_add (s t : ℝ) (f : CircleL2) :
    circleTranslation (s + t) f = circleTranslation s (circleTranslation t f) := by
  apply fourierBasis.repr.injective
  ext n
  simp only [fourierBasis_repr, fourierCoeff_circleTranslation, wave_add_argument, mul_assoc]

@[simp] theorem circleTranslation_neg (t : ℝ) (f : CircleL2) :
    circleTranslation (-t) (circleTranslation t f) = f := by
  rw [← circleTranslation_add, neg_add_cancel, circleTranslation_zero]

/-- Actual interval increments represent the translated difference class almost everywhere. -/
theorem circlePullback_circleTranslation_sub (t : ℝ) (f : CircleL2) :
    circlePullback (circleTranslation t f - f) =ᵐ[volume.restrict (Ioc 0 2)]
      fun x : ℝ => circlePullback f (t + x) - circlePullback f x := by
  have hg := circle_ae_pullback (Lp.coeFn_sub (circleTranslation t f) f)
  have ht := circlePullback_circleTranslation t f
  filter_upwards [hg, ht] with x hx hx'
  change (circleTranslation t f - f) (x : AddCircle (2 : ℝ)) = _
  rw [hx]
  change circlePullback (circleTranslation t f) x - circlePullback f x = _
  rw [hx']

/-- Every translated physical increment is square integrable on a period. -/
theorem memLp_circlePullback_increment (t : ℝ) (f : CircleL2) :
    MemLp (fun x : ℝ => circlePullback f (t + x) - circlePullback f x) 2
      (volume.restrict (Ioc 0 2)) :=
  (memLp_congr_ae (circlePullback_circleTranslation_sub t f)).mp
    (memLp_circlePullback (circleTranslation t f - f))

/-- Normalized increment energy equals half the physical interval integral. -/
theorem norm_sq_circleTranslation_sub (t : ℝ) (f : CircleL2) :
    ‖circleTranslation t f - f‖ ^ 2 = (1 / 2 : ℝ) *
      ∫ x in (0 : ℝ)..2, ‖circlePullback f (t + x) - circlePullback f x‖ ^ 2 := by
  let g := circleTranslation t f - f
  have he : periodTwoL2Coefficients (circlePullback g) (memLp_circlePullback g) =
      fourierBasis.repr g := by
    ext n
    simp only [periodTwoL2Coefficients_apply, periodTwoCoefficient_circlePullback, fourierBasis_repr]
  have hp := norm_sq_periodTwoL2Coefficients (circlePullback g) (memLp_circlePullback g)
  rw [he, LinearIsometryEquiv.norm_map] at hp
  rw [hp]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  have hg := circle_ae_pullback (Lp.coeFn_sub (circleTranslation t f) f)
  have ht := circlePullback_circleTranslation t f
  have hi : (Set.uIoc (0 : ℝ) 2) = Ioc 0 2 := by simp
  rw [hi]
  filter_upwards [hg, ht] with x hx hx'
  change ‖g (x : AddCircle (2 : ℝ))‖ ^ 2 = _
  rw [hx]
  change ‖circlePullback (circleTranslation t f) x - circlePullback f x‖ ^ 2 = _
  rw [hx']

/-- Real displacements act strongly continuously on arbitrary periodic `L²` data. -/
theorem continuous_circleTranslation (f : CircleL2) : Continuous (fun t : ℝ => circleTranslation t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let a := fourierBasis.repr f
  let b := fun t : ℝ => fourierBasis.repr (circleTranslation t f - circleTranslation t₀ f)
  have hb (t : ℝ) (n : ℤ) : b t n = (wave n t - wave n t₀) * a n := by
    simp only [b, a, map_sub, lp.coeFn_sub, Pi.sub_apply, fourierBasis_repr,
      fourierCoeff_circleTranslation]
    ring
  have hw (n : ℤ) (t : ℝ) : ‖wave n t‖ = 1 := by
    rw [← fourier_two_eq_wave, fourier_apply, Circle.norm_coe]
  have hlim : Filter.Tendsto b (nhds t₀) (nhds 0) := by
    apply Coeff.tendsto_zero_of_dominated (by simp) b ((2 : ℂ) • a)
    · apply Filter.Eventually.of_forall
      intro t n
      rw [hb, norm_mul]
      have hbound : ‖wave n t - wave n t₀‖ ≤ 2 := by
        simpa only [hw, one_add_one_eq_two] using norm_sub_le (wave n t) (wave n t₀)
      simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_ofNat] using
        mul_le_mul_of_nonneg_right hbound (norm_nonneg (a n))
    · intro n
      simp only [hb]
      have hc := (((continuous_wave n).sub (continuous_const (y := wave n t₀))).mul
        (continuous_const (y := a n))).tendsto t₀
      simpa only [Pi.mul_apply, Pi.sub_apply, sub_self, zero_mul] using! hc
  have hs := l2Synthesis.continuous.tendsto 0 |>.comp hlim
  have hz : Filter.Tendsto (fun t : ℝ => circleTranslation t f - circleTranslation t₀ f)
      (nhds t₀) (nhds 0) := by
    simpa only [b, l2Synthesis, Function.comp_def, LinearIsometryEquiv.symm_apply_apply, map_zero] using hs
  exact tendsto_sub_nhds_zero_iff.mp hz

end NLS.Fourier
