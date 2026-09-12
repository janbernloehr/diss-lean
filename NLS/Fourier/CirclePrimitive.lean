import NLS.Fourier.SobolevSynthesis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Integrating the period-two Hilbert realization

Pullback of a circle `L²` representative is square integrable on a full period.
Integration from zero to any point of `[0,2]` is a bounded linear functional on
that Hilbert space, independently of the chosen almost-everywhere representative.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.Fourier

abbrev CircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := (2 : ℝ)))

/-- The real-line representative obtained from the circle covering map. -/
def circlePullback (f : CircleL2) (x : ℝ) : ℂ := f (x : AddCircle (2 : ℝ))

theorem memLp_circlePullback (f : CircleL2) :
    MemLp (circlePullback f) 2 (volume.restrict (Ioc 0 2)) := by
  change MemLp (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 2 (volume.restrict (Ioc 0 2))
  simpa only [zero_add, Function.comp_def] using
    (Lp.memLp f).of_haarAddCircle.comp_measurePreserving (AddCircle.measurePreserving_mk 2 0)

theorem intervalIntegrable_circlePullback (f : CircleL2) :
    IntervalIntegrable (circlePullback f) volume 0 2 :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    ((memLp_circlePullback f).integrable (by norm_num))

/-- Almost-everywhere equality on the normalized circle pulls back to a full period. -/
theorem circle_ae_pullback {f g : AddCircle (2 : ℝ) → ℂ}
    (h : f =ᵐ[AddCircle.haarAddCircle] g) :
    (fun x : ℝ => f (x : AddCircle (2 : ℝ))) =ᵐ[volume.restrict (Ioc 0 2)]
      (fun x : ℝ => g (x : AddCircle (2 : ℝ))) := by
  have hv : f =ᵐ[volume] g := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure h _
  simpa only [Function.comp_def, zero_add] using
    (AddCircle.measurePreserving_mk 2 0).quasiMeasurePreserving.ae_eq_comp hv

/-- The integral of the norm on a full physical period is bounded by twice the Hilbert norm. -/
theorem integral_norm_circlePullback_le (f : CircleL2) :
    (∫ t in (0 : ℝ)..2, ‖circlePullback f t‖) ≤ 2 * ‖f‖ := by
  have h : (∫ t, ‖f t‖ ∂AddCircle.haarAddCircle) ≤ ‖f‖ := by
    rw [integral_norm_eq_lintegral_enorm (Lp.memLp f).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.memLp f).aestronglyMeasurable)
  have he := AddCircle.intervalIntegral_preimage 2 0 (fun t => ‖f t‖)
  simp only [zero_add, AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), smul_eq_mul] at he
  exact he.trans_le (mul_le_mul_of_nonneg_left h (by norm_num))

/-- The primitive evaluated at a physical point. -/
def circlePrimitive (x : ℝ) (f : CircleL2) : ℂ := ∫ t in (0 : ℝ)..x, circlePullback f t

theorem norm_circlePrimitive_le {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) (f : CircleL2) :
    ‖circlePrimitive x f‖ ≤ 2 * ‖f‖ := by
  calc
    ‖circlePrimitive x f‖ ≤ ∫ t in (0 : ℝ)..x, ‖circlePullback f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hx.1
    _ ≤ ∫ t in (0 : ℝ)..2, ‖circlePullback f t‖ :=
      intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
        (Filter.Eventually.of_forall (fun t => norm_nonneg _))
        (intervalIntegrable_circlePullback f).norm
    _ ≤ 2 * ‖f‖ := integral_norm_circlePullback_le f

private theorem primitive_congr {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioc 0 2)] g) :
    (∫ t in (0 : ℝ)..x, f t) = ∫ t in (0 : ℝ)..x, g t := by
  rw [intervalIntegral.integral_of_le hx.1, intervalIntegral.integral_of_le hx.1]
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (Ioc_subset_Ioc le_rfl hx.2) h)

/-- Bounded linear integration on the normalized circle Hilbert space. -/
def circlePrimitiveCLM (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) : CircleL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := circlePrimitive x
      map_add' := fun f g => by
        change (∫ t in (0 : ℝ)..x, (f + g) (t : AddCircle (2 : ℝ))) = _
        rw [primitive_congr hx (circle_ae_pullback (Lp.coeFn_add f g))]
        exact intervalIntegral.integral_add
          ((intervalIntegrable_circlePullback f).mono_set (uIcc_subset_uIcc (by simp) (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hx)))
          ((intervalIntegrable_circlePullback g).mono_set (uIcc_subset_uIcc (by simp) (by simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] using hx)))
      map_smul' := fun c f => by
        change (∫ t in (0 : ℝ)..x, (c • f) (t : AddCircle (2 : ℝ))) = _
        rw [primitive_congr hx (circle_ae_pullback (Lp.coeFn_smul c f))]
        exact intervalIntegral.integral_smul c (circlePullback f) }
    2 (norm_circlePrimitive_le hx)

@[simp] theorem circlePrimitiveCLM_apply (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 2) (f : CircleL2) :
    circlePrimitiveCLM x hx f = circlePrimitive x f := rfl

/-- For a continuous circle function, the Hilbert-space primitive is its physical integral. -/
theorem circlePrimitive_toLp {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2)
    (f : C(AddCircle (2 : ℝ), ℂ)) :
    circlePrimitive x (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f) =
      ∫ t in (0 : ℝ)..x, f (t : AddCircle (2 : ℝ)) :=
  primitive_congr hx (circle_ae_pullback (ContinuousMap.coeFn_toLp AddCircle.haarAddCircle f))

/-- The Fourier coefficients of the Hilbert representative use the physical interval normalization. -/
theorem periodTwoCoefficient_circlePullback (f : CircleL2) (n : ℤ) :
    periodTwoCoefficient (circlePullback f) n = fourierCoeff f n := by
  rw [fourierCoeff_eq_intervalIntegral f n 0]
  simp only [zero_add, fourier_two_eq_wave, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    periodTwoCoefficient, circlePullback]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  exact mul_comm _ _

end NLS.Fourier
