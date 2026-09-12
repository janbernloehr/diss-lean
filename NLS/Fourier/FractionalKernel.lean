import NLS.Fourier.FractionalTranslationEnergy
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The integrable fractional model kernel

The squared unit-frequency phase cancels the singularity at zero for `s < 1`.
Its boundedness controls the tails for `s > 0`. These are the analytic estimates
behind comparison of the physical fractional seminorm with Sobolev weights.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The real unit-frequency fractional kernel; its value at zero is zero. -/
def fractionalModelKernel (s x : ℝ) : ℝ := ‖wave 1 x - 1‖ ^ 2 * |x| ^ (-(1 + 2 * s))

theorem fractionalModelKernel_nonneg (s x : ℝ) : 0 ≤ fractionalModelKernel s x :=
  mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)

@[simp] theorem fractionalModelKernel_zero (s : ℝ) : fractionalModelKernel s 0 = 0 := by
  simp [fractionalModelKernel]

theorem measurable_fractionalModelKernel (s : ℝ) : Measurable (fractionalModelKernel s) := by
  unfold fractionalModelKernel
  fun_prop

/-- The phase increment is bounded linearly by displacement. -/
theorem norm_wave_one_sub_one_le (x : ℝ) : ‖wave 1 x - 1‖ ≤ Real.pi * |x| := by
  have he : wave 1 x = Complex.exp (Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
    unfold wave
    congr 1
    push_cast
    ring
  rw [he]
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := Real.pi * x))

/-- The phase increment is bounded independently of displacement. -/
theorem norm_wave_one_sub_one_le_two (x : ℝ) : ‖wave 1 x - 1‖ ≤ 2 := by
  have hw : ‖wave 1 x‖ = 1 := by rw [← fourier_two_eq_wave, fourier_apply, Circle.norm_coe]
  simpa only [hw, norm_one, one_add_one_eq_two] using norm_sub_le (wave 1 x) (1 : ℂ)

/-- Quadratic cancellation gives an integrable power near zero when `s < 1`. -/
theorem fractionalModelKernel_le_near (s x : ℝ) :
    fractionalModelKernel s x ≤ Real.pi ^ 2 * |x| ^ (1 - 2 * s) := by
  by_cases hx : x = 0
  · subst x
    rw [fractionalModelKernel_zero]
    positivity
  have hsq : ‖wave 1 x - 1‖ ^ 2 ≤ (Real.pi * |x|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_wave_one_sub_one_le x) 2
  apply (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (abs_nonneg _) _)).trans_eq
  rw [mul_pow, mul_assoc, ← Real.rpow_two |x|, ← Real.rpow_add (abs_pos.mpr hx)]
  congr 2
  ring

/-- The tail is bounded by an integrable negative power when `s > 0`. -/
theorem fractionalModelKernel_le_far (s x : ℝ) :
    fractionalModelKernel s x ≤ 4 * |x| ^ (-(1 + 2 * s)) := by
  have hsq : ‖wave 1 x - 1‖ ^ 2 ≤ (4 : ℝ) := by
    have hh := norm_wave_one_sub_one_le_two x
    nlinarith [norm_nonneg (wave 1 x - 1)]
  exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (abs_nonneg _) _)

@[simp] theorem fractionalModelKernel_neg (s x : ℝ) :
    fractionalModelKernel s (-x) = fractionalModelKernel s x := by
  have he : wave 1 (-x) - 1 = starRingEnd ℂ (wave 1 x - 1) := by
    have hw : wave 1 (-x) = wave (-1) x := by simp [wave]
    rw [hw]
    simp [wave_neg]
  simp only [fractionalModelKernel, he, Complex.norm_conj, abs_neg]

/-- The unit-frequency kernel is globally integrable for the full fractional range. -/
theorem integrable_fractionalModelKernel {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) :
    Integrable (fractionalModelKernel s) := by
  have hm : AEStronglyMeasurable (fractionalModelKernel s) volume :=
    (measurable_fractionalModelKernel s).aestronglyMeasurable
  have hnear : IntegrableOn (fractionalModelKernel s) (Metric.ball 0 2) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp) (α := 2 * s - 1) (C := Real.pi ^ 2)
      (by simpa using (show 2 * s - 1 < (1 : ℝ) by linarith)) _ hm
    apply Filter.Eventually.of_forall
    intro x
    simpa only [Real.norm_of_nonneg (fractionalModelKernel_nonneg s x), Real.norm_eq_abs,
      neg_sub] using fractionalModelKernel_le_near s x
  have hpos : IntegrableOn (fractionalModelKernel s) (Ioi 1) := by
    apply ((integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + 2 * s) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul 4).mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    simpa only [Real.norm_of_nonneg (fractionalModelKernel_nonneg s x), abs_of_pos (by linarith : 0 < x)]
      using fractionalModelKernel_le_far s x
  have hneg : IntegrableOn (fractionalModelKernel s) (Iio (-1)) := by
    have hn := ((Measure.measurePreserving_neg volume).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding).mpr hpos
    have he : (Neg.neg ⁻¹' Ioi (1 : ℝ)) = Iio (-1) := by
      ext x
      simp only [mem_preimage, mem_Ioi, mem_Iio]
      constructor <;> intro hx <;> linarith
    simpa only [Function.comp_def, fractionalModelKernel_neg, he] using hn
  have hall := hnear.union (hpos.union hneg)
  apply integrableOn_univ.mp (hall.mono_set _)
  intro x _
  simp only [mem_union, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, mem_Ioi, mem_Iio]
  by_cases hx : |x| < 2
  · exact Or.inl hx
  · have hh := le_abs.mp (le_of_not_gt hx)
    rcases hh with hh | hh
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))

/-- The kernel is strictly positive between the zero-frequency phase crossings. -/
theorem fractionalModelKernel_pos {s x : ℝ} (hx : 0 < x) (hx₂ : x < 2) :
    0 < fractionalModelKernel s x := by
  have he : wave 1 x = Complex.exp (Complex.I * ((Real.pi * x : ℝ) : ℂ)) := by
    unfold wave
    congr 1
    push_cast
    ring
  have hsin : 0 < Real.sin (Real.pi * x / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  apply mul_pos _ (Real.rpow_pos_of_pos (abs_pos.mpr hx.ne') _)
  apply sq_pos_of_pos
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  exact norm_pos_iff.mpr (mul_ne_zero (by norm_num) hsin.ne')

/-- Positive mass on a fixed physical subinterval supplies a frequency-independent lower constant. -/
theorem fractionalModelKernel_core_pos {s : ℝ} (hs : 0 < s) (hs₁ : s < 1) :
    0 < ∫ x in (0 : ℝ)..1, fractionalModelKernel s x := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((integrable_fractionalModelKernel hs hs₁).intervalIntegrable)
    (fun x hx => fractionalModelKernel_pos hx.1 (hx.2.trans (by norm_num))) (by norm_num)

end NLS.Fourier
