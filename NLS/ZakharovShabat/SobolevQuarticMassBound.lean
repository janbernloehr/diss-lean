import NLS.ZakharovShabat.SourceSobolevEnergyCoercivity

/-! # The quartic interaction dominates squared mass on a unit period -/
noncomputable section
open MeasureTheory NLS.Fourier
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- The variance of a continuous real function on a unit interval is nonnegative. -/
theorem unit_interval_mean_sq_le (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x in (0:ℝ)..1, f x)^2 ≤ ∫ x in (0:ℝ)..1, (f x)^2 := by
  let M := ∫ x in (0:ℝ)..1, f x
  have hi := hf.intervalIntegrable (μ := volume) 0 1
  have hi2 : IntervalIntegrable (fun x => (f x)^2) volume 0 1 :=
    (hf.pow 2).intervalIntegrable (μ := volume) 0 1
  have hil : IntervalIntegrable (fun x => (2*M)*f x) volume 0 1 := hi.const_mul (2*M)
  have his : IntervalIntegrable (fun x => (f x)^2-(2*M)*f x) volume 0 1 := hi2.sub hil
  have hpos : 0 ≤ ∫ x in (0:ℝ)..1, (f x-M)^2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun x _ => sq_nonneg _)
  have he : (fun x => (f x-M)^2) = fun x => (f x)^2-(2*M)*f x+M^2 := by
    funext x
    ring
  rw [he, intervalIntegral.integral_add his intervalIntegrable_const,
    intervalIntegral.integral_sub hi2 hil, intervalIntegral.integral_const_mul] at hpos
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at hpos
  change M^2 ≤ _
  change 0 ≤ (∫ x in (0:ℝ)..1, (f x)^2)-2*M*M+M^2 at hpos
  nlinarith

/-- The real physical mass is the integral of the squared amplitude. -/
theorem periodOneSobolevMass_re_eq_integral_norm_sq (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevMass a.val).re = ∫ x in (0:ℝ)..1,
      ‖periodOneSobolevSynthesis a.val.1 (x : AddCircle (2:ℝ))‖^2 := by
  rw [periodOneSobolevMass_eq_integral]
  have hi := ((continuous_periodOneSobolevSynthesis a.val.1).mul
    (continuous_periodOneSobolevSynthesis a.val.2)).intervalIntegrable (μ := volume) 0 1
  have he := (intervalIntegral.intervalIntegral_re hi).symm
  change (∫ x in (0:ℝ)..1, periodOneSobolevSynthesis a.val.1 (x : AddCircle (2:ℝ))*
    periodOneSobolevSynthesis a.val.2 (x : AddCircle (2:ℝ))).re = _ at he
  rw [he]
  apply intervalIntegral.integral_congr
  intro x _
  change (periodOneSobolevSynthesis a.val.1 (x : AddCircle (2:ℝ))*
    periodOneSobolevSynthesis a.val.2 (x : AddCircle (2:ℝ))).re = _
  rw [periodOneSobolevSynthesis_real, Complex.mul_conj']
  norm_cast

/-- The real quartic energy is the integral of the fourth power of the amplitude. -/
theorem periodOneSobolevQuartic_re_eq_integral_norm_four (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevQuartic a.val).re = ∫ x in (0:ℝ)..1,
      ‖periodOneSobolevSynthesis a.val.1 (x : AddCircle (2:ℝ))‖^4 := by
  rw [periodOneSobolevQuartic_eq_integral]
  have hi := (((continuous_periodOneSobolevSynthesis a.val.1).pow 2).mul
    ((continuous_periodOneSobolevSynthesis a.val.2).pow 2)).intervalIntegrable (μ := volume) 0 1
  have he := (intervalIntegral.intervalIntegral_re hi).symm
  change (∫ x in (0:ℝ)..1, (periodOneSobolevSynthesis a.val.1 (x : AddCircle (2:ℝ)))^2*
    (periodOneSobolevSynthesis a.val.2 (x : AddCircle (2:ℝ)))^2).re = _ at he
  rw [he]
  apply intervalIntegral.integral_congr
  intro x _
  change ((periodOneSobolevSynthesis a.val.1 (x : AddCircle (2:ℝ)))^2*
    (periodOneSobolevSynthesis a.val.2 (x : AddCircle (2:ℝ)))^2).re = _
  rw [periodOneSobolevSynthesis_real, ← mul_pow, Complex.mul_conj']
  norm_cast
  ring

/-- The unit-period quartic interaction is at least the square of the physical mass. -/
theorem periodOneSobolevMass_sq_le_quartic (a : realTypeSobolevSourceLocus) :
    (periodOneSobolevMass a.val).re^2 ≤ (periodOneSobolevQuartic a.val).re := by
  rw [periodOneSobolevMass_re_eq_integral_norm_sq, periodOneSobolevQuartic_re_eq_integral_norm_four]
  have h := unit_interval_mean_sq_le
    (fun x : ℝ => ‖periodOneSobolevSynthesis a.val.1 (x : AddCircle (2:ℝ))‖^2)
    ((continuous_periodOneSobolevSynthesis a.val.1).norm.pow 2)
  simpa only [← pow_mul, show 2*2=4 from rfl] using h

end NLS.ZakharovShabat
