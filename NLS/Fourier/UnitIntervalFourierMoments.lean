import NLS.Fourier.HalfIntervalL2Identification
import NLS.Fourier.PeriodOneCoefficients

/-! # Fourier coefficients of physical unit-interval moments

The actual L2 coefficient norm contracts under multiplication by x^k on the unit interval, without matching endpoint values.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- Arbitrary interval L2 coefficients have the original period-one
normalization; matching endpoint values are not required. -/
theorem unitIntervalMemLpCoefficients_eq_periodOneCoefficient
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) (n : ℤ) :
    unitIntervalMemLpCoefficients f hf n = periodOneCoefficient f n := by
  rw [unitIntervalMemLpCoefficients_apply,intervalFourierCoefficient_eq_fourierCoeffOn (by norm_num)]
  rfl

/-- Parseval for the actual interval coefficient realization. -/
theorem norm_sq_unitIntervalMemLpCoefficients
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioc 0 1))) :
    ‖unitIntervalMemLpCoefficients f hf‖^2 = ∫ x in (0:ℝ)..1, ‖f x‖^2 := by
  have hs := lp.hasSum_norm (p := (2:ℝ≥0∞)) (by norm_num) (unitIntervalMemLpCoefficients f hf)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,
    unitIntervalMemLpCoefficients_eq_periodOneCoefficient,periodOneCoefficient] at hs
  have hi := hasSum_sq_fourierCoeffOn (by norm_num : (0:ℝ) < 1) hf
  simp only [sub_zero,inv_one,one_smul] at hi
  exact hs.unique hi

/-- Fourier coefficients of the kth physical moment on the unit interval. -/
def unitIntervalMomentCoefficients (f : ℝ → ℂ) (hf : Continuous f) (k : ℕ) : NLS.Coeff 2 :=
  unitIntervalMemLpCoefficients (fun x => (x:ℂ)^k*f x)
    (memLp_two_interval (by fun_prop) 0 1 (by norm_num))

@[simp] theorem unitIntervalMomentCoefficients_apply
    (f : ℝ → ℂ) (hf : Continuous f) (k : ℕ) (n : ℤ) :
    unitIntervalMomentCoefficients f hf k n =
      periodOneCoefficient (fun x => (x:ℂ)^k*f x) n :=
  unitIntervalMemLpCoefficients_eq_periodOneCoefficient _ _ _

/-- Physical moments contract the L2 Fourier norm uniformly in their
order, even though multiplication by x^k need not preserve endpoint values. -/
theorem norm_unitIntervalMomentCoefficients_le
    (f : ℝ → ℂ) (hf : Continuous f) (k : ℕ) :
    ‖unitIntervalMomentCoefficients f hf k‖ ≤
      ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖ := by
  have hm : Continuous (fun x : ℝ => (x:ℂ)^k*f x) := by fun_prop
  have hsq : ‖unitIntervalMomentCoefficients f hf k‖^2 ≤
      ‖unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num))‖^2 := by
    rw [unitIntervalMomentCoefficients,norm_sq_unitIntervalMemLpCoefficients,
      norm_sq_unitIntervalMemLpCoefficients]
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((hm.norm.pow 2).intervalIntegrable 0 1) ((hf.norm.pow 2).intervalIntegrable 0 1)
    intro x hx
    have hpow : ‖(x:ℂ)^k‖ ≤ 1 := by
      rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1]
      exact pow_le_one₀ hx.1 hx.2
    have hnorm : ‖(x:ℂ)^k*f x‖ ≤ ‖f x‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hpow
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith [norm_nonneg (unitIntervalMomentCoefficients f hf k),
    norm_nonneg (unitIntervalMemLpCoefficients f (memLp_two_interval hf 0 1 (by norm_num)))]

end NLS.Fourier
