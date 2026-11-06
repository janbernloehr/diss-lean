import NLS.Fourier.ContinuousPeriodOneRealization

/-! # Bounded Fourier analysis of continuous unit-interval curves -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open scoped ENNReal
open NLS.LinearVolterra
namespace NLS.Fourier

private theorem memlp_unitCurveCoefficients (f : Curve ℂ) :
    Memℓp (periodOneCoefficient (extend f)) 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    (hasSum_sq_periodOneCoefficient (memLp_two_interval (continuous_extend f) 0 1 (by norm_num))).summable

/-- Actual normalized unit-interval Fourier integrals. Endpoint matching
is not required for this bounded L2 analysis map. -/
def unitCurveCoefficients (f : Curve ℂ) : Coeff 2 :=
  ⟨periodOneCoefficient (extend f),memlp_unitCurveCoefficients f⟩

@[simp] theorem unitCurveCoefficients_apply (f : Curve ℂ) (n : ℤ) :
    unitCurveCoefficients f n=periodOneCoefficient (extend f) n := rfl

theorem norm_sq_unitCurveCoefficients (f : Curve ℂ) :
    ‖unitCurveCoefficients f‖^2=∫ x in (0:ℝ)..1, ‖extend f x‖^2 := by
  have hs := lp.hasSum_norm (p := (2:ℝ≥0∞)) (by norm_num) (unitCurveCoefficients f)
  simp only [ENNReal.toReal_ofNat,Real.rpow_two,unitCurveCoefficients_apply] at hs
  exact hs.unique (hasSum_sq_periodOneCoefficient (memLp_two_interval (continuous_extend f) 0 1 (by norm_num)))

theorem norm_unitCurveCoefficients_le (f : Curve ℂ) : ‖unitCurveCoefficients f‖≤‖f‖ := by
  have hi : (∫ x in (0:ℝ)..1, ‖extend f x‖^2)≤‖f‖^2 := by
    calc
      _ ≤ ∫ x in (0:ℝ)..1, ‖f‖^2 := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (((continuous_extend f).norm.pow 2).intervalIntegrable 0 1) (intervalIntegrable_const)
        intro x _
        exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm _) 2
      _ = _ := by simp
  rw [← norm_sq_unitCurveCoefficients] at hi
  nlinarith [norm_nonneg (unitCurveCoefficients f),norm_nonneg f]

/-- The Fourier analysis map is bounded and complex linear, with norm at
most one in the physical unit-period convention. -/
def unitCurveCoefficientsCLM : Curve ℂ →L[ℂ] Coeff 2 :=
  LinearMap.mkContinuous
    { toFun := unitCurveCoefficients
      map_add' := by
        intro f g
        ext n
        change periodOneCoefficient (extend (f+g)) n =
          periodOneCoefficient (extend f) n+periodOneCoefficient (extend g) n
        simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,
          unitFourierCoefficient,NLS.LinearVolterra.extend,ContinuousMap.add_apply,add_mul]
        exact intervalIntegral.integral_add
          (((continuous_extend f).mul (continuous_wave _)).intervalIntegrable 0 1)
          (((continuous_extend g).mul (continuous_wave _)).intervalIntegrable 0 1)
      map_smul' := by
        intro c f
        ext n
        change periodOneCoefficient (extend (c • f)) n=c*periodOneCoefficient (extend f) n
        simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,
          unitFourierCoefficient,NLS.LinearVolterra.extend,ContinuousMap.smul_apply,smul_eq_mul,mul_assoc]
        exact intervalIntegral.integral_const_mul c _ }
    1 (fun f => by
      change ‖unitCurveCoefficients f‖≤1*‖f‖
      simpa only [one_mul] using norm_unitCurveCoefficients_le f)

@[simp] theorem unitCurveCoefficientsCLM_apply (f : Curve ℂ) :
    unitCurveCoefficientsCLM f=unitCurveCoefficients f := rfl

/-- Existing endpoint-matching Fourier realizations use this same bounded
analysis map, so their parameter integrals are legitimate Banach integrals. -/
theorem unitCurveCoefficients_eq_continuousPeriodOneCoefficients (f : Curve ℂ)
    (he : extend f 0=extend f 1) :
    unitCurveCoefficients f=continuousPeriodOneCoefficients (extend f) (continuous_extend f) he := by
  ext n
  rw [unitCurveCoefficients_apply,continuousPeriodOneCoefficients_apply]

end NLS.Fourier
