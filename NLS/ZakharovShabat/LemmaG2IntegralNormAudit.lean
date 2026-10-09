import NLS.ZakharovShabat.IntervalH1OperatorBound
import NLS.ComplexAnalysis.OscillatoryIntegralConstant

/-! # A norm-qualified audit of G.2's arbitrary-time first estimate

With the unnormalized integral H1 norm, the first estimate fails even for
a smooth constant periodic potential. This is not a claim about every
possible interpretation of the source's unspecified interval norm, nor
about its unit-interval remainder consequence (proved in the imported file).
-/
noncomputable section
open Set MeasureTheory
open NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- A smooth, period-one potential with one nonzero component. -/
def g2IntegralNormTestPotential (_ : ℝ) : ℂ × ℂ := (1,0)

private theorem sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2^2 by norm_num,Real.sqrt_sq (by norm_num)]

/-- The local integral H1 norm of the constant potential shrinks with
interval length. At t=1/4 it is exactly one half. -/
theorem g2IntegralNormTestPotential_norm_quarter :
    intervalPairH1Norm g2IntegralNormTestPotential (1/4) = 1/2 := by
  norm_num [intervalPairH1Norm,intervalH1Norm,g2IntegralNormTestPotential,
    Real.sqrt_div,sqrt_four]

/-- The actual weighted Hermitian first Born norm at z=2*pi and t=1/4. -/
theorem g2IntegralNormTestPotential_firstBorn_quarter :
    Real.exp (-(|(2*Real.pi : ℂ).im| * (1/4 : ℝ)))*
      ‖intervalHermitianFirstBornOperator g2IntegralNormTestPotential (2*Real.pi) (1/4)‖ =
      1/(2*Real.pi) := by
  have hc : Complex.I*(2*Real.pi) ≠ (0 : ℂ) :=
    mul_ne_zero Complex.I_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hm : oscillatoryIntegral (-Complex.I*(2*Real.pi)) (1/4) (fun _ => (1 : ℂ)) =
      (1/(2*Real.pi) : ℝ) := by
    rw [neg_mul,oscillatoryIntegral_neg_const _ hc,oscillatoryIntegral_const_quarter_period]
  rw [norm_intervalHermitianFirstBornOperator]
  dsimp only [g2IntegralNormTestPotential]
  rw [hm]
  simp [oscillatoryIntegral,Real.pi_pos.le]

/-- The literal first inequality with the integral norm has a strict
counterexample: its right side is 5/(16*pi), its left side is 1/(2*pi). -/
theorem lemmaG2_firstBorn_integralNorm_counterexample :
    (2+Real.sqrt (1/4 : ℝ))/(2*‖(2*Real.pi : ℂ)‖)*
        intervalPairH1Norm g2IntegralNormTestPotential (1/4) <
      Real.exp (-(|(2*Real.pi : ℂ).im| * (1/4 : ℝ)))*
        ‖intervalHermitianFirstBornOperator g2IntegralNormTestPotential (2*Real.pi) (1/4)‖ := by
  rw [g2IntegralNormTestPotential_norm_quarter,g2IntegralNormTestPotential_firstBorn_quarter]
  norm_num [Real.sqrt_div,sqrt_four,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  field_simp
  linarith [Real.pi_pos]

/-- The test is within the regularity and nonzero-frequency scope of G.2. -/
theorem g2IntegralNormTestPotential_admissible :
    ContDiff ℝ ⊤ g2IntegralNormTestPotential ∧ Function.Periodic g2IntegralNormTestPotential 1 ∧
      (2*Real.pi : ℂ) ≠ 0 := by
  refine ⟨contDiff_const,fun _ => rfl,?_⟩
  exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

end NLS.ZakharovShabat
