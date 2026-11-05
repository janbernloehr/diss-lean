import NLS.SequenceSpaces.PeriodOneMassSobolevInverse
import NLS.SequenceSpaces.SobolevConvolutionBounds
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The nonlinear part of the original weak Miura inverse gains two
orders over L2 forcing. The formula is an analytic polynomial of the
H1 lift, and its identification uses the original period-one equation. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

def periodOneMiuraSmoothingRemainder (u : ZakharovShabat.ScalarDomain 2) :
    WeightedCoeff (Weight.sobolev (1 + 1)) 2 :=
  periodOneMassSobolevInverse 1 0 2
    (u - WeightedCoeff.sobolevConvolutionCLM (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) u u)

theorem analyticAt_periodOneMiuraSmoothingRemainder (u : ZakharovShabat.ScalarDomain 2) :
    AnalyticAt ℂ periodOneMiuraSmoothingRemainder u := by
  have hconv : AnalyticAt ℂ (fun v : ZakharovShabat.ScalarDomain 2 =>
      WeightedCoeff.sobolevConvolutionCLM (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) v v) u :=
    ((WeightedCoeff.sobolevConvolutionCLM (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).analyticAt_bilinear _).comp₂
      analyticAt_id analyticAt_id
  exact ((periodOneMassSobolevInverse 1 0 2).analyticAt _).comp (analyticAt_id.sub hconv)

theorem periodOneMiuraSmoothingRemainder_apply (u : ZakharovShabat.ScalarDomain 2) (k : ℤ) :
    (periodOneMiuraSmoothingRemainder u).val k =
      (periodOneMassSymbol 0 k)⁻¹ * (u.val k - ∑' j : ℤ, u.val (k-j) * u.val j) := by
  rw [periodOneMiuraSmoothingRemainder, periodOneMassSobolevInverse_apply]
  simp only [WeightedCoeff.sub_val,
    WeightedCoeff.sobolevConvolutionCLM_apply, ZakharovShabat.sobolevConvolution_apply]

theorem periodOneMiuraSmoothingRemainder_apply_of_equation
    (q : Coeff 2) (u : ZakharovShabat.ScalarDomain 2)
    (h : ∀ k : ℤ, 2 * I * (Real.pi : ℂ) * k * u.val k +
      ∑' j : ℤ, u.val (k-j) * u.val j = q k) (k : ℤ) :
    (periodOneMiuraSmoothingRemainder u).val k =
      u.val k - (periodOneMassSymbol 0 k)⁻¹ * q k := by
  rw [periodOneMiuraSmoothingRemainder_apply]
  have hm : u.val k - (∑' j : ℤ, u.val (k-j) * u.val j) =
      periodOneMassSymbol 0 k * u.val k - q k := by
    simp only [periodOneMassSymbol, Nat.cast_zero, zero_add, ofReal_one]
    linear_combination -(h k)
  rw [hm, mul_sub, ← mul_assoc, inv_mul_cancel₀ (periodOneMassSymbol_ne_zero 0 k), one_mul]

end NLS
