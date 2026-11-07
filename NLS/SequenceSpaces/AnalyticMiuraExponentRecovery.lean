import NLS.SequenceSpaces.PeriodOneMiuraRegularity
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! An EXPLICIT analytic improvement from L2 Miura data to ell^(4/3).
The formula uses the fixed massive resolvent and bounded Young/Holder
maps. When the original weak Miura equation holds, the formula has
exactly the original solution coefficients. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

private abbrev miuraP43 : ℝ≥0∞ := ENNReal.ofReal (4/3 : ℝ)
private instance : Fact (1 ≤ miuraP43) := ⟨by norm_num [miuraP43]⟩

private def miuraMassKernel43 : Coeff miuraP43 :=
  ⟨fun k => (periodOneMassSymbol 0 k)⁻¹,
    memlp_periodOneMassInverseSymbol (by norm_num [miuraP43]) 0⟩

def periodOneMiuraExponentRecovery (q v : Coeff 2) : Coeff (ENNReal.ofReal (4/3 : ℝ)) :=
  Coeff.exponentInclusion (by norm_num [miuraP43] : (1 : ℝ≥0∞) ≤ miuraP43)
    (Coeff.holderProduct (q := 1) (periodOneMassKernel 0) (v + q)) -
      Coeff.holderProduct (q := miuraP43) miuraMassKernel43
        (Coeff.youngConvolutionCLM youngRelation_two_two_top v v)

theorem periodOneMiuraExponentRecovery_apply (q v : Coeff 2) (k : ℤ) :
    periodOneMiuraExponentRecovery q v k =
      (periodOneMassSymbol 0 k)⁻¹ * (v k + q k) -
        (periodOneMassSymbol 0 k)⁻¹ * (∑' j : ℤ, v (k-j) * v j) := by
  simp only [periodOneMiuraExponentRecovery, lp.coeFn_sub, Pi.sub_apply,
    Coeff.exponentInclusion_apply, Coeff.holderProduct_apply, periodOneMassKernel_apply,
    lp.coeFn_add, Pi.add_apply, Coeff.youngConvolutionCLM_apply, Coeff.youngConvolution_apply]
  rfl

theorem analyticAt_periodOneMiuraExponentRecovery (z : Coeff 2 × Coeff 2) :
    AnalyticAt ℂ (fun y : Coeff 2 × Coeff 2 => periodOneMiuraExponentRecovery y.1 y.2) z := by
  have hsum : AnalyticAt ℂ (fun y : Coeff 2 × Coeff 2 => y.2 + y.1) z :=
    analyticAt_snd.add analyticAt_fst
  have hfirst := ((Coeff.exponentInclusion
    (by norm_num [miuraP43] : (1 : ℝ≥0∞) ≤ miuraP43)).analyticAt _).comp
      (((Coeff.holderProduct (q := 1) (periodOneMassKernel 0)).analyticAt _).comp hsum)
  have hconv : AnalyticAt ℂ (fun y : Coeff 2 × Coeff 2 =>
      Coeff.youngConvolutionCLM youngRelation_two_two_top y.2 y.2) z :=
    ((Coeff.youngConvolutionCLM youngRelation_two_two_top).analyticAt_bilinear _).comp₂
      analyticAt_snd analyticAt_snd
  have hsecond := ((Coeff.holderProduct (q := miuraP43) miuraMassKernel43).analyticAt _).comp hconv
  exact hfirst.sub hsecond

theorem periodOneMiuraExponentRecovery_eq_of_equation (q v : Coeff 2)
    (h : ∀ k : ℤ, 2 * I * (Real.pi : ℂ) * k * v k + ∑' j : ℤ, v (k-j) * v j = q k)
    (k : ℤ) : periodOneMiuraExponentRecovery q v k = v k := by
  rw [periodOneMiuraExponentRecovery_apply]
  have hm : v k + q k - (∑' j : ℤ, v (k-j) * v j) = periodOneMassSymbol 0 k * v k := by
    simp only [periodOneMassSymbol, Nat.cast_zero, zero_add, ofReal_one]
    linear_combination -(h k)
  calc
    _ = (periodOneMassSymbol 0 k)⁻¹ * (v k + q k - (∑' j : ℤ, v (k-j) * v j)) := by ring
    _ = _ := by rw [hm, ← mul_assoc, inv_mul_cancel₀ (periodOneMassSymbol_ne_zero 0 k), one_mul]

end NLS
