import NLS.SequenceSpaces.AnalyticMiuraExponentRecovery
import NLS.SequenceSpaces.PeriodOneMassSobolevInverse
import NLS.SequenceSpaces.PeriodOneMiuraShift

/-! An explicit analytic H1 representative recovered from the original
L2 weak Miura equation. Analyticity is proved for the formula on all L2
data; the weak equation then identifies its entire coefficient sequence
with the original solution. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

private abbrev miuraP43 : ℝ≥0∞ := ENNReal.ofReal (4/3 : ℝ)
private instance : Fact (1 ≤ miuraP43) := ⟨by norm_num [miuraP43]⟩
private theorem miuraYoung43 : YoungRelation miuraP43 miuraP43 2 := by
  unfold YoungRelation
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num [miuraP43])).mp
  rw [ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_add (by norm_num [miuraP43]) (by norm_num [miuraP43])]
  norm_num [miuraP43]

def periodOneMiuraH1Recovery (q v : Coeff 2) : ZakharovShabat.ScalarDomain 2 :=
  periodOneMassL2ToH1 0 (v + q - Coeff.youngConvolutionCLM miuraYoung43
    (periodOneMiuraExponentRecovery q v) (periodOneMiuraExponentRecovery q v))

theorem analyticAt_periodOneMiuraH1Recovery (z : Coeff 2 × Coeff 2) :
    AnalyticAt ℂ (fun y : Coeff 2 × Coeff 2 => periodOneMiuraH1Recovery y.1 y.2) z := by
  have hconv : AnalyticAt ℂ (fun y : Coeff 2 × Coeff 2 => Coeff.youngConvolutionCLM miuraYoung43
      (periodOneMiuraExponentRecovery y.1 y.2) (periodOneMiuraExponentRecovery y.1 y.2)) z :=
    ((Coeff.youngConvolutionCLM miuraYoung43).analyticAt_bilinear _).comp₂
      (analyticAt_periodOneMiuraExponentRecovery z) (analyticAt_periodOneMiuraExponentRecovery z)
  exact ((periodOneMassL2ToH1 0).analyticAt _).comp ((analyticAt_snd.add analyticAt_fst).sub hconv)

theorem periodOneMiuraH1Recovery_apply_of_equation (q v : Coeff 2)
    (h : ∀ k : ℤ, 2 * I * (Real.pi : ℂ) * k * v k + ∑' j : ℤ, v (k-j) * v j = q k)
    (k : ℤ) : (periodOneMiuraH1Recovery q v).val k = v k := by
  rw [periodOneMiuraH1Recovery, periodOneMassL2ToH1_apply]
  simp only [lp.coeFn_sub, lp.coeFn_add, Pi.sub_apply, Pi.add_apply,
    Coeff.youngConvolutionCLM_apply, Coeff.youngConvolution_apply,
    periodOneMiuraExponentRecovery_eq_of_equation q v h]
  have hm : v k + q k - (∑' j : ℤ, v (k-j) * v j) = periodOneMassSymbol 0 k * v k := by
    simp only [periodOneMassSymbol, Nat.cast_zero, zero_add, ofReal_one]
    linear_combination -(h k)
  rw [hm, ← mul_assoc, inv_mul_cancel₀ (periodOneMassSymbol_ne_zero 0 k), one_mul]

theorem scalarInclusion_periodOneMiuraH1Recovery_of_equation (q v : Coeff 2)
    (h : ∀ k : ℤ, 2 * I * (Real.pi : ℂ) * k * v k + ∑' j : ℤ, v (k-j) * v j = q k) :
    ZakharovShabat.scalarInclusion (periodOneMiuraH1Recovery q v) = v := by
  ext k
  rw [ZakharovShabat.scalarInclusion_apply, periodOneMiuraH1Recovery_apply_of_equation q v h]

theorem periodOneMiura_equation_of_image (q v : Coeff 2)
    (himage : periodOneMiura v = periodOneL2Inclusion q) (k : ℤ) :
    2 * I * (Real.pi : ℂ) * k * v k + ∑' j : ℤ, v (k-j) * v j = q k := by
  have h := congrArg (fun a : PeriodOneHminusOne => a.val k) himage
  rw [periodOneMiura_apply, periodOneL2Inclusion_apply] at h
  exact h

theorem analyticAt_periodOneMiuraH1Recovery_comp (f g : Coeff 2 → Coeff 2) (q : Coeff 2)
    (hf : AnalyticAt ℂ f q) (hg : AnalyticAt ℂ g q) :
    AnalyticAt ℂ (fun a => periodOneMiuraH1Recovery (f a) (g a)) q :=
  (analyticAt_periodOneMiuraH1Recovery (f q, g q)).comp
    (f := fun a => (f a, g a)) (hf.prod hg)

theorem analyticAt_comp_periodOneL2Inclusion (f : PeriodOneHminusOne → Coeff 2) (q : Coeff 2)
    (hf : AnalyticAt ℂ f (periodOneL2Inclusion q)) :
    AnalyticAt ℂ (fun a : Coeff 2 => f (periodOneL2Inclusion a)) q :=
  hf.comp (f := fun a : Coeff 2 => periodOneL2Inclusion a) (periodOneL2Inclusion.analyticAt q)

end NLS
