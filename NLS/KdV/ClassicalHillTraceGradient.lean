import NLS.KdV.ClassicalHillFundamentalColumns
import NLS.KdV.ClassicalHillVariationKernels
import NLS.KdV.ClassicalHillFreeTraceVariation

/-! The ACTUAL discriminant potential gradient at every continuous
complex potential and every energy, expressed by its normalized columns. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

def classicalHillTraceGradient (q : Curve ℂ) (μ : ℂ) (x : ℝ) : ℂ :=
  classicalHillS q μ 1*(classicalHillC q μ x)^2+
    (classicalHillSPrime q μ 1-classicalHillC q μ 1)*(classicalHillC q μ x*classicalHillS q μ x)-
    classicalHillCPrime q μ 1*(classicalHillS q μ x)^2

theorem continuous_classicalHillTraceGradient (q : Curve ℂ) (μ : ℂ) :
    Continuous (classicalHillTraceGradient q μ) :=
  (continuous_const.mul ((continuous_classicalHillC q μ).pow 2)).add
    (continuous_const.mul ((continuous_classicalHillC q μ).mul (continuous_classicalHillS q μ))) |>.sub
      (continuous_const.mul ((continuous_classicalHillS q μ).pow 2))

theorem fderiv_classicalHillDiscriminant_eq_integral_gradient (q h : Curve ℂ) (μ : ℂ) :
    (fderiv ℂ (fun r => classicalHillDiscriminant r μ) q) h=
      ∫ s in (0:ℝ)..1, extend h s*classicalHillTraceGradient q μ s := by
  have hcc := continuous_classicalHillC q μ
  have hss := continuous_classicalHillS q μ
  have hhc := continuous_extend h
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hC := (classicalHillPotentialVariation_kernels q h μ (1,0) t).1
  have hS := (classicalHillPotentialVariation_kernels q h μ (0,1) t).2
  change (classicalHillPotentialVariation q h μ (1,0) 1).1=_ at hC
  change (classicalHillPotentialVariation q h μ (0,1) 1).2=_ at hS
  rw [fderiv_classicalHillDiscriminant_potential,hC,hS]
  change classicalHillS q μ 1*(∫ s in (0:ℝ)..1, extend h s*classicalHillC q μ s*classicalHillC q μ s)-
    classicalHillC q μ 1*(∫ s in (0:ℝ)..1, extend h s*classicalHillS q μ s*classicalHillC q μ s)+
    (classicalHillSPrime q μ 1*(∫ s in (0:ℝ)..1, extend h s*classicalHillC q μ s*classicalHillS q μ s)-
      classicalHillCPrime q μ 1*(∫ s in (0:ℝ)..1, extend h s*classicalHillS q μ s*classicalHillS q μ s))=_
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub,← intervalIntegral.integral_sub,← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro s _
    dsimp only [classicalHillTraceGradient]
    ring
  all_goals
    apply Continuous.intervalIntegrable
    fun_prop (disch := assumption)

end NLS.KdV
