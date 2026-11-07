import NLS.KdV.ClassicalHillQuadraticKernels
import NLS.KdV.ClassicalHillVariationKernels

/-! The ACTUAL full potential derivative of the normalized Dirichlet
characteristic, with its physical quadratic kernel and endpoint jets. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

def classicalHillDirichletGradient (q : Curve ℂ) (μ : ℂ) : ℝ → ℂ :=
  classicalHillQuadraticKernel q μ 0 (classicalHillS q μ 1) (-classicalHillC q μ 1)

def classicalHillDirichletGradientPrime (q : Curve ℂ) (μ : ℂ) : ℝ → ℂ :=
  classicalHillQuadraticKernelPrime q μ 0 (classicalHillS q μ 1) (-classicalHillC q μ 1)

def classicalHillDirichletGradientKinetic (q : Curve ℂ) (μ : ℂ) : ℝ → ℂ :=
  classicalHillQuadraticKernelKinetic q μ 0 (classicalHillS q μ 1) (-classicalHillC q μ 1)

theorem continuous_classicalHillDirichletGradient (q : Curve ℂ) (μ : ℂ) :
    Continuous (classicalHillDirichletGradient q μ) := continuous_classicalHillQuadraticKernel q μ _ _ _

theorem continuous_classicalHillDirichletGradientPrime (q : Curve ℂ) (μ : ℂ) :
    Continuous (classicalHillDirichletGradientPrime q μ) := continuous_classicalHillQuadraticKernelPrime q μ _ _ _

theorem continuous_classicalHillDirichletGradientKinetic (q : Curve ℂ) (μ : ℂ) :
    Continuous (classicalHillDirichletGradientKinetic q μ) := continuous_classicalHillQuadraticKernelKinetic q μ _ _ _

theorem hasDerivAt_classicalHillDirichletGradient (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillDirichletGradient q μ) (classicalHillDirichletGradientPrime q μ t) t :=
  hasDerivAt_classicalHillQuadraticKernel q μ _ _ _ t

theorem hasDerivAt_classicalHillDirichletGradientPrime (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillDirichletGradientPrime q μ)
      (2*(q t-μ)*classicalHillDirichletGradient q μ t+2*classicalHillDirichletGradientKinetic q μ t) t :=
  hasDerivAt_classicalHillQuadraticKernelPrime q μ _ _ _ t

theorem hasDerivAt_classicalHillDirichletGradientKinetic (q : Curve ℂ) (μ : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillDirichletGradientKinetic q μ) ((q t-μ)*classicalHillDirichletGradientPrime q μ t) t :=
  hasDerivAt_classicalHillQuadraticKernelKinetic q μ _ _ _ t

theorem classicalHillDirichletGradient_initial (q : Curve ℂ) (μ : ℂ) :
    classicalHillDirichletGradient q μ 0=0 ∧
      classicalHillDirichletGradientPrime q μ 0=classicalHillS q μ 1 ∧
      classicalHillDirichletGradientKinetic q μ 0= -classicalHillC q μ 1 := by
  obtain ⟨hC,hCp,hS,hSp⟩ := classicalHillFundamentalColumns_initial q μ
  simp [classicalHillDirichletGradient,classicalHillQuadraticKernel,
    classicalHillDirichletGradientPrime,classicalHillQuadraticKernelPrime,
    classicalHillDirichletGradientKinetic,classicalHillQuadraticKernelKinetic,hC,hCp,hS,hSp]

theorem classicalHillDirichletGradient_terminal (q : Curve ℂ) (μ : ℂ) :
    classicalHillDirichletGradient q μ 1=0 ∧
      classicalHillDirichletGradientPrime q μ 1= -classicalHillS q μ 1 ∧
      classicalHillDirichletGradientKinetic q μ 1= -classicalHillSPrime q μ 1 := by
  have hdet := classicalHillFundamentalColumns_det q μ ⟨1,by constructor <;> norm_num⟩
  dsimp only [classicalHillDirichletGradient,classicalHillQuadraticKernel,
    classicalHillDirichletGradientPrime,classicalHillQuadraticKernelPrime,
    classicalHillDirichletGradientKinetic,classicalHillQuadraticKernelKinetic]
  refine ⟨by ring,?_,?_⟩
  · linear_combination -classicalHillS q μ 1*hdet
  · linear_combination -classicalHillSPrime q μ 1*hdet

theorem classicalHillDirichletGradient_boundary (q : Curve ℂ) (μ : ℂ) :
    classicalHillDirichletGradient q μ 1=classicalHillDirichletGradient q μ 0 := by
  rw [(classicalHillDirichletGradient_terminal q μ).1,(classicalHillDirichletGradient_initial q μ).1]

theorem fderiv_classicalHillDirichlet_eq_integral_gradient (q h : Curve ℂ) (μ : ℂ) :
    (fderiv ℂ (fun r => classicalHillDirichlet r μ) q) h=
      ∫ x in (0:ℝ)..1, extend h x*classicalHillDirichletGradient q μ x := by
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hS := (classicalHillPotentialVariation_kernels q h μ (0,1) t).1
  change (classicalHillPotentialVariation q h μ (0,1) 1).1=_ at hS
  rw [fderiv_classicalHillDirichlet_potential,hS]
  change classicalHillS q μ 1*(∫ x in (0:ℝ)..1, extend h x*classicalHillC q μ x*classicalHillS q μ x)-
    classicalHillC q μ 1*(∫ x in (0:ℝ)..1, extend h x*classicalHillS q μ x*classicalHillS q μ x)=_
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro x _
    dsimp only [classicalHillDirichletGradient,classicalHillQuadraticKernel]
    ring
  all_goals
    apply Continuous.intervalIntegrable
    have hh := continuous_extend h
    have hC := continuous_classicalHillC q μ
    have hS := continuous_classicalHillS q μ
    fun_prop

end NLS.KdV
