import NLS.KdV.ClassicalHillDirichletGradient

/-! The actual terminal potential derivative and the moving-energy
norming kernel. Periodic endpoint identities are asserted only at an
actual Dirichlet root; the fixed-energy terminal is not assumed to
extend as a functional on H-minus-one. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

def classicalHillTerminalGradient (q : Curve ℂ) (μ : ℂ) : ℝ → ℂ :=
  classicalHillQuadraticKernel q μ 0 (classicalHillSPrime q μ 1) (-classicalHillCPrime q μ 1)

theorem continuous_classicalHillTerminalGradient (q : Curve ℂ) (μ : ℂ) :
    Continuous (classicalHillTerminalGradient q μ) := continuous_classicalHillQuadraticKernel q μ _ _ _

theorem fderiv_classicalHillTerminal_eq_integral_gradient (q h : Curve ℂ) (μ : ℂ) :
    (fderiv ℂ (fun r => classicalHillDirichletTerminal r μ) q) h=
      ∫ x in (0:ℝ)..1, extend h x*classicalHillTerminalGradient q μ x := by
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hS := (classicalHillPotentialVariation_kernels q h μ (0,1) t).2
  change (classicalHillPotentialVariation q h μ (0,1) 1).2=_ at hS
  rw [fderiv_classicalHillDirichletTerminal_potential,hS]
  change classicalHillSPrime q μ 1*(∫ x in (0:ℝ)..1, extend h x*classicalHillC q μ x*classicalHillS q μ x)-
    classicalHillCPrime q μ 1*(∫ x in (0:ℝ)..1, extend h x*classicalHillS q μ x*classicalHillS q μ x)=_
  rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro x _
    dsimp only [classicalHillTerminalGradient,classicalHillQuadraticKernel]
    ring
  all_goals
    apply Continuous.intervalIntegrable
    have hh := continuous_extend h
    have hC := continuous_classicalHillC q μ
    have hS := continuous_classicalHillS q μ
    fun_prop

def classicalHillNormingGradient (q : Curve ℂ) (μ η : ℂ) : ℝ → ℂ :=
  classicalHillQuadraticKernel q μ 0 (classicalHillSPrime q μ 1-η*classicalHillS q μ 1)
    (η*classicalHillC q μ 1-classicalHillCPrime q μ 1)

def classicalHillNormingGradientPrime (q : Curve ℂ) (μ η : ℂ) : ℝ → ℂ :=
  classicalHillQuadraticKernelPrime q μ 0 (classicalHillSPrime q μ 1-η*classicalHillS q μ 1)
    (η*classicalHillC q μ 1-classicalHillCPrime q μ 1)

theorem continuous_classicalHillNormingGradient (q : Curve ℂ) (μ η : ℂ) :
    Continuous (classicalHillNormingGradient q μ η) := continuous_classicalHillQuadraticKernel q μ _ _ _

theorem continuous_classicalHillNormingGradientPrime (q : Curve ℂ) (μ η : ℂ) :
    Continuous (classicalHillNormingGradientPrime q μ η) := continuous_classicalHillQuadraticKernelPrime q μ _ _ _

theorem hasDerivAt_classicalHillNormingGradient (q : Curve ℂ) (μ η : ℂ) (t : Icc (0:ℝ) 1) :
    HasDerivAt (classicalHillNormingGradient q μ η) (classicalHillNormingGradientPrime q μ η t) t :=
  hasDerivAt_classicalHillQuadraticKernel q μ _ _ _ t

theorem classicalHillNormingGradient_eq_terminal_sub (q : Curve ℂ) (μ η : ℂ) (x : ℝ) :
    classicalHillNormingGradient q μ η x=
      classicalHillTerminalGradient q μ x-η*classicalHillDirichletGradient q μ x := by
  dsimp only [classicalHillNormingGradient,classicalHillTerminalGradient,
    classicalHillDirichletGradient,classicalHillQuadraticKernel]
  ring

theorem classicalHillTerminal_sub_characteristic_derivative (q h : Curve ℂ) (μ η : ℂ) :
    (fderiv ℂ (fun r => classicalHillDirichletTerminal r μ) q) h-
      η*(fderiv ℂ (fun r => classicalHillDirichlet r μ) q) h=
      ∫ x in (0:ℝ)..1, extend h x*classicalHillNormingGradient q μ η x := by
  rw [fderiv_classicalHillTerminal_eq_integral_gradient,fderiv_classicalHillDirichlet_eq_integral_gradient,
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    rw [classicalHillNormingGradient_eq_terminal_sub]
    ring
  · exact ((continuous_extend h).mul (continuous_classicalHillTerminalGradient q μ)).intervalIntegrable 0 1
  · exact (continuous_const.mul ((continuous_extend h).mul
      (continuous_classicalHillDirichletGradient q μ))).intervalIntegrable 0 1

theorem classicalHillNormingGradient_boundary_at_root (q : Curve ℂ) (μ η : ℂ)
    (hroot : classicalHillS q μ 1=0) :
    classicalHillNormingGradient q μ η 0=0 ∧ classicalHillNormingGradient q μ η 1=0 ∧
      classicalHillNormingGradientPrime q μ η 0=classicalHillSPrime q μ 1 ∧
      classicalHillNormingGradientPrime q μ η 1=classicalHillSPrime q μ 1 := by
  obtain ⟨hC,hCp,hS,hSp⟩ := classicalHillFundamentalColumns_initial q μ
  have hdet := classicalHillFundamentalColumns_det q μ ⟨1,by constructor <;> norm_num⟩
  rw [hroot,mul_zero,sub_zero] at hdet
  dsimp only [classicalHillNormingGradient,classicalHillNormingGradientPrime,
    classicalHillQuadraticKernel,classicalHillQuadraticKernelPrime]
  rw [hroot,hC,hCp,hS,hSp]
  refine ⟨by ring,by ring,by ring,?_⟩
  linear_combination classicalHillSPrime q μ 1*hdet

end NLS.KdV
