import NLS.KdV.ClassicalHillQuadraticLagrange
import NLS.KdV.ClassicalHillDirichletGradient
import NLS.KdV.ClassicalHillTraceGradientBoundary

/-! The actual mixed discriminant/Dirichlet gradient bracket, with
its endpoint diagonal differences and exact factor two. No energy
difference is divided out, and the potential need only be continuous. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

theorem classicalHill_mixed_gradient_bracket (q : Curve ℂ) (μ ν : ℂ) :
    2*(μ-ν)*(∫ x in (0:ℝ)..1, classicalHillTraceGradient q μ x*classicalHillDirichletGradientPrime q ν x)=
      classicalHillS q ν 1*(classicalHillSPrime q μ 1-classicalHillC q μ 1)-
        classicalHillS q μ 1*(classicalHillSPrime q ν 1-classicalHillC q ν 1) := by
  have hG : classicalHillQuadraticKernel q μ (classicalHillS q μ 1)
      (classicalHillSPrime q μ 1-classicalHillC q μ 1) (-classicalHillCPrime q μ 1)=
      classicalHillTraceGradient q μ := by
    funext x
    dsimp only [classicalHillQuadraticKernel,classicalHillTraceGradient]
    ring
  have hG1 : classicalHillQuadraticKernelPrime q μ (classicalHillS q μ 1)
      (classicalHillSPrime q μ 1-classicalHillC q μ 1) (-classicalHillCPrime q μ 1)=
      classicalHillTraceGradientPrime q μ := by
    funext x
    dsimp only [classicalHillQuadraticKernelPrime,classicalHillTraceGradientPrime]
    ring
  have hK : classicalHillQuadraticKernelKinetic q μ (classicalHillS q μ 1)
      (classicalHillSPrime q μ 1-classicalHillC q μ 1) (-classicalHillCPrime q μ 1)=
      classicalHillTraceGradientKinetic q μ := by
    funext x
    dsimp only [classicalHillQuadraticKernelKinetic,classicalHillTraceGradientKinetic]
    ring
  have hi := classicalHillQuadratic_lagrange_integral q μ ν (classicalHillS q μ 1)
    (classicalHillSPrime q μ 1-classicalHillC q μ 1) (-classicalHillCPrime q μ 1)
    0 (classicalHillS q ν 1) (-classicalHillC q ν 1)
  dsimp only [classicalHillQuadraticBoundary] at hi
  rw [hG,hG1,hK] at hi
  change 4*(μ-ν)*(∫ x in (0:ℝ)..1, classicalHillTraceGradient q μ x*classicalHillDirichletGradientPrime q ν x)=
    (2*classicalHillTraceGradientKinetic q μ 1*classicalHillDirichletGradient q ν 1-
      classicalHillTraceGradientPrime q μ 1*classicalHillDirichletGradientPrime q ν 1+
      2*classicalHillTraceGradient q μ 1*classicalHillDirichletGradientKinetic q ν 1-
      2*(μ+ν)*classicalHillTraceGradient q μ 1*classicalHillDirichletGradient q ν 1)-
    (2*classicalHillTraceGradientKinetic q μ 0*classicalHillDirichletGradient q ν 0-
      classicalHillTraceGradientPrime q μ 0*classicalHillDirichletGradientPrime q ν 0+
      2*classicalHillTraceGradient q μ 0*classicalHillDirichletGradientKinetic q ν 0-
      2*(μ+ν)*classicalHillTraceGradient q μ 0*classicalHillDirichletGradient q ν 0)+
    4*μ*(classicalHillTraceGradient q μ 1*classicalHillDirichletGradient q ν 1-
      classicalHillTraceGradient q μ 0*classicalHillDirichletGradient q ν 0) at hi
  rw [(classicalHillDirichletGradient_initial q ν).1,(classicalHillDirichletGradient_terminal q ν).1,
    (classicalHillDirichletGradient_initial q ν).2.1,(classicalHillDirichletGradient_terminal q ν).2.1,
    (classicalHillDirichletGradient_initial q ν).2.2,(classicalHillDirichletGradient_terminal q ν).2.2,
    classicalHillTraceGradient_initial,classicalHillTraceGradient_terminal,
    classicalHillTraceGradientPrime_initial,classicalHillTraceGradientPrime_terminal] at hi
  linear_combination (1/2:ℂ)*hi

end NLS.KdV
