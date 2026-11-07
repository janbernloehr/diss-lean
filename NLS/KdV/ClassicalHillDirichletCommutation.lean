import NLS.KdV.ClassicalHillDirichletGradient
import NLS.KdV.ClassicalHillQuadraticLagrange

/-! Actual Dirichlet gradient kernels commute at all complex energies.
The potential is only continuous. Equal energies are handled directly. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem classicalHillDirichletGradients_lagrange (q : Curve ℂ) (μ ν : ℂ) :
    (μ-ν)*(∫ x in (0:ℝ)..1, classicalHillDirichletGradient q μ x*
      classicalHillDirichletGradientPrime q ν x)=0 := by
  have hi := classicalHillQuadratic_lagrange_integral q μ ν
    0 (classicalHillS q μ 1) (-classicalHillC q μ 1)
    0 (classicalHillS q ν 1) (-classicalHillC q ν 1)
  change 4*(μ-ν)*(∫ x in (0:ℝ)..1, classicalHillDirichletGradient q μ x*classicalHillDirichletGradientPrime q ν x)=
    (2*classicalHillDirichletGradientKinetic q μ 1*classicalHillDirichletGradient q ν 1-
      classicalHillDirichletGradientPrime q μ 1*classicalHillDirichletGradientPrime q ν 1+
      2*classicalHillDirichletGradient q μ 1*classicalHillDirichletGradientKinetic q ν 1-
      2*(μ+ν)*classicalHillDirichletGradient q μ 1*classicalHillDirichletGradient q ν 1)-
    (2*classicalHillDirichletGradientKinetic q μ 0*classicalHillDirichletGradient q ν 0-
      classicalHillDirichletGradientPrime q μ 0*classicalHillDirichletGradientPrime q ν 0+
      2*classicalHillDirichletGradient q μ 0*classicalHillDirichletGradientKinetic q ν 0-
      2*(μ+ν)*classicalHillDirichletGradient q μ 0*classicalHillDirichletGradient q ν 0)+
    4*μ*(classicalHillDirichletGradient q μ 1*classicalHillDirichletGradient q ν 1-
      classicalHillDirichletGradient q μ 0*classicalHillDirichletGradient q ν 0) at hi
  rw [(classicalHillDirichletGradient_initial q μ).1,(classicalHillDirichletGradient_initial q ν).1,
    (classicalHillDirichletGradient_terminal q μ).1,(classicalHillDirichletGradient_terminal q ν).1,
    (classicalHillDirichletGradient_initial q μ).2.1,(classicalHillDirichletGradient_initial q ν).2.1,
    (classicalHillDirichletGradient_terminal q μ).2.1,(classicalHillDirichletGradient_terminal q ν).2.1] at hi
  linear_combination (1/4:ℂ)*hi

theorem integral_classicalHillDirichletGradients_eq_zero (q : Curve ℂ) (μ ν : ℂ) :
    (∫ x in (0:ℝ)..1, classicalHillDirichletGradient q μ x*classicalHillDirichletGradientPrime q ν x)=0 := by
  by_cases hμν : μ=ν
  · subst ν
    exact integral_self_mul_derivative_eq_zero _ _ (continuous_classicalHillDirichletGradient q μ)
      (continuous_classicalHillDirichletGradientPrime q μ)
      (fun t ht => hasDerivAt_classicalHillDirichletGradient q μ ⟨t,ht.1.le,ht.2.le⟩)
      (classicalHillDirichletGradient_boundary q μ)
  · exact (mul_eq_zero.mp (classicalHillDirichletGradients_lagrange q μ ν)).resolve_left (sub_ne_zero.mpr hμν)

end NLS.KdV
