import NLS.KdV.ClassicalHillNormingGradient
import NLS.KdV.ClassicalHillQuadraticLagrange

/-! Actual moving norming kernels at distinct Dirichlet roots have
zero Gardner integral, with no regularity beyond a continuous potential. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

theorem integral_classicalHillNormingGradients_eq_zero (q : Curve ℂ) (μ ν η θ : ℂ)
    (hμ : classicalHillS q μ 1=0) (hν : classicalHillS q ν 1=0) (hne : μ ≠ ν) :
    (∫ x in (0:ℝ)..1, classicalHillNormingGradient q μ η x*classicalHillNormingGradientPrime q ν θ x)=0 := by
  have hi := classicalHillQuadratic_lagrange_integral q μ ν
    0 (classicalHillSPrime q μ 1-η*classicalHillS q μ 1) (η*classicalHillC q μ 1-classicalHillCPrime q μ 1)
    0 (classicalHillSPrime q ν 1-θ*classicalHillS q ν 1) (θ*classicalHillC q ν 1-classicalHillCPrime q ν 1)
  let K : ℝ → ℂ := classicalHillQuadraticKernelKinetic q μ
    0 (classicalHillSPrime q μ 1-η*classicalHillS q μ 1) (η*classicalHillC q μ 1-classicalHillCPrime q μ 1)
  let L : ℝ → ℂ := classicalHillQuadraticKernelKinetic q ν
    0 (classicalHillSPrime q ν 1-θ*classicalHillS q ν 1) (θ*classicalHillC q ν 1-classicalHillCPrime q ν 1)
  change 4*(μ-ν)*(∫ x in (0:ℝ)..1, classicalHillNormingGradient q μ η x*classicalHillNormingGradientPrime q ν θ x)=
    (2*K 1*classicalHillNormingGradient q ν θ 1-
      classicalHillNormingGradientPrime q μ η 1*classicalHillNormingGradientPrime q ν θ 1+
      2*classicalHillNormingGradient q μ η 1*L 1-
      2*(μ+ν)*classicalHillNormingGradient q μ η 1*classicalHillNormingGradient q ν θ 1)-
    (2*K 0*classicalHillNormingGradient q ν θ 0-
      classicalHillNormingGradientPrime q μ η 0*classicalHillNormingGradientPrime q ν θ 0+
      2*classicalHillNormingGradient q μ η 0*L 0-
      2*(μ+ν)*classicalHillNormingGradient q μ η 0*classicalHillNormingGradient q ν θ 0)+
    4*μ*(classicalHillNormingGradient q μ η 1*classicalHillNormingGradient q ν θ 1-
      classicalHillNormingGradient q μ η 0*classicalHillNormingGradient q ν θ 0) at hi
  obtain ⟨hf0,hf1,hfp0,hfp1⟩ := classicalHillNormingGradient_boundary_at_root q μ η hμ
  obtain ⟨hg0,hg1,hgp0,hgp1⟩ := classicalHillNormingGradient_boundary_at_root q ν θ hν
  rw [hf0,hf1,hfp0,hfp1,hg0,hg1,hgp0,hgp1] at hi
  have hz : (μ-ν)*(∫ x in (0:ℝ)..1, classicalHillNormingGradient q μ η x*classicalHillNormingGradientPrime q ν θ x)=0 := by
    linear_combination (1/4:ℂ)*hi
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

end NLS.KdV
