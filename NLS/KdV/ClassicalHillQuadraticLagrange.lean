import NLS.KdV.ClassicalHillQuadraticKernels
import NLS.ComplexAnalysis.QuadraticKernelLagrange

/-! The boundary Green identity for the ACTUAL Hill quadratic kernels,
at every continuous complex potential and every pair of energies. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillQuadraticBoundary (q : Curve ℂ) (μ ν α β γ δ ε ζ : ℂ) (x : ℝ) : ℂ :=
  2*classicalHillQuadraticKernelKinetic q μ α β γ x*classicalHillQuadraticKernel q ν δ ε ζ x-
    classicalHillQuadraticKernelPrime q μ α β γ x*classicalHillQuadraticKernelPrime q ν δ ε ζ x+
      2*classicalHillQuadraticKernel q μ α β γ x*classicalHillQuadraticKernelKinetic q ν δ ε ζ x-
        2*(μ+ν)*classicalHillQuadraticKernel q μ α β γ x*classicalHillQuadraticKernel q ν δ ε ζ x

theorem classicalHillQuadratic_lagrange_integral (q : Curve ℂ) (μ ν α β γ δ ε ζ : ℂ) :
    4*(μ-ν)*(∫ x in (0:ℝ)..1,
      classicalHillQuadraticKernel q μ α β γ x*classicalHillQuadraticKernelPrime q ν δ ε ζ x)=
      classicalHillQuadraticBoundary q μ ν α β γ δ ε ζ 1-
        classicalHillQuadraticBoundary q μ ν α β γ δ ε ζ 0+
          4*μ*(classicalHillQuadraticKernel q μ α β γ 1*classicalHillQuadraticKernel q ν δ ε ζ 1-
            classicalHillQuadraticKernel q μ α β γ 0*classicalHillQuadraticKernel q ν δ ε ζ 0) := by
  have h0 (E a b c : ℂ) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (classicalHillQuadraticKernel q E a b c)
        (classicalHillQuadraticKernelPrime q E a b c t) t :=
    hasDerivAt_classicalHillQuadraticKernel q E a b c ⟨t,ht.1.le,ht.2.le⟩
  have h1 (E a b c : ℂ) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (classicalHillQuadraticKernelPrime q E a b c)
        (2*(extend q t-E)*classicalHillQuadraticKernel q E a b c t+
          2*classicalHillQuadraticKernelKinetic q E a b c t) t := by
    simpa only [← extend_coe q ⟨t,ht.1.le,ht.2.le⟩] using
      hasDerivAt_classicalHillQuadraticKernelPrime q E a b c ⟨t,ht.1.le,ht.2.le⟩
  have h2 (E a b c : ℂ) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (classicalHillQuadraticKernelKinetic q E a b c)
        ((extend q t-E)*classicalHillQuadraticKernelPrime q E a b c t) t := by
    simpa only [← extend_coe q ⟨t,ht.1.le,ht.2.le⟩] using
      hasDerivAt_classicalHillQuadraticKernelKinetic q E a b c ⟨t,ht.1.le,ht.2.le⟩
  exact quadraticKernel_boundary_lagrange_integral (extend q)
    (classicalHillQuadraticKernel q μ α β γ) (classicalHillQuadraticKernelPrime q μ α β γ)
    (classicalHillQuadraticKernelKinetic q μ α β γ)
    (classicalHillQuadraticKernel q ν δ ε ζ) (classicalHillQuadraticKernelPrime q ν δ ε ζ)
    (classicalHillQuadraticKernelKinetic q ν δ ε ζ) μ ν (continuous_extend q)
    (continuous_classicalHillQuadraticKernel q μ α β γ) (continuous_classicalHillQuadraticKernelPrime q μ α β γ)
    (continuous_classicalHillQuadraticKernelKinetic q μ α β γ)
    (continuous_classicalHillQuadraticKernel q ν δ ε ζ) (continuous_classicalHillQuadraticKernelPrime q ν δ ε ζ)
    (continuous_classicalHillQuadraticKernelKinetic q ν δ ε ζ)
    (h0 μ α β γ) (h1 μ α β γ) (h2 μ α β γ)
    (h0 ν δ ε ζ) (h1 ν δ ε ζ) (h2 ν δ ε ζ)

end NLS.KdV
