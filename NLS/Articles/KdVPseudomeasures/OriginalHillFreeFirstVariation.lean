import NLS.KdV.ClassicalHillFreeEnergyDerivative
import NLS.KdV.ClassicalHillFreeTraceVariation

/-! Exact first-variation INPUTS for the article's Hill coordinates.
These are derivatives of the ACTUAL independently normalized physical
scalar IVP. Identification of the native Cartesian differential remains
an additional obligation. -/
noncomputable section
open Complex NLS.KdV NLS.LinearVolterra
open scoped Real
namespace NLS.Articles.KdVPseudomeasures

theorem original_Hill_free_physical_Dirichlet_first_variation (h : Curve ℂ) (n : ℕ+) :
    (fderiv ℂ (fun q => classicalHillDirichlet q ((π*n)^2)) 0) h =
      -(-1:ℂ)^(n:ℕ)/(π*n)^2 *
        ∫ s in (0:ℝ)..1, extend h s * sin (π*n*(s:ℂ))^2 ∧
    HasDerivAt (classicalHillDirichlet 0) ((-1:ℂ)^(n:ℕ)/(2*(π*n)^2)) ((π*n)^2) ∧
    deriv (classicalHillDirichlet 0) ((π*n)^2) ≠ 0 :=
  ⟨fderiv_classicalHillDirichlet_free_fourier h n,
    hasDerivAt_classicalHillDirichlet_free_eigenvalue n,
    deriv_classicalHillDirichlet_free_eigenvalue_ne_zero n⟩

theorem original_Hill_free_physical_norming_first_variation (h : Curve ℂ) (n : ℕ+) :
    (fderiv ℂ (fun q => classicalHillDirichletTerminal q ((π*n)^2)) 0) h =
      (-1:ℂ)^(n:ℕ)/(2*(π*n)) *
        ∫ s in (0:ℝ)..1, extend h s * sin (2*(π*n)*(s:ℂ)) ∧
    HasDerivAt (classicalHillDirichletTerminal 0) 0 ((π*n)^2) :=
  ⟨fderiv_classicalHillDirichletTerminal_free_fourier h n,
    hasDerivAt_classicalHillDirichletTerminal_free_eigenvalue n⟩

theorem original_Hill_free_physical_trace_first_variation (h : Curve ℂ) (z : ℂ) (hz : z ≠ 0) :
    (fderiv ℂ (fun q => classicalHillDiscriminant q (z^2)) 0) h =
      sin z/z * ∫ s in (0:ℝ)..1, extend h s :=
  fderiv_classicalHillDiscriminant_free h z hz

end NLS.Articles.KdVPseudomeasures
