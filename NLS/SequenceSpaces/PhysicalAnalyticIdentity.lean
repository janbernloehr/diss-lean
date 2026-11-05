import NLS.SequenceSpaces.FourierRealZeroCoordinates
import NLS.FunctionalAnalysis.AnalyticDenseDerivativeIdentity

/-! Analytic derivative identity on the physical Fourier real Banach
models, retaining their actual inherited norm topology. -/
noncomputable section
namespace NLS.WeightedCoeff

theorem fourierRealZero_fderiv_eq_of_analytic_dense_fderiv_eq (w : Weight)
    (f g : fourierRealZeroSubmodule w 2 → ℂ) (S : Set (fourierRealZeroSubmodule w 2))
    (hf : ∀ x, AnalyticAt ℝ f x) (hg : ∀ x, AnalyticAt ℝ g x)
    (hS : Dense S) (hD : ∀ x ∈ S, fderiv ℝ f x=fderiv ℝ g x) :
    ∀ x, fderiv ℝ f x=fderiv ℝ g x := by
  exact @NLS.FunctionalAnalysis.fderiv_eq_of_analytic_dense_fderiv_eq (fourierRealZeroSubmodule w 2) ℂ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    f g S hf hg hS hD

theorem fourierRealZero_eq_of_analytic_dense_fderiv_eq (w : Weight)
    (f g : fourierRealZeroSubmodule w 2 → ℂ) (S : Set (fourierRealZeroSubmodule w 2))
    (hf : ∀ x, AnalyticAt ℝ f x) (hg : ∀ x, AnalyticAt ℝ g x)
    (hS : Dense S) (hD : ∀ x ∈ S, fderiv ℝ f x=fderiv ℝ g x)
    (x₀ : fourierRealZeroSubmodule w 2) (h₀ : f x₀=g x₀) : f=g := by
  exact @NLS.FunctionalAnalysis.eq_of_analytic_dense_fderiv_eq (fourierRealZeroSubmodule w 2) ℂ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    f g S hf hg hS hD x₀ h₀

end NLS.WeightedCoeff
