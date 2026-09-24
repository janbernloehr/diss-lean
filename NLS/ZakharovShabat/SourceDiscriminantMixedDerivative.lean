import NLS.ComplexAnalysis.MixedSpectralSourceDerivative
import NLS.ZakharovShabat.SourceCriticalRootRatioJointAnalytic

/-!
# Mixed derivatives of the source discriminant

The spectral derivative of the canonical discriminant may be
differentiated in the potential by first taking its source Fréchet
derivative and then differentiating in the spectral variable.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Interchange the source Fréchet derivative and spectral derivative
of the canonical discriminant. -/
theorem fderiv_source_discriminant_deriv_eq_deriv_spectral_fderiv_source
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (z : ℂ) (φ h : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z) φ) h =
      deriv (fun w : ℂ =>
        (fderiv ℂ (fun ψ : CoeffPair p =>
          canonicalDiscriminant hp (periodOnePotential ψ) w) φ) h) z := by
  let F : ℂ × CoeffPair p → ℂ := fun t =>
    canonicalDiscriminant hp (periodOnePotential t.2) t.1
  have hF : AnalyticOnNhd ℂ F univ :=
    analyticOnNhd_canonicalDiscriminant_periodOne hp hp1
  exact NLS.ComplexAnalysis.fderiv_source_deriv_spectral_eq_deriv_spectral_fderiv_source
    F univ isOpen_univ hF z φ (mem_univ _) h

end NLS.ZakharovShabat
