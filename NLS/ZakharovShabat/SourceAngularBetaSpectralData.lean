import NLS.ZakharovShabat.SourceAngularPrimitiveSpectralData
import NLS.ZakharovShabat.SourceDirichletSignData
import NLS.ZakharovShabat.SourceAngularBetaSeries

/-! # Beta corrections depend on the actual signed Dirichlet data

The periodic spectrum, Dirichlet eigenvalues and their signs preserve
every defining normalized primitive value set. Therefore every beta
summand and the full beta correction agree for independent actual psi
families. The endpoint zero convention is transported explicitly.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equal actual spectra and selected Dirichlet points preserve the endpoint alternative. -/
theorem sourceAngularDirichletTerminalIsEndpoint_isospectral_iff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : realTypeSourceSubmodule p)
    (h : ψ ∈ sourceIsospectralSet hp φ) (m : ℤ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m) :
    SourceAngularDirichletTerminalIsEndpoint hp hp1 ψ.val m ↔
      SourceAngularDirichletTerminalIsEndpoint hp hp1 φ.val m := by
  have he := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  simp only [SourceAngularDirichletTerminalIsEndpoint,hμ,he.1,he.2]

namespace SourcePsiIsolatingComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
  {s t : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The full defining beta value sets depend only on the signed Dirichlet data
on an actual isospectral set. This includes regular and endpoint terminals. -/
theorem betaValues_eq_of_isospectral_root_sign
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hp hp1 V t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n m : ℤ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)
    (hσ : sourceDirichletSign hp hp1 ψ m = sourceDirichletSign hp hp1 φ m) :
    sourceAngularBetaValues hp hp1 n m s ψ.val = sourceAngularBetaValues hp hp1 n m t φ.val := by
  unfold sourceAngularBetaValues
  rw [propext (sourceAngularDirichletTerminalIsEndpoint_isospectral_iff hp hp1 φ ψ h m hμ),
    sourceAngularRegularDirichletValues_eq_of_isospectral hp hp1 φ ψ h n m s t
      (D.candidate_real_isospectral_agreement E φ ψ h n) hμ
      (sourceDirichletTerminal_eq_of_isospectral_root_sign hp hp1 φ ψ h m hμ hσ)]

/-- The actual chosen beta summand agrees without an open-gap or regular-terminal restriction. -/
theorem beta_eq_of_isospectral_root_sign
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hp hp1 V t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n m : ℤ)
    (hμ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)
    (hσ : sourceDirichletSign hp hp1 ψ m = sourceDirichletSign hp hp1 φ m) :
    sourceAngularBeta hp hp1 n m s ψ.val = sourceAngularBeta hp hp1 n m t φ.val := by
  unfold sourceAngularBeta
  rw [D.betaValues_eq_of_isospectral_root_sign E φ ψ h n m hμ hσ]

/-- Equal full signed Dirichlet data preserve the actual infinite beta correction.
Each literal summand is identified before taking the sum. -/
theorem betaCorrection_eq_of_isospectral_roots_signs
    (D : SourcePsiIsolatingComplexExtension hp hp1 W s)
    (E : SourcePsiIsolatingComplexExtension hp hp1 V t)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) (n : ℤ)
    (hμ : ∀ m, canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ.val m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m)
    (hσ : ∀ m, sourceDirichletSign hp hp1 ψ m = sourceDirichletSign hp hp1 φ m) :
    sourceAngularBetaCorrection hp hp1 n s ψ.val = sourceAngularBetaCorrection hp hp1 n t φ.val := by
  unfold sourceAngularBetaCorrection
  apply tsum_congr
  intro m
  simp only [sourceAngularBetaSeriesTerm,D.beta_eq_of_isospectral_root_sign E φ ψ h n m (hμ m) (hσ m)]

end SourcePsiIsolatingComplexExtension
end NLS.ZakharovShabat
