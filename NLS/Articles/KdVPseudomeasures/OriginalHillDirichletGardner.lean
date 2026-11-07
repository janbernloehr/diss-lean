import NLS.Articles.KdVPseudomeasures.OriginalAnalyticDirichletCoordinates
import NLS.Articles.KdVPseudomeasures.OriginalHillGardnerBrackets
import NLS.KdV.HillMixedDirichletGardner

/-! Actual original Dirichlet spectral Gardner identities. The common
complex domain, original physical potential and prescribed sheet sign
are retained; coordinate canonicality is not assumed. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem original_Hill_Dirichlet_characteristics_Gardner_commute
    (q : OriginalHminusOnePotential) (μ ν : ℂ) :
    NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDirichlet p μ) (fun p => hillHminusDirichlet p ν)
      (originalPeriodOneCoefficients q)=0 :=
  hillHminusDirichletCharacteristics_Gardner_commute _ μ ν

theorem original_Hill_Dirichlet_eigenvalues_Gardner_commute
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusCanonicalDirichlet m)
      (originalPeriodOneCoefficients q)=0 :=
  hillHminusCanonicalDirichlets_Gardner_commute n m _
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))

theorem original_Hill_Dirichlet_eigenvalues_intrinsic_Gardner_commute
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.gardnerMeanZeroCotangentBivector
      ((fderiv ℂ (hillHminusCanonicalDirichlet n) (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)
      ((fderiv ℂ (hillHminusCanonicalDirichlet m) (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)=0 := by
  rw [NLS.Poisson.gardnerMeanZeroCotangentBivector_restrict]
  exact original_Hill_Dirichlet_eigenvalues_Gardner_commute q n m

theorem original_Hill_discriminant_Dirichlet_Gardner
    (q : OriginalHminusOnePotential) (n : ℕ+) (μ : ℂ) :
    2*(μ-hillHminusCanonicalDirichlet n (originalPeriodOneCoefficients q))*
      deriv (hillHminusDirichlet (originalPeriodOneCoefficients q)) (hillHminusCanonicalDirichlet n (originalPeriodOneCoefficients q))*
      NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalDirichlet n)
        (originalPeriodOneCoefficients q)=
      -hillHminusDirichlet (originalPeriodOneCoefficients q) μ*hillHminusDirichletSheet n (originalPeriodOneCoefficients q) :=
  hillHminus_discriminant_Dirichlet_Gardner n μ _
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))

end NLS.Articles.KdVPseudomeasures
