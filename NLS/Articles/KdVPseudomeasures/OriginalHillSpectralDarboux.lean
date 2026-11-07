import NLS.Articles.KdVPseudomeasures.OriginalHillSpectralCrossBrackets
import NLS.KdV.HillLocalSpectralDarboux

/-! The full local spectral Gardner matrix at the SAME original
physical potential. The actual local norming logarithms remain spectral
auxiliaries; the article Abelian angles and Birkhoff map are unchanged. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_normings_Gardner_commute (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillHminusDirichletNorming n) (hillHminusDirichletNorming m)
      (originalPeriodOneCoefficients q)=0 :=
  hillHminusNormings_Gardner_commute n m _
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))

theorem original_Hill_normings_physical_Gardner_integral_zero
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    (∫ x in (0:ℝ)..1,
      periodOneSobolevSynthesis (hillHminusNormingGradient n (originalPeriodOneCoefficients q))
        (x : AddCircle (2:ℝ))*
      deriv (fun t : ℝ => periodOneSobolevSynthesis
        (hillHminusNormingGradient m (originalPeriodOneCoefficients q)) (t : AddCircle (2:ℝ))) x)=0 := by
  rw [← NLS.Poisson.gardnerBivector_eq_physical_integral]
  exact original_Hill_normings_Gardner_commute q n m

theorem original_Hill_normings_intrinsic_Gardner_commute
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.gardnerMeanZeroCotangentBivector
      ((fderiv ℂ (hillHminusDirichletNorming n) (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)
      ((fderiv ℂ (hillHminusDirichletNorming m) (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)=0 := by
  rw [NLS.Poisson.gardnerMeanZeroCotangentBivector_restrict]
  exact original_Hill_normings_Gardner_commute q n m

theorem original_Hill_local_spectral_Gardner_matrix (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n) (hillHminusCanonicalDirichlet m)
      (originalPeriodOneCoefficients q)=0 ∧
      NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet n)
        (hillHminusLocalLogNorming m (originalPeriodOneCoefficients q)) (originalPeriodOneCoefficients q)=
        (if n=m then 1 else 0) ∧
      NLS.Poisson.hminusGardnerBracket (hillHminusLocalLogNorming n (originalPeriodOneCoefficients q))
        (hillHminusLocalLogNorming m (originalPeriodOneCoefficients q)) (originalPeriodOneCoefficients q)=0 :=
  hillHminus_local_spectral_Gardner_matrix n m _
    (real_mem_hillHminusCanonicalDirichletDomain _ (originalPeriodOneCoefficients_real q))

end NLS.Articles.KdVPseudomeasures
