import NLS.Articles.KdVPseudomeasures.OriginalHillDifferentialActionInvariance
import NLS.KdV.HillOffIndexCorrectionGardnerLimit

/-! Actual physical off-index Abelian variations at the original
potential, including the closed-mean-zero bracket and the derivative
limit for the complete infinite correction. The on-index angle and
the complete angle/action Kronecker matrix remain further steps. -/
noncomputable section
open Set Complex Filter Topology NLS.LpSequence
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_offIndex_Abelian_action_Gardner_cleared
    (q : OriginalHminusOnePotential) (n m k : ℕ+) (hmn : m ≠ n) :
    hillHminusDirichletSheet m (originalPeriodOneCoefficients q)*
      NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
        (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q) =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m (originalPeriodOneCoefficients q),
        originalPeriodOneCoefficients q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q) :=
  hillHminusPhysicalOffIndexAbelianValue_action_Gardner_cleared_of_real n m k hmn _
    (originalPeriodOneCoefficients_real q)

theorem original_Hill_offIndex_Abelian_action_intrinsic_Gardner_cleared
    (q : OriginalHminusOnePotential) (n m k : ℕ+) (hmn : m ≠ n) :
    hillHminusDirichletSheet m (originalPeriodOneCoefficients q)*
      NLS.Poisson.gardnerMeanZeroCotangentBivector
        ((fderiv ℂ (hillHminusPhysicalOffIndexAbelianValue n m) (originalPeriodOneCoefficients q)).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)
        ((fderiv ℂ (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q)).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m (originalPeriodOneCoefficients q),
        originalPeriodOneCoefficients q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q) := by
  rw [NLS.Poisson.gardnerMeanZeroCotangentBivector_restrict]
  exact original_Hill_offIndex_Abelian_action_Gardner_cleared q n m k hmn

theorem original_Hill_offIndex_Abelian_action_Gardner_of_sheet_ne_zero
    (q : OriginalHminusOnePotential) (n m k : ℕ+) (hmn : m ≠ n)
    (hs : hillHminusDirichletSheet m (originalPeriodOneCoefficients q) ≠ 0) :
    NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
      (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q) =
      (hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m (originalPeriodOneCoefficients q),
        originalPeriodOneCoefficients q)/hillHminusDirichletSheet m (originalPeriodOneCoefficients q))*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q) :=
  hillHminusPhysicalOffIndexAbelianValue_action_Gardner_of_sheet_ne_zero n m k hmn _
    (real_mem_hillHminusPhysicalAbelianDomain _ (originalPeriodOneCoefficients_real q)) hs

theorem original_Hill_infinite_Abelian_correction_Gardner_limit
    (q : OriginalHminusOnePotential) (n k : ℕ+) :
    Tendsto (fun N : ℕ => ∑ j ∈ Finset.Icc (-(N:ℤ)) N,
      NLS.Poisson.hminusGardnerBracket
        (fun a => positiveScalarExtension (hillHminusOffIndexAbelianTerm n a) j)
        (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q)) atTop
        (𝓝 (NLS.Poisson.hminusGardnerBracket (hillHminusOffIndexAbelianCorrection n)
          (hillHminusCanonicalAction k) (originalPeriodOneCoefficients q))) :=
  tendsto_hillHminusOffIndexAbelian_Gardner_sums n (hillHminusCanonicalAction k) _
    (real_mem_hillHminusOffIndexAnalyticDomain _ (originalPeriodOneCoefficients_real q))

end NLS.Articles.KdVPseudomeasures
