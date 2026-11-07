import NLS.Articles.KdVPseudomeasures.OriginalHillSignedComplexCoordinates
import NLS.KdV.HillNativeFreeGardnerRelations
import NLS.Poisson.GardnerPhysicalIntegral
import NLS.Poisson.GardnerBracketJacobi
import NLS.Poisson.GardnerZeroModeRestriction

/-! The article's ACTUAL signed coordinates have well-defined physical
Gardner brackets, analytic on the common native complex domain and
intrinsic to the correct mean-zero source. Their canonical matrix at zero
has the exact printed sign i. Global canonicality is NOT asserted. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_signed_coordinate_native (q : OriginalHminusOnePotential) (k : ℤ) :
    (originalHillSignedComplexCoordinates q).val.val k=
      hillHminusNativeCoordinate k (originalPeriodOneCoefficients q) := by
  change (hillMeanZeroComplexMap _).val.val k=_
  rw [hillMeanZeroComplexMap_coe]
  rfl

def originalHillGardnerBracket (k l : ℤ) (q : OriginalHminusOnePotential) : ℂ :=
  hillHminusNativeGardnerBracket k l (originalPeriodOneCoefficients q)

theorem original_Hill_Gardner_bracket_physical (k l : ℤ) (q : OriginalHminusOnePotential) :
    originalHillGardnerBracket k l q=∫ x in (0:ℝ)..1,
      periodOneSobolevSynthesis (hillHminusNativeCoordinateGradient k (originalPeriodOneCoefficients q))
        (x : AddCircle (2:ℝ))*
      deriv (fun t : ℝ => periodOneSobolevSynthesis
        (hillHminusNativeCoordinateGradient l (originalPeriodOneCoefficients q)) (t : AddCircle (2:ℝ))) x :=
  NLS.Poisson.gardnerBivector_eq_physical_integral _ _

theorem original_Hill_Gardner_bracket_analytic (k l : ℤ) :
    AnalyticOnNhd ℂ (hillHminusNativeGardnerBracket k l) hillHminusActionAngleNativeDomain :=
  analyticOnNhd_hillHminusNativeGardnerBracket k l

theorem original_Hill_Gardner_bracket_intrinsic (k l : ℤ) (q : PeriodOneHminusOne) :
    NLS.Poisson.gardnerMeanZeroCotangentBivector
      ((fderiv ℂ (hillHminusNativeCoordinate k) q).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)
      ((fderiv ℂ (hillHminusNativeCoordinate l) q).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)=
      hillHminusNativeGardnerBracket k l q :=
  NLS.Poisson.gardnerMeanZeroCotangentBivector_restrict _ _

theorem original_Hill_Gardner_bracket_jacobi (k l m : ℤ) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) :
    NLS.Poisson.hminusGardnerBracket (hillHminusNativeGardnerBracket k l) (hillHminusNativeCoordinate m) q+
      NLS.Poisson.hminusGardnerBracket (hillHminusNativeGardnerBracket l m) (hillHminusNativeCoordinate k) q+
      NLS.Poisson.hminusGardnerBracket (hillHminusNativeGardnerBracket m k) (hillHminusNativeCoordinate l) q=0 :=
  NLS.Poisson.hminusGardnerBracket_jacobi _ _ _ q
    (analyticOnNhd_hillHminusNativeCoordinate k q hq)
    (analyticOnNhd_hillHminusNativeCoordinate l q hq)
    (analyticOnNhd_hillHminusNativeCoordinate m q hq)

theorem original_Hill_Gardner_brackets_at_zero (n m : ℕ+) :
    hillHminusNativeGardnerBracket (n:ℤ) (-(m:ℤ)) 0=(if n=m then I else 0) ∧
      hillHminusNativeGardnerBracket (n:ℤ) (m:ℤ) 0=0 ∧
      hillHminusNativeGardnerBracket (-(n:ℤ)) (-(m:ℤ)) 0=0 :=
  ⟨hillHminusNativeGardnerBracket_positive_negative_zero n m,
    hillHminusNativeGardnerBracket_positive_positive_zero n m,
    hillHminusNativeGardnerBracket_negative_negative_zero n m⟩

end NLS.Articles.KdVPseudomeasures
