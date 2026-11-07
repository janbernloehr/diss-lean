import NLS.Articles.KdVPseudomeasures.OriginalHillGardnerBrackets
import NLS.KdV.HillDiscriminantContourInvolution

/-! Spectral involution for the SAME original physical Hill potential.
All energy pairs and all complex native H-minus-one sources are covered.
Neither action involution nor coordinate canonicality is asserted here. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem original_Hill_discriminants_Gardner_commute
    (q : OriginalHminusOnePotential) (μ ν : ℂ) :
    NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ)
      (fun p => hillHminusDiscriminant p ν) (originalPeriodOneCoefficients q)=0 :=
  hillHminusDiscriminants_Gardner_commute _ μ ν

theorem original_Hill_discriminants_intrinsic_Gardner_commute
    (q : OriginalHminusOnePotential) (μ ν : ℂ) :
    NLS.Poisson.gardnerMeanZeroCotangentBivector
      ((hillHminusDiscriminantCotangent μ (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)
      ((hillHminusDiscriminantCotangent ν (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)=0 := by
  rw [NLS.Poisson.gardnerMeanZeroCotangentBivector_restrict]
  exact hillHminusDiscriminantCotangents_Gardner_commute _ μ ν

theorem original_Hill_discriminant_contour_direction_isospectral
    (q : OriginalHminusOnePotential) (w : ℂ → ℂ) (c : ℂ) (R : ℝ) (μ : ℂ)
    (hw : CircleIntegrable (fun ν => w ν • hillHminusDiscriminantCotangent ν
      (originalPeriodOneCoefficients q)) c R) :
    (hillHminusDiscriminantCotangent μ (originalPeriodOneCoefficients q))
      (NLS.Poisson.gardnerHamiltonianDirection
        (hillHminusDiscriminantContourCotangent (originalPeriodOneCoefficients q) w c R))=0 :=
  hillHminusDiscriminantContourDirection_isospectral _ w c R μ hw

end NLS.Articles.KdVPseudomeasures
