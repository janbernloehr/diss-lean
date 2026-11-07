import NLS.Articles.KdVPseudomeasures.OriginalCanonicalActions
import NLS.Articles.KdVPseudomeasures.OriginalHillGardnerBrackets
import NLS.KdV.HillCanonicalActionIsospectral

/-! The original physical Hill actions commute under the literal
unit-period Gardner bracket, intrinsically on the closed mean-zero
source. Their Hamiltonian directions are first-order isospectral.
Action-angle and signed-coordinate canonical relations remain separate. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_actions_Gardner_commute
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalAction n) (hillHminusCanonicalAction m)
      (originalPeriodOneCoefficients q)=0 :=
  hillHminusCanonicalActions_Gardner_commute_of_real _ (originalPeriodOneCoefficients_real q) n m

theorem original_Hill_actions_intrinsic_Gardner_commute
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    NLS.Poisson.gardnerMeanZeroCotangentBivector
      ((fderiv ℂ (hillHminusCanonicalAction n) (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)
      ((fderiv ℂ (hillHminusCanonicalAction m) (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)=0 := by
  rw [NLS.Poisson.gardnerMeanZeroCotangentBivector_restrict]
  exact original_Hill_actions_Gardner_commute q n m

theorem original_Hill_actions_physical_Gardner_integral_zero
    (q : OriginalHminusOnePotential) (n m : ℕ+) :
    (∫ x in (0:ℝ)..1,
      periodOneSobolevSynthesis
        (NLS.Poisson.hminusScalarGradient (hillHminusCanonicalAction n) (originalPeriodOneCoefficients q))
        (x : AddCircle (2:ℝ))*
      deriv (fun t : ℝ => periodOneSobolevSynthesis
        (NLS.Poisson.hminusScalarGradient (hillHminusCanonicalAction m) (originalPeriodOneCoefficients q))
        (t : AddCircle (2:ℝ))) x)=0 := by
  rw [← NLS.Poisson.gardnerBivector_eq_physical_integral]
  exact original_Hill_actions_Gardner_commute q n m

theorem original_Hill_action_discriminant_Gardner_commute
    (q : OriginalHminusOnePotential) (μ : ℂ) (n : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (fun p => hillHminusDiscriminant p μ) (hillHminusCanonicalAction n)
      (originalPeriodOneCoefficients q)=0 :=
  hillHminusDiscriminant_action_Gardner_commute_of_real _ (originalPeriodOneCoefficients_real q) μ n

theorem original_Hill_action_Hamiltonian_direction_isospectral
    (q : OriginalHminusOnePotential) (μ : ℂ) (n : ℕ+) :
    (fderiv ℂ (fun p => hillHminusDiscriminant p μ) (originalPeriodOneCoefficients q))
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction n) (originalPeriodOneCoefficients q))=0 := by
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact original_Hill_action_discriminant_Gardner_commute q μ n

end NLS.Articles.KdVPseudomeasures
