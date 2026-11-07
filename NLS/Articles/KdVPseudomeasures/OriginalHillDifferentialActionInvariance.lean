import NLS.Articles.KdVPseudomeasures.OriginalHillSpectralDarboux
import NLS.KdV.HillCanonicalDifferentialIsospectral

/-! Actual normalized numerators and energy differentials at the
original physical potential are stationary along the actual Gardner
action directions. These are infinitesimal identities; the article
Abelian angles and signed Birkhoff canonicality remain further steps. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier

theorem original_Hill_numerators_action_Gardner_commute
    (q : OriginalHminusOnePotential) (n m : ℕ+) (E : ℂ) :
    NLS.Poisson.hminusGardnerBracket (fun a => hillHminusCanonicalPsi n (E,a))
      (hillHminusCanonicalAction m) (originalPeriodOneCoefficients q) = 0 :=
  hillHminusCanonicalPsi_action_Gardner_commute_of_real n m E _
    (originalPeriodOneCoefficients_real q)

theorem original_Hill_numerators_action_Hamiltonian_direction
    (q : OriginalHminusOnePotential) (n m : ℕ+) (E : ℂ) :
    (fderiv ℂ (fun a => hillHminusCanonicalPsi n (E,a)) (originalPeriodOneCoefficients q))
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction m)
        (originalPeriodOneCoefficients q)) = 0 := by
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact original_Hill_numerators_action_Gardner_commute q n m E

theorem original_Hill_energyRoot_action_Gardner_commute
    (q : OriginalHminusOnePotential) (m : ℕ+) (E : ℂ) (hE : E.im ≠ 0) :
    NLS.Poisson.hminusGardnerBracket (fun a => hillHminusCanonicalEnergyRoot (E,a))
      (hillHminusCanonicalAction m) (originalPeriodOneCoefficients q) = 0 :=
  hillHminusCanonicalEnergyRoot_action_Gardner_commute E m _
    (nonreal_mem_hillHminusCanonicalEnergyRootDomain E hE _ (originalPeriodOneCoefficients_real q))
    (real_mem_hillHminusCanonicalActionDomain _ (originalPeriodOneCoefficients_real q))

theorem original_Hill_energyDifferential_action_Gardner_commute
    (q : OriginalHminusOnePotential) (n m : ℕ+) (E : ℂ) (hE : E.im ≠ 0) :
    NLS.Poisson.hminusGardnerBracket (fun a => hillHminusCanonicalEnergyDifferential n (E,a))
      (hillHminusCanonicalAction m) (originalPeriodOneCoefficients q) = 0 :=
  hillHminusCanonicalEnergyDifferential_action_Gardner_commute n m E _
    (nonreal_mem_hillHminusCanonicalEnergyRootDomain E hE _ (originalPeriodOneCoefficients_real q))

theorem original_Hill_energyDifferential_action_Hamiltonian_direction
    (q : OriginalHminusOnePotential) (n m : ℕ+) (E : ℂ) (hE : E.im ≠ 0) :
    (fderiv ℂ (fun a => hillHminusCanonicalEnergyDifferential n (E,a)) (originalPeriodOneCoefficients q))
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction m)
        (originalPeriodOneCoefficients q)) = 0 := by
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact original_Hill_energyDifferential_action_Gardner_commute q n m E hE

theorem original_Hill_energyDifferential_intrinsic_Gardner_action_commute
    (q : OriginalHminusOnePotential) (n m : ℕ+) (E : ℂ) (hE : E.im ≠ 0) :
    NLS.Poisson.gardnerMeanZeroCotangentBivector
      ((fderiv ℂ (fun a => hillHminusCanonicalEnergyDifferential n (E,a))
        (originalPeriodOneCoefficients q)).comp
          (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL)
      ((fderiv ℂ (hillHminusCanonicalAction m) (originalPeriodOneCoefficients q)).comp
        (WeightedCoeff.zeroModeSubmodule (Weight.sobolev (-1)) 2).subtypeL) = 0 := by
  rw [NLS.Poisson.gardnerMeanZeroCotangentBivector_restrict]
  exact original_Hill_energyDifferential_action_Gardner_commute q n m E hE

end NLS.Articles.KdVPseudomeasures
