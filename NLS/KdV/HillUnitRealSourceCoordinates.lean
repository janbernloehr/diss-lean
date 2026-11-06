import NLS.KdV.HillAbelianCoordinateContinuity
import NLS.SequenceSpaces.PeriodOneL2RealFormIdentity

/-! # Exact physical real source coordinates at unit spectral weight -/
noncomputable section
open scoped ComplexConjugate
namespace NLS.KdV

def hillUnitSourceLift : Coeff 2 ≃ₗᵢ[ℂ] WeightedCoeff SpectralWeight.one.doubleIndex.toWeight 2 :=
  (WeightedCoeff.weightIsometry SpectralWeight.one.doubleIndex.toWeight 2).symm

theorem hillUnitSourceLift_toCoeff (u : Coeff 2) :
    SpectralWeight.one.doubleIndex.toCoeff (hillUnitSourceLift u) = u := by
  ext j
  rw [SpectralWeight.toCoeff_apply]
  change u j / (1 : ℂ) = u j
  exact div_one _

def hillUnitRealSourceLift (u : Coeff 2) (hu : periodOneL2Conjugation u = u) :
    RealHillWeightedPotential SpectralWeight.one :=
  ⟨hillUnitSourceLift u,by
    rw [hillUnitSourceLift_toCoeff]
    exact (periodOneL2Conjugation_fixed_iff u).mp hu⟩

theorem hillUnitRealSourceLift_toCoeff (u : Coeff 2) (hu : periodOneL2Conjugation u = u) :
    SpectralWeight.one.doubleIndex.toCoeff (hillUnitRealSourceLift u hu).val = u :=
  hillUnitSourceLift_toCoeff u

end NLS.KdV
