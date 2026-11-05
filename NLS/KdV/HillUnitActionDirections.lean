import NLS.KdV.HillUnitRealSourceUnembed
import NLS.KdV.HillRealActionHamiltonians

/-! # The actual physical action Hamiltonian directions in unit Fourier coordinates -/
noncomputable section
namespace NLS.KdV

def hillUnitActionDirection (p : RealHillWeightedPotential SpectralWeight.one) (m : ℕ) : Coeff 2 :=
  let q := hillRealWeightedEmbedding SpectralWeight.one p
  Fourier.paritySample 0 (hillL2TracePeriodDirection q.val q.property.1 q.property.2 m)

theorem hillUnitActionDirection_zero (p : RealHillWeightedPotential SpectralWeight.one)
    (m : ℕ) (hm : 1 ≤ m) : hillUnitActionDirection p m 0 = 0 := by
  rw [hillUnitActionDirection,hillUnitSample_apply,mul_zero]
  exact hillL2TracePeriodDirection_zero _ _ _ m hm

theorem periodDouble_hillUnitActionDirection (p : RealHillWeightedPotential SpectralWeight.one)
    (m : ℕ) (hm : 1 ≤ m) :
    Coeff.periodDouble (hillUnitActionDirection p m) =
      let q := hillRealWeightedEmbedding SpectralWeight.one p
      hillL2TracePeriodDirection q.val q.property.1 q.property.2 m :=
  hillPeriodDouble_unitSample _ (hillL2TracePeriodDirection_mem_parity _ _ _ m hm)

theorem hillUnitActionDirection_real (p : RealHillWeightedPotential SpectralWeight.one)
    (m : ℕ) (hm : 1 ≤ m) : periodOneL2Conjugation (hillUnitActionDirection p m) = hillUnitActionDirection p m := by
  apply (periodOneL2Conjugation_fixed_iff _).mpr
  intro j
  simp only [hillUnitActionDirection,hillUnitSample_apply,show 2*(-j) = -(2*j) by ring]
  exact hillL2TracePeriodDirection_isReal _ _ _ m hm (2*j)

def hillDeletedActionDirection (p : RealHillWeightedPotential SpectralWeight.one)
    (m : ℕ) (hm : 1 ≤ m) : DeletedCoeff 2 0 :=
  ⟨hillUnitActionDirection p m,hillUnitActionDirection_zero p m hm⟩

end NLS.KdV
