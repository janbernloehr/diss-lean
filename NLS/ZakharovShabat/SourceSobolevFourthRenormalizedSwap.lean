import NLS.ZakharovShabat.SourceSobolevFourthFrequencySwap
import NLS.ZakharovShabat.SourceSobolevFourthMomentIdentification

/-! # Exact lower-Hamiltonian and normalized-frequency swap covariance -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.ZakharovShabat

/-- The independently defined physical mass is invariant under component
exchange throughout the native H₄ domain. -/
theorem sourceFourthSobolevMass_componentSwap (a : NativeFourthSobolevSource) :
    sourceFourthSobolevMass (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) =
      sourceFourthSobolevMass a := by
  apply eq_of_continuous_weighted_finiteGap (by simp) (by norm_num) fourthSobolevSpectralWeight
    (fun b => sourceFourthSobolevMass (weightedRealSourceComponentSwap fourthSobolevSpectralWeight b))
    sourceFourthSobolevMass
    ((continuous_iff_continuousAt.mpr fun b => (analyticAt_sourceFourthSobolevMass b).continuousAt).comp
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight).continuous)
    (continuous_iff_continuousAt.mpr fun b => (analyticAt_sourceFourthSobolevMass b).continuousAt) _ a
  intro b hf
  have hs : originalWeightedRealSource fourthSobolevSpectralWeight
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight b) ∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
    rw [originalWeightedRealSource_componentSwap]
    exact realSourceComponentSwap_mem_finiteGap (by simp) (by norm_num) _ hf
  rw [sourceFourthSobolevMass_eq_finiteGap _ hs,sourceFourthSobolevMass_eq_finiteGap _ hf]
  simpa only [originalWeightedRealSource_componentSwap,pow_zero,one_mul] using
    sourceFiniteGapNLSHamiltonian_componentSwap (by simp) (by norm_num) _ hf 0

/-- Physical momentum changes sign under the same actual field exchange. -/
theorem sourceFourthSobolevMomentum_componentSwap (a : NativeFourthSobolevSource) :
    sourceFourthSobolevMomentum (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) =
      -sourceFourthSobolevMomentum a := by
  apply eq_of_continuous_weighted_finiteGap (by simp) (by norm_num) fourthSobolevSpectralWeight
    (fun b => sourceFourthSobolevMomentum (weightedRealSourceComponentSwap fourthSobolevSpectralWeight b))
    (fun b => -sourceFourthSobolevMomentum b)
    ((continuous_iff_continuousAt.mpr fun b => (analyticAt_sourceFourthSobolevMomentum b).continuousAt).comp
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight).continuous)
    (continuous_iff_continuousAt.mpr fun b => (analyticAt_sourceFourthSobolevMomentum b).continuousAt).neg _ a
  intro b hf
  have hs : originalWeightedRealSource fourthSobolevSpectralWeight
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight b) ∈
      sourceFiniteGapLocus (by simp) (by norm_num) := by
    rw [originalWeightedRealSource_componentSwap]
    exact realSourceComponentSwap_mem_finiteGap (by simp) (by norm_num) _ hf
  rw [sourceFourthSobolevMomentum_eq_finiteGap _ hs,sourceFourthSobolevMomentum_eq_finiteGap _ hf]
  simpa only [originalWeightedRealSource_componentSwap,pow_one,neg_one_mul] using
    sourceFiniteGapNLSHamiltonian_componentSwap (by simp) (by norm_num) _ hf 1

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Full off-diagonal swap covariance of the independently normalized
physical H₄ frequency, with every physical shift retained. -/
theorem normalizedSobolevFourthFrequency_componentSwap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    D.normalizedSobolevFourthFrequency
      (weightedRealSourceComponentSwap fourthSobolevSpectralWeight a) n =
      -D.normalizedSobolevFourthFrequency a (-n) := by
  unfold normalizedSobolevFourthFrequency
  rw [D.sobolevFourthFrequency_componentSwap,sourceFourthSobolevMass_componentSwap,
    sourceFourthSobolevMomentum_componentSwap]
  push_cast
  ring

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
