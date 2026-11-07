import NLS.KdV.HillOriginalBirkhoffSobolevRestriction
import NLS.KdV.HillNativeIntegerLower
import NLS.SequenceSpaces.RealWeightedNatPairInclusion

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

theorem hillOriginalWeightedMeanZeroSource_integer_lower (M j : ℕ) (hj : j ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    hillOriginalWeightedMeanZeroSource (hillIntegerWeight j) (hillRealNativeIntegerLower M j hj p)
        (hillRealNativeIntegerLower_mean_zero M j hj p hmean) =
      hillOriginalWeightedMeanZeroSource (hillIntegerWeight M) p hmean := by
  apply Subtype.ext
  apply Subtype.ext
  exact hillPeriodOneUnitPotential_lower M j hj p.val

theorem norm_hillOriginalBirkhoffSobolevRestriction_lower (M j : ℕ) (hj : j ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    ‖hillOriginalBirkhoffSobolevRestriction M j hj p hmean‖ =
      ‖hillOriginalBirkhoffSobolevRestriction j j le_rfl (hillRealNativeIntegerLower M j hj p)
        (hillRealNativeIntegerLower_mean_zero M j hj p hmean)‖ := by
  apply RealWeightedNatPair.norm_eq_of_coordinates
  intro k
  exact congrArg (fun q : hillRealMeanZeroSourceSubmodule => (hillOriginalBirkhoffMap q).val k)
    (hillOriginalWeightedMeanZeroSource_integer_lower M j hj p hmean).symm

theorem norm_hillOriginalBirkhoffSobolevRestriction_zero_le (M : ℕ)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    ‖hillOriginalBirkhoffSobolevRestriction M 0 (Nat.zero_le M) p hmean‖ ≤
      ‖(hillRealNativeIntegerLower M 0 (Nat.zero_le M) p).val‖ := by
  rw [norm_hillOriginalBirkhoffSobolevRestriction]
  have hsq := norm_hillHomogeneousSpectralSequence_sq (by simp) (by intro k; simp)
    M 0 (Nat.zero_le M) p
  have hmass := tsum_hillNativeBaseActions_eq_half_norm M p hmean
  dsimp only at hmass
  change hillNativeActionMass M 0 p = (1/2 : ℝ)*‖hillPeriodOneUnitPotential (hillIntegerWeight M) p.val‖^2 at hmass
  have hB := norm_hillPeriodOneUnitPotential_le (hillIntegerWeight 0)
    (hillRealNativeIntegerLower M 0 (Nat.zero_le M) p).val
  change ‖hillPeriodOneUnitPotential (hillIntegerWeight 0) (hillNativeIntegerLower M 0 (Nat.zero_le M) p.val)‖ ≤
    ‖(hillRealNativeIntegerLower M 0 (Nat.zero_le M) p).val‖ at hB
  rw [hillPeriodOneUnitPotential_lower M 0 (Nat.zero_le M) p.val] at hB
  have hB2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
  nlinarith [norm_nonneg (hillHomogeneousSpectralSequence (by simp) (by intro k; simp) M 0 (Nat.zero_le M) p),
    norm_nonneg (hillRealNativeIntegerLower M 0 (Nat.zero_le M) p).val]

end NLS.KdV
