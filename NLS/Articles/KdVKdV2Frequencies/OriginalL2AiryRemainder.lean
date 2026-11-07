import NLS.Articles.KdVKdV2Frequencies.PhysicalL2PhaseError
import NLS.Articles.KdVKdV2Frequencies.OriginalL2InverseSmoothing
import NLS.FunctionalAnalysis.LinearRemainderBound

/-! An ORIGINAL physical mean-zero H1 realization of the exact difference
between the SAME actual KdV trajectory and the unit-period Airy group. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

def originalAiryFlow (s t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s) :=
  physicalRealMeanZeroPhaseFlow (Weight.sobolev s) airySignedFrequency airySignedFrequency_odd t q

theorem originalAiryFlow_coefficient (s t : ℝ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) (j : ℤ) :
    (originalAiryFlow s t q).val.val j=Complex.exp (((t*airySignedFrequency j:ℝ):ℂ)*I)*q.val.val j :=
  physicalRealMeanZeroPhaseFlow_apply _ _ _ _ _ _

theorem norm_originalAiryFlow (s t : ℝ)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) : ‖originalAiryFlow s t q‖=‖q‖ :=
  norm_physicalRealMeanZeroPhaseFlow _ _ _ _ _

theorem inverse_smoothing_coefficient_at_original_source (D : GlobalRoughAbelianForwardData)
    (S : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) →
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1))
    (hS : ∀ z j,(S z).val.val j=((originalL2Coordinates D).symm z).val.val j-
      (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*z.val.val j)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (S (originalL2Coordinates D q)).val.val j=q.val.val j-
      (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*(originalL2Coordinates D q).val.val j := by
  simpa only [(originalL2Coordinates D).symm_apply_apply] using hS (originalL2Coordinates D q) j

def originalL2AiryRemainder (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (L : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1) ≃L[ℝ]
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)))
    (S : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) →
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1))
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1) :=
  L.symm (originalL2StrongPhaseError D G h t q)+
    S (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q))-
      originalAiryFlow 1 t (S (originalL2Coordinates D q))

theorem originalL2AiryRemainder_coefficient (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (L : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1) ≃L[ℝ]
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)))
    (hL : ∀ q j,(L q).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j)
    (S : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) →
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1))
    (hS : ∀ z j,(S z).val.val j=((originalL2Coordinates D).symm z).val.val j-
      (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*z.val.val j)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) (j : ℤ) :
    (originalL2AiryRemainder D G h L S t q).val.val j=
      (originalKdVBirkhoffFlow D 0 (by norm_num) G t q).val.val j-
        Complex.exp (((t*airySignedFrequency j:ℝ):ℂ)*I)*q.val.val j := by
  change (L.symm (originalL2StrongPhaseError D G h t q)).val.val j+
    (S (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q))).val.val j-
      (originalAiryFlow 1 t (S (originalL2Coordinates D q))).val.val j=_
  rw [physical_mean_zero_fourier_inverse_coefficient _ _ L hL,originalL2StrongPhaseError_coefficient,
    inverse_smoothing_coefficient_at_original_source D S hS,originalAiryFlow_coefficient,
    inverse_smoothing_coefficient_at_original_source D S hS]
  ring

theorem originalL2AiryRemainder_inclusion (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (L : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1) ≃L[ℝ]
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)))
    (hL : ∀ q j,(L q).val.val j=(Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)⁻¹*q.val.val j)
    (S : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) →
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1))
    (hS : ∀ z j,(S z).val.val j=((originalL2Coordinates D).symm z).val.val j-
      (Real.sqrt (2*(j.natAbs:ℝ)*Real.pi):ℂ)*z.val.val j)
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    physicalRealMeanZeroSobolevInclusion (by norm_num : (0:ℝ)≤1) (originalL2AiryRemainder D G h L S t q)=
      originalKdVBirkhoffFlow D 0 (by norm_num) G t q-originalAiryFlow 0 t q := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [physicalRealMeanZeroSobolevInclusion_coefficient]
  change _=(originalKdVBirkhoffFlow D 0 (by norm_num) G t q).val.val j-(originalAiryFlow 0 t q).val.val j
  rw [originalAiryFlow_coefficient]
  exact originalL2AiryRemainder_coefficient D G h L hL S hS t q j

theorem norm_originalL2AiryRemainder_le (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (L : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1) ≃L[ℝ]
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (1+1/2)))
    (S : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (0+1/2)) →
      physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1))
    (t : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) :
    ‖originalL2AiryRemainder D G h L S t q‖≤
      ‖L.symm.toContinuousLinearMap‖*‖originalL2StrongPhaseError D G h t q‖+
        ‖S (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q))‖+
          ‖S (originalL2Coordinates D q)‖ := by
  have hb := NLS.FunctionalAnalysis.norm_clm_add_sub_le L.symm.toContinuousLinearMap
    (originalL2StrongPhaseError D G h t q)
    (S (originalL2Coordinates D (originalKdVBirkhoffFlow D 0 (by norm_num) G t q)))
    (originalAiryFlow 1 t (S (originalL2Coordinates D q)))
  simpa only [norm_originalAiryFlow] using! hb

end NLS.Articles.KdVKdV2Frequencies
