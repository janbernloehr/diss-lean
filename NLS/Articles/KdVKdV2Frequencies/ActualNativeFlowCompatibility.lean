import NLS.Articles.KdVKdV2Frequencies.ActualNativeSourceFlow

/-! The SAME KdV phase evolution commutes with the actual native-to-weak
inclusions. No order-dependent physical solution is chosen. -/
noncomputable section
open Set Complex NLS.Articles.KdVConvexity
namespace NLS.Articles.KdVKdV2Frequencies

theorem normalizedSobolevWeakActionInclusion_base (a : Coeff 1) :
    normalizedSobolevWeakActionInclusion (-1) le_rfl a=a := by
  ext k
  rw [normalizedSobolevWeakActionInclusion_apply,baseActionWeight_eq_sobolev]
  exact mul_div_cancel₀ _ (Weight.complex_ne_zero _ _)

theorem nativeTargetWeakActions_inclusion (t : ℝ) (ht : 0≤t) (z : physicalRealDeletedSubmodule) :
    nativeTargetWeakActions t ht z=
      nativeTargetWeakActions 0 (by norm_num)
        (physicalRealSobolevInclusion (by linarith : (-1/2:ℝ)≤t-1/2) z) := by
  unfold nativeTargetWeakActions nativeTargetActions
  simp only [show (2:ℝ)*0-1= -1 by norm_num,normalizedSobolevWeakActionInclusion_base]
  exact normalizedSobolevWeakActionInclusion_signed_actions t ht z.val

theorem nativeTargetKdVSignedFrequency_inclusion (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (z : physicalRealDeletedSubmodule) :
    nativeTargetKdVSignedFrequency t ht G z=
      nativeTargetKdVSignedFrequency 0 (by norm_num) G
        (physicalRealSobolevInclusion (by linarith : (-1/2:ℝ)≤t-1/2) z) := by
  unfold nativeTargetKdVSignedFrequency nativeTargetKdVNaturalFrequency nativeTargetKdVFrequency
  rw [nativeTargetWeakActions_inclusion]

theorem nativeTargetKdVPhaseFlow_weak (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (time : ℝ) (z : physicalRealDeletedSubmodule) :
    physicalRealSobolevInclusion (by linarith : (-1/2:ℝ)≤t-1/2)
      (nativeTargetKdVPhaseFlow t ht G time z)=
      nativeTargetKdVPhaseFlow 0 (by norm_num) G time
        (physicalRealSobolevInclusion (by linarith : (-1/2:ℝ)≤t-1/2) z) := by
  unfold nativeTargetKdVPhaseFlow
  rw [physicalRealSobolevInclusion_phaseRotation]
  simp only [nativeTargetKdVSignedFrequency_inclusion t ht G z]

theorem nativeKdVSourceFlow_weak (D : GlobalRoughAbelianForwardData) (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    physicalRealSobolevInclusion (by linarith : (-1:ℝ)≤t-1) (nativeKdVSourceFlow D t ht G time a)=
      nativeKdVSourceFlow D 0 (by norm_num) G time
        (physicalRealSobolevInclusion (by linarith : (-1:ℝ)≤t-1) a) := by
  have hF0 (b : physicalRealDeletedSubmodule) : D.realNativeForward 0 (by norm_num) b=D.realWeakForward b := by
    have h := D.realNativeForward_weak_commuting 0 (by norm_num) b
    simpa only [show (0:ℝ)-1/2= -1/2 by ring,show (0:ℝ)-1= -1 by ring,
      physicalRealSobolevInclusion_self] using h
  have hI0 (b : physicalRealDeletedSubmodule) : D.realNativeInverse 0 (by norm_num) b=D.realWeakHomeomorph.symm b := by
    have h := D.realNativeInverse_weak_commuting 0 (by norm_num) b
    simpa only [show (0:ℝ)-1/2= -1/2 by ring,show (0:ℝ)-1= -1 by ring,
      physicalRealSobolevInclusion_self] using h
  unfold nativeKdVSourceFlow
  rw [D.realNativeInverse_weak_commuting,nativeTargetKdVPhaseFlow_weak,
    D.realNativeForward_weak_commuting,hI0,hF0]

end NLS.Articles.KdVKdV2Frequencies
