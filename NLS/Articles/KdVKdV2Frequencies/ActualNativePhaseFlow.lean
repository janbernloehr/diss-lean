import NLS.Articles.KdVKdV2Frequencies.ActualNativeTargetFrequency
import NLS.SequenceSpaces.PhysicalRealPhaseRotation

/-! The actual action-dependent KdV phase group at every native order.
Its frequencies are the globally calibrated physical frequencies. -/
noncomputable section
open Set Complex
namespace NLS.Articles.KdVKdV2Frequencies

def nativeTargetKdVPhaseFlow (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (time : ℝ) (z : physicalRealDeletedSubmodule) : physicalRealDeletedSubmodule :=
  physicalRealPhaseRotation (nativeTargetKdVSignedFrequency t ht G z)
    (nativeTargetKdVSignedFrequency_odd t ht G z) time z

theorem nativeTargetActions_phaseFlow (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (time : ℝ) (z : physicalRealDeletedSubmodule) :
    nativeTargetActions (nativeTargetKdVPhaseFlow t ht G time z)=nativeTargetActions z :=
  quadraticActions_physicalRealPhaseRotation _ _ _ _ _

theorem nativeTargetWeakActions_phaseFlow (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (time : ℝ) (z : physicalRealDeletedSubmodule) :
    nativeTargetWeakActions t ht (nativeTargetKdVPhaseFlow t ht G time z)=nativeTargetWeakActions t ht z := by
  unfold nativeTargetWeakActions
  rw [nativeTargetActions_phaseFlow]

theorem nativeTargetKdVSignedFrequency_phaseFlow (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (time : ℝ) (z : physicalRealDeletedSubmodule) :
    nativeTargetKdVSignedFrequency t ht G (nativeTargetKdVPhaseFlow t ht G time z)=
      nativeTargetKdVSignedFrequency t ht G z := by
  unfold nativeTargetKdVSignedFrequency nativeTargetKdVNaturalFrequency nativeTargetKdVFrequency
  simp_rw [nativeTargetWeakActions_phaseFlow]

@[simp] theorem nativeTargetKdVPhaseFlow_zero (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (z : physicalRealDeletedSubmodule) : nativeTargetKdVPhaseFlow t ht G 0 z=z :=
  physicalRealPhaseRotation_zero _ _ _

theorem nativeTargetKdVPhaseFlow_add (t : ℝ) (ht : 0≤t) (G : ℕ+ → Coeff 1 → ℂ)
    (time u : ℝ) (z : physicalRealDeletedSubmodule) :
    nativeTargetKdVPhaseFlow t ht G time (nativeTargetKdVPhaseFlow t ht G u z)=
      nativeTargetKdVPhaseFlow t ht G (time+u) z := by
  unfold nativeTargetKdVPhaseFlow at *
  simp only [show nativeTargetKdVSignedFrequency t ht G
      (physicalRealPhaseRotation (nativeTargetKdVSignedFrequency t ht G z)
        (nativeTargetKdVSignedFrequency_odd t ht G z) u z)=nativeTargetKdVSignedFrequency t ht G z from
          nativeTargetKdVSignedFrequency_phaseFlow t ht G u z]
  exact physicalRealPhaseRotation_add _ _ _ _ _

theorem continuous_nativeTargetKdVPhaseFlow (t : ℝ) (ht : 0≤t)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V) :
    Continuous (fun x : ℝ × physicalRealDeletedSubmodule => nativeTargetKdVPhaseFlow t ht G x.1 x.2) := by
  apply continuous_physicalRealPhaseRotation_family _ _ id _ continuous_id
  intro j
  unfold nativeTargetKdVSignedFrequency signedHamiltonianFrequency nativeTargetKdVNaturalFrequency
  split_ifs
  · exact continuous_nativeTargetKdVFrequency t ht G V hCV hG _
  · exact continuous_const
  · exact (continuous_nativeTargetKdVFrequency t ht G V hCV hG _).neg
  · exact continuous_const.neg
  · exact continuous_const

end NLS.Articles.KdVKdV2Frequencies
