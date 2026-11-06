import NLS.Articles.KdVConvexity.FourierLebesguePhysicalPhaseFlow
import NLS.Articles.KdVConvexity.NativeOriginalFrequencyCompatibility

/-! # The phase flow uses the original physical KdV Hamiltonian frequencies

At every actual H1 source the new native-target action map agrees with
the original cubic-weighted physical actions. This identifies its base
frequency with the independently proved intrinsic KdV frequency, including
closed indices and every Fourier-Lebesgue norm representing that target.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.Articles.KdVKdV2Frequencies

theorem fourierLebesguePhysicalActions_eq_original
    (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (ha : D.nativeSourceActionSequence 1 3 (by norm_num) q=originalPositiveActionInsertion b.val)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p)
    (hz : ∀ j : ℤ, z.val.val j=(D.signed (nativeHillSource 1 q.val)).val j) :
    fourierLebesguePhysicalActions s hs p hp h2p z=
      baseActionInclusion (originalActionInclusion b.val) := by
  apply Subtype.ext
  funext k
  rw [fourierLebesguePhysicalActions_apply,hz,hz,
    baseActionInclusion_apply,originalActionInclusion_apply,Equiv.symm_apply_apply]
  have h := congrArg (fun a => a.val (actionIndexEquiv k : ℤ)) ha
  rw [D.nativeSourceActionSequence_apply,if_pos (by exact_mod_cast (actionIndexEquiv k).pos),
    originalPositiveActionInsertion_apply,Equiv.symm_apply_apply] at h
  exact h

/-- Actual Hamiltonian frequency recovery for EVERY native target that
represents the signed physical coordinates of the supplied H1 source. -/
theorem BasePhysicalFrequencyExtension.fourierLebesgueFrequency_eq_native
    (B : BasePhysicalFrequencyExtension) (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)))
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p)
    (hz : ∀ j : ℤ, z.val.val j=(D.signed (nativeHillSource 1 q.val)).val j) (n : ℕ+) :
    B.fourierLebesguePhysicalFrequency s hs p hp h2p z n=
      D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n := by
  obtain ⟨b,ha,_⟩ := exists_original_actions_of_native_source D q
  have hi := fourierLebesguePhysicalActions_eq_original D q b ha s hs p hp h2p z hz
  have he : (B.fourierLebesguePhysicalFrequency s hs p hp h2p z n : ℂ)=
      (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ) := by
    rw [B.fourierLebesguePhysicalFrequency_coe,hi,B.physical_agreement,
      ←nativeSourceFrequency_eq_originalPhysicalFrequency D q b ha n]
  exact Complex.ofReal_injective he

end NLS.Articles.KdVConvexity
