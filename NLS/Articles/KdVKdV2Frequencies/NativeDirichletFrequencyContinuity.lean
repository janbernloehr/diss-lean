import NLS.Articles.KdVKdV2Frequencies.NativeFiniteGapSpectralFrequencies
import NLS.Articles.KdVKdV2Frequencies.DirichletVelocityContinuity
import NLS.SequenceSpaces.PhysicalRealMeanZeroSobolevInclusion
import NLS.KdV.NativeHillSourceComparisons

/-! # Genuine finite Dirichlet frequency continuity in native Sobolev norms -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat NLS.Fourier
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The finite physical KdV Dirichlet sum is continuous on the full original
native H1 space, at all selected modes including closed gaps. -/
theorem continuous_nativeKdVDirichletFrequency (N : ℕ) (n : ℕ+) :
    Continuous (fun q => nativeKdVDirichletFrequency q N n) := by
  have hQ : Continuous (fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)) =>
      nativeHillContinuousSource 1 (by decide) q.val) :=
    (continuous_nativeHillContinuousSource 1 (by decide)).comp continuous_subtype_val
  simpa only [nativeKdVDirichletFrequency,kdvDirichletVelocitySum] using!
    continuous_kdvDirichletVelocitySum_family _ hQ _ (continuous_nativeHillPhysicalSource 1) n N

/-- Three native derivatives supply continuity of the actual physical
second jet. Thus the finite KdV2 Dirichlet sum is continuous after the
literal H^M -> H2 inclusion, with no smoothness or gap-opening assumption. -/
theorem continuous_nativeKdV2DirichletFrequency_higher (M : ℕ) (hM : 3≤M) (N : ℕ) (n : ℕ+) :
    Continuous (fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (M : ℝ)) =>
      nativeKdV2DirichletFrequency
        (physicalRealMeanZeroSobolevInclusion (show ((2 : ℕ) : ℝ)≤(M : ℝ) by exact_mod_cast (show 2≤M by omega)) q) N n) := by
  let L := physicalRealMeanZeroSobolevInclusion
    (show ((2 : ℕ) : ℝ)≤(M : ℝ) by exact_mod_cast (show 2≤M by omega))
  let Q := fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (M : ℝ)) =>
    nativeHillContinuousSource 2 (by decide) (L q).val
  let p := fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (M : ℝ)) =>
    nativeHillPhysicalSource 2 (L q).val (L q).property.1
  have hQ : Continuous Q :=
    (continuous_nativeHillContinuousSource 2 (by decide)).comp (continuous_subtype_val.comp L.continuous)
  have hp : Continuous p := (continuous_nativeHillPhysicalSource 2).comp L.continuous
  have hD : Continuous (fun q => iteratedDeriv 2 (fun x : ℝ => Q q (x : AddCircle (2 : ℝ))) 0) := by
    have he : (fun q => iteratedDeriv 2 (fun x : ℝ => Q q (x : AddCircle (2 : ℝ))) 0) =
        fun q => hierarchySobolevJetContinuous M 2 (by omega) q.val (0 : AddCircle (2 : ℝ)) := by
      funext q
      have hqQ : Q q=nativeHillContinuousSource M (by omega) q.val :=
        nativeHillContinuousSource_eq_of_native_coefficients 2 M (by decide) (by omega) (L q).val q.val
          (fun j => physicalRealMeanZeroSobolevInclusion_coefficient _ q j)
      rw [hqQ,iteratedDeriv_nativeHillContinuousSource_two M hM]
      rfl
    rw [he]
    exact (continuous_eval_const _).comp ((hierarchySobolevJetContinuous M 2 (by omega)).continuous.comp continuous_subtype_val)
  simpa only [L,Q,p,nativeKdV2DirichletFrequency,kdv2DirichletVelocitySum] using!
    continuous_kdv2DirichletVelocitySum_family Q hQ hD p hp n N

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
