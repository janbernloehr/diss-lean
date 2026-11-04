import NLS.Articles.MKdVBelowL2.PhysicalFourthImageFlow
import NLS.ZakharovShabat.SourceActionPhaseSobolevLift

/-! # Full Sobolev regularity of the fixed physical fourth trajectory

The weighted source path belongs to the same fixed physical Birkhoff family.
Every nonnegative Sobolev order is preserved, with continuous dependence in
the complete compact-time weighted norm. These statements do not yet assert
the physical PDE for arbitrary smooth data.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

/-- The actual fixed fourth path retaining its complete native Sobolev norm. -/
def fourthSobolevTrajectoryOn (σ : ℝ) (hσ : 0 ≤ σ) (T : ℝ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ)) :
    C(Icc (-T) T,weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ)) :=
  (fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).sobolevTrajectoryOn
    (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex le_rfl σ hσ T a

/-- The stronger path represents exactly the same two original physical
distributions as the fixed physical fourth lift at every time. -/
theorem fourthSobolevTrajectoryOn_physical (σ : ℝ) (hσ : 0 ≤ σ) (T : ℝ)
    (a : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ))
    (time : Icc (-T) T) :
    physicalRealCoefficientsCL.symm
      (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ)
        (fourthSobolevTrajectoryOn σ hσ T a time)) =
    fourthPhysicalImageFlow (p := 2) (by simp) (by norm_num)
      (physicalRealCoefficientsCL.symm (originalWeightedRealSource (sourceSobolevSpectralWeight σ hσ) a)) time.val := by
  unfold fourthPhysicalImageFlow
  rw [ContinuousLinearEquiv.apply_symm_apply]
  apply congrArg physicalRealCoefficientsCL.symm
  exact SourceActionFrequency.originalWeightedRealSource_sobolevImageFlow _ _ le_rfl σ hσ a time.val

/-- Continuous dependence in the full uniform Sobolev trajectory norm. -/
theorem continuous_fourthSobolevTrajectoryOn (σ : ℝ) (hσ : 0 ≤ σ) (T : ℝ) :
    Continuous (fourthSobolevTrajectoryOn σ hσ T) :=
  SourceActionFrequency.continuous_sobolevTrajectoryOn _ _ le_rfl σ hσ T

/-- Any convergent family has convergent complete fourth paths in the full
uniform native Sobolev norm, including a given finite-gap approximating family. -/
theorem tendsto_fourthSobolevTrajectoryOn (σ : ℝ) (hσ : 0 ≤ σ) (T : ℝ)
    {ι : Type*} {l : Filter ι}
    (a : ι → weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ))
    (b : weightedRealSourceSubmodule (p := 2) (sourceSobolevSpectralWeight σ hσ))
    (ha : Tendsto a l (𝓝 b)) :
    Tendsto (fun i => fourthSobolevTrajectoryOn σ hσ T (a i)) l
      (𝓝 (fourthSobolevTrajectoryOn σ hσ T b)) :=
  (continuous_fourthSobolevTrajectoryOn σ hσ T).continuousAt.tendsto.comp ha

end NLS.Articles.MKdVBelowL2
