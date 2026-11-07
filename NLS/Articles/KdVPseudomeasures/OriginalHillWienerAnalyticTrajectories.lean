import NLS.Articles.KdVPseudomeasures.OriginalHillWienerCanonicalFlow
import NLS.ComplexAnalysis.RealContinuousMapSuperposition
import NLS.SequenceSpaces.FourierRealContractiveComplexification
import NLS.FunctionalAnalysis.ContinuousMapLinearEquivalenceTransport

/-! The actual nonlinear Wiener inverse acts analytically on complete
compact-time paths in the UNIFORM strong Wiener norm. Hence the SAME
original physical KdV flow has Banach real analytic compact trajectories
at EVERY nonnegative integer Wiener order. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
variable {K : Type} [TopologicalSpace K] [CompactSpace K]

local instance (N : ℕ) : NormedSpace ℝ (OriginalWienerTarget N) :=
  fourierRealZeroSubmodule_normedSpace _
local instance (N : ℕ) : NormedSpace ℝ C(K,OriginalWienerTarget N) :=
  @ContinuousMap.normedSpace K (OriginalWienerTarget N) inferInstance inferInstance
    inferInstance ℝ inferInstance (fourierRealZeroSubmodule_normedSpace _)
local instance (N : ℕ) : NormedSpace ℝ
    C(K,fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1) :=
  @ContinuousMap.normedSpace K _ inferInstance inferInstance inferInstance ℝ inferInstance
    (fourierRealZeroSubmodule_normedSpace _)

private def inverseCoefficients (N : ℕ) (z : OriginalWienerTarget N) :
    fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1 :=
  originalWienerSourceCoefficients N ((originalHillWienerEquiv N).symm z)

private theorem analytic_inverseCoefficients (N : ℕ) (z : OriginalWienerTarget N) :
    AnalyticAt ℝ (inverseCoefficients N) z := by
  have hL := @ContinuousLinearMap.analyticAt ℝ inferInstance
    (OriginalWienerPotential N) inferInstance inferInstance
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1)
    inferInstance (fourierRealZeroSubmodule_normedSpace _)
    (originalWienerSourceCoefficients N).toContinuousLinearMap ((originalHillWienerEquiv N).symm z)
  exact hL.comp (f := (originalHillWienerEquiv N).symm) (analyticAt_originalHillWienerEquiv_symm N z)

private theorem analytic_inverseCoefficients_superposition (N : ℕ) (a : C(K,OriginalWienerTarget N)) :
    AnalyticAt ℝ (superposition (K := K) (inverseCoefficients N)) a := by
  let c := fourierRealContractiveComplexification (p := 1)
    (Weight.sobolev (signedStepOrder (1/2) N)) (Weight.sobolev_neg _)
  let d := fourierRealContractiveComplexification (p := 1)
    (Weight.signedSobolev (signedStepOrder 0 N)) (Weight.signedSobolev_neg _)
  exact @analyticAt_real_superposition K (OriginalWienerTarget N)
    (zeroModeSubmodule (Weight.sobolev (signedStepOrder (1/2) N)) 1)
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1)
    (zeroModeSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1)
    inferInstance inferInstance inferInstance (fourierRealZeroSubmodule_normedSpace _)
    inferInstance inferInstance inferInstance (fourierRealZeroSubmodule_normedSpace _)
    inferInstance inferInstance inferInstance c d (fun _ => rfl)
    (inverseCoefficients N) (analytic_inverseCoefficients N) a

theorem analyticAt_originalHillWienerInverse_superposition (N : ℕ) (a : C(K,OriginalWienerTarget N)) :
    AnalyticAt ℝ (superposition (K := K) (originalHillWienerEquiv N).symm) a := by
  have hci : Continuous (originalHillWienerEquiv N).symm :=
    continuous_iff_continuousAt.mpr (fun z => (analyticAt_originalHillWienerEquiv_symm N z).continuousAt)
  exact @NLS.FunctionalAnalysis.analyticAt_superposition_of_linearEquiv K
    (OriginalWienerTarget N) (OriginalWienerPotential N)
    (fourierRealZeroSubmodule (Weight.signedSobolev (signedStepOrder 0 N)) 1)
    inferInstance inferInstance inferInstance (fourierRealZeroSubmodule_normedSpace _)
    inferInstance inferInstance inferInstance (fourierRealZeroSubmodule_normedSpace _)
    (originalWienerSourceCoefficients N) (originalHillWienerEquiv N).symm hci a
    (analytic_inverseCoefficients_superposition N a)

theorem analyticAt_originalWienerKdVTrajectory (N : ℕ) (θ : C(K,ℝ)) (q : OriginalWienerPotential N) :
    AnalyticAt ℝ (originalWienerKdVTrajectory N θ) q := by
  have hA := (analyticAt_originalHillWienerInverse_superposition N
    (originalWienerKdVCoordinateTrajectory N θ q)).comp
      (f := originalWienerKdVCoordinateTrajectory N θ) (analyticAt_originalWienerKdVCoordinateTrajectory N θ q)
  apply hA.congr
  apply Filter.Eventually.of_forall
  intro b
  apply ContinuousMap.ext
  intro t
  have hci : Continuous (originalHillWienerEquiv N).symm :=
    continuous_iff_continuousAt.mpr (fun z => (analyticAt_originalHillWienerEquiv_symm N z).continuousAt)
  exact superposition_apply (U := univ) hci.continuousOn (subset_univ _) t

end NLS.Articles.KdVPseudomeasures
