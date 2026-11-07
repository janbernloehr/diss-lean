import NLS.Articles.KdVPseudomeasures.OriginalHillWienerPhaseTrajectory
import NLS.FunctionalAnalysis.InverseGermDerivative

/-! Literal Wiener auxiliary assertions: surjectivity, invertibility
of every differential, and analytic trajectories with target initial data. -/
noncomputable section
open Set NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures
local instance sourceWienerAuxiliaryTargetNormedSpace (N : ℕ) : NormedSpace ℝ (OriginalWienerTarget N) :=
  fourierRealZeroSubmodule_normedSpace _

theorem sourceLemma5_5 (N : ℕ) : Function.Surjective (originalHillWienerEquiv N) :=
  (originalHillWienerEquiv N).surjective

theorem sourceLemma5_6 (N : ℕ) (q : OriginalWienerPotential N) :
    ∃ e : OriginalWienerPotential N ≃L[ℝ] OriginalWienerTarget N,
      (e : OriginalWienerPotential N →L[ℝ] OriginalWienerTarget N) =
        fderiv ℝ (originalHillWienerEquiv N) q := by
  obtain ⟨e,he,_⟩ := @NLS.FunctionalAnalysis.exists_fderiv_equiv_of_inverse_germs
    ℝ (OriginalWienerPotential N) (OriginalWienerTarget N)
    inferInstance inferInstance inferInstance inferInstance (fourierRealZeroSubmodule_normedSpace _)
    (originalHillWienerEquiv N) (originalHillWienerEquiv N).symm q
    (analyticAt_originalHillWienerEquiv N q).differentiableAt
    (analyticAt_originalHillWienerEquiv_symm N _).differentiableAt
    ((originalHillWienerEquiv N).symm_apply_apply q)
    (by exact Filter.Eventually.of_forall (originalHillWienerEquiv N).symm_apply_apply)
    (by exact Filter.Eventually.of_forall (originalHillWienerEquiv N).apply_symm_apply)
  exact ⟨e,he⟩

variable {K : Type} [TopologicalSpace K] [CompactSpace K]
local instance sourceWienerAuxiliaryTrajectoryNormedSpace (N : ℕ) : NormedSpace ℝ C(K,OriginalWienerTarget N) :=
  @ContinuousMap.normedSpace K (OriginalWienerTarget N) inferInstance inferInstance
    inferInstance ℝ inferInstance (fourierRealZeroSubmodule_normedSpace _)

def originalWienerKdVTargetTrajectory (N : ℕ) (θ : C(K,ℝ)) (z : OriginalWienerTarget N) :
    C(K,OriginalWienerTarget N) :=
  originalWienerKdVCoordinateTrajectory N θ ((originalHillWienerEquiv N).symm z)

theorem sourceLemma5_8 (N : ℕ) (θ : C(K,ℝ)) (z : OriginalWienerTarget N) :
    AnalyticAt ℝ (originalWienerKdVTargetTrajectory N θ) z :=
  (analyticAt_originalWienerKdVCoordinateTrajectory N θ _).comp
    (f := (originalHillWienerEquiv N).symm) (analyticAt_originalHillWienerEquiv_symm N z)

theorem originalWienerKdVTargetTrajectory_initial (N : ℕ) (θ : C(K,ℝ))
    (z : OriginalWienerTarget N) (t : K) (ht : θ t=0) :
    originalWienerKdVTargetTrajectory N θ z t=z := by
  rw [originalWienerKdVTargetTrajectory,originalWienerKdVCoordinateTrajectory_phase,ht]
  rw [fourierRealZeroPhaseFlow_zero]
  exact (originalHillWienerEquiv N).apply_symm_apply z

end NLS.Articles.KdVPseudomeasures
