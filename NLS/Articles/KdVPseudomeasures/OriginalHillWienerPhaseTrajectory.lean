import NLS.Articles.KdVPseudomeasures.MainTheorem51
import NLS.Articles.KdVPseudomeasures.OriginalHillWienerSignedFrequency
import NLS.SequenceSpaces.FourierRealAnalyticPhaseTrajectory

/-! The actual original Birkhoff phase trajectories are Banach real
analytic in the UNIFORM compact-time weighted ell-one norm, at EVERY
nonnegative integer order. All original signed coordinates are retained. -/
noncomputable section
open Complex NLS.KdV NLS.WeightedCoeff
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

local instance (N : ℕ) : NormedSpace ℝ C(K,OriginalWienerTarget N) :=
  @ContinuousMap.normedSpace K (OriginalWienerTarget N) inferInstance inferInstance
    inferInstance ℝ inferInstance (fourierRealZeroSubmodule_normedSpace _)

def originalWienerKdVCoordinateTrajectory (N : ℕ) (θ : C(K,ℝ)) (q : OriginalWienerPotential N) :
    C(K,OriginalWienerTarget N) :=
  fourierRealAnalyticPhaseTrajectory (by simp : (1:ℝ≥0∞) ≠ ⊤)
    (Weight.sobolev (signedStepOrder (1/2) N)) (Weight.sobolev_neg _)
    (fun k => (2*Real.pi*(k:ℝ))^3) θ
    (originalWienerSignedFrequencyCorrection N q) (originalHillWienerEquiv N q)

theorem analyticAt_originalWienerKdVCoordinateTrajectory (N : ℕ) (θ : C(K,ℝ)) (q : OriginalWienerPotential N) :
    AnalyticAt ℝ (originalWienerKdVCoordinateTrajectory N θ) q := by
  have hpair : AnalyticAt ℝ (fun a : OriginalWienerPotential N =>
      (originalWienerSignedFrequencyCorrection N a,originalHillWienerEquiv N a)) q :=
    (analyticAt_originalWienerSignedFrequencyCorrection N q).prod (analyticAt_originalHillWienerEquiv N q)
  exact (analyticAt_fourierRealAnalyticPhaseTrajectory (p := 1) (by simp)
    (Weight.sobolev (signedStepOrder (1/2) N)) (Weight.sobolev_neg _)
    (fun k => (2*Real.pi*(k:ℝ))^3) θ _).comp
      (f := fun a : OriginalWienerPotential N =>
        (originalWienerSignedFrequencyCorrection N a,originalHillWienerEquiv N a)) hpair

theorem originalWienerKdVCoordinateTrajectory_phase (N : ℕ) (θ : C(K,ℝ)) (q : OriginalWienerPotential N) (t : K) :
    originalWienerKdVCoordinateTrajectory N θ q t =
      fourierRealZeroPhaseFlow (Weight.sobolev (signedStepOrder (1/2) N))
        (originalWienerSignedKdVFrequency N q) (originalWienerSignedKdVFrequency_neg N q)
        (θ t) (originalHillWienerEquiv N q) :=
  fourierRealAnalyticPhaseTrajectory_apply (by simp) _ _ _ θ _ _ _ _
    (originalWienerSignedFrequencyCorrection_free N q) t

theorem originalWienerKdVCoordinateTrajectory_apply (N : ℕ) (θ : C(K,ℝ))
    (q : OriginalWienerPotential N) (t : K) (k : ℤ) :
    (originalWienerKdVCoordinateTrajectory N θ q t).val.val.val k =
      exp (((θ t*originalWienerSignedKdVFrequency N q k:ℝ):ℂ)*I)*
        (hillRealSignedMap (originalHillRealMeanZeroSource (originalWienerOriginalPotential N q))).val.val.val k := by
  rw [originalWienerKdVCoordinateTrajectory_phase,fourierRealZeroPhaseFlow_apply,originalHillWienerEquiv_apply]

theorem norm_originalWienerKdVCoordinateTrajectory_apply (N : ℕ) (θ : C(K,ℝ))
    (q : OriginalWienerPotential N) (t : K) :
    ‖originalWienerKdVCoordinateTrajectory N θ q t‖=‖originalHillWienerEquiv N q‖ := by
  rw [originalWienerKdVCoordinateTrajectory_phase,norm_fourierRealZeroPhaseFlow]

end NLS.Articles.KdVPseudomeasures
