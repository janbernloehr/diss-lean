import NLS.Articles.KdVPseudomeasures.OriginalHillActionRotation
import NLS.Articles.KdVPseudomeasures.OriginalHillSpatialStationarity
import NLS.KdV.HillActionSpatialTranslation
import NLS.FunctionalAnalysis.CompactInvariantFlowEquivariance

/-! The ACTUAL complete indexed action flows commute with ACTUAL spatial
translation on the full original physical real Hminus-one source. This is
proved from Gardner covariance and ODE uniqueness, not from assumed
Birkhoff spatial phases or source action-flow periods. -/
noncomputable section
open NLS.KdV Complex
namespace NLS.Articles.KdVPseudomeasures

/-- Exact commutation of the ACTUAL complete action flow with spatial
translation, for EVERY index, source, displacement and real flow time. -/
theorem originalHillNativeActionFlow_spatialTranslation (n : ℕ+) (q : HillRealMeanZeroSource)
    (s t : ℝ) :
    originalHillNativeActionFlow n (hillRealSpatialTranslation s q) t=
      hillRealSpatialTranslation s (originalHillNativeActionFlow n q t) := by
  exact (originalHillActionHamiltonianSystem n).globalCurve_equivariant (hillRealSpatialTranslation s)
    (fun p => (hillRealActionHamiltonianVector_spatialTranslation n s p).symm) q t

/-- The physical real coefficient symmetry is EXACTLY the previous entire
original distributional spatial translation, with the same2*pi phases. -/
theorem originalHillRealMeanZeroSource_spatialTranslation (q : OriginalHminusOnePotential) (s : ℝ) :
    originalHillRealMeanZeroSource (originalHillSpatialTranslation s q)=
      hillRealSpatialTranslation s (originalHillRealMeanZeroSource q) := by
  apply hillRealMeanZeroInclusion_injective
  rw [originalHillRealMeanZeroSource_inclusion,originalHillSpatialTranslation_coefficients,
    hillRealSpatialTranslation_inclusion,originalHillRealMeanZeroSource_inclusion]

/-- The commutation statement on the ENTIRE original physical distribution
domain. Every input is the SAME original source; no smoothness is imposed. -/
theorem original_Hill_action_flow_spatial_commutation (n : ℕ+)
    (q : OriginalHminusOnePotential) (s t : ℝ) :
    originalHillNativeActionFlow n
      (originalHillRealMeanZeroSource (originalHillSpatialTranslation s q)) t=
      hillRealSpatialTranslation s (originalHillNativeActionFlow n (originalHillRealMeanZeroSource q) t) := by
  rw [originalHillRealMeanZeroSource_spatialTranslation,originalHillNativeActionFlow_spatialTranslation]

/-- Exact action-flow invariance of the ACTUAL spatial coordinate quotient.
Division is valid as a total complex operation even at a closed coordinate;
only the already proved nonzero scalar action rotation is canceled. -/
theorem originalHill_spatialCoordinateRatio_actionFlow_invariant (n : ℕ+)
    (q : HillRealMeanZeroSource) (s t : ℝ) (k : ℤ) :
    hillHminusNativeCoordinate k (hillRealMeanZeroInclusion
        (hillRealSpatialTranslation s (originalHillNativeActionFlow n q t)))/
      hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (originalHillNativeActionFlow n q t))=
    hillHminusNativeCoordinate k (hillRealMeanZeroInclusion (hillRealSpatialTranslation s q))/
      hillHminusNativeCoordinate k (hillRealMeanZeroInclusion q) := by
  rw [← originalHillNativeActionFlow_spatialTranslation,originalHillNativeActionFlow_coordinate,
    originalHillNativeActionFlow_coordinate]
  exact mul_div_mul_left _ _ (Complex.exp_ne_zero _)

/-- Actual spatial translation preserves EVERY positive native coordinate
modulus. This follows from the actual action identity, not a phase formula. -/
theorem norm_hillRealNativeCoordinate_spatialTranslation (n : ℕ+) (s : ℝ) (q : HillRealMeanZeroSource) :
    ‖hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion (hillRealSpatialTranslation s q))‖=
      ‖hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q)‖ := by
  have hp (p : HillRealMeanZeroSource) := hillHminusNativeComplexMap_action_identity
    (hillRealMeanZeroInclusion p) (real_mem_hillHminusActionAngleNativeDomain _ p.property) n
  have hact : hillHminusCanonicalAction n (hillRealMeanZeroInclusion (hillRealSpatialTranslation s q))=
      hillHminusCanonicalAction n (hillRealMeanZeroInclusion q) := by
    rw [hillRealSpatialTranslation_inclusion]
    exact hillHminusCanonicalAction_spatialTranslation_real _ q.property s n
  have he := (hp (hillRealSpatialTranslation s q)).trans (hact.trans (hp q).symm)
  have hr (p : HillRealMeanZeroSource) :
      (hillHminusNativeComplexMap (hillRealMeanZeroInclusion p)).val (-(n:ℤ))=
        (starRingEnd ℂ) ((hillHminusNativeComplexMap (hillRealMeanZeroInclusion p)).val (n:ℤ)) :=
    hillHminusNativeComplexMap_real _ p.property (n:ℤ)
  rw [hr,hr] at he
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := congrArg Complex.re he
  simpa only [hillHminusNativeCoordinate,mul_conj,ofReal_re,normSq_eq_norm_sq] using h

/-- Every actual open-coordinate spatial quotient is unimodular. Its
specific winding number or speed is NOT inferred from this statement. -/
theorem norm_hillRealSpatialCoordinateRatio (n : ℕ+) (s : ℝ) (q : HillRealMeanZeroSource)
    (hz : hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q) ≠ 0) :
    ‖hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion (hillRealSpatialTranslation s q))/
      hillHminusNativeCoordinate (n:ℤ) (hillRealMeanZeroInclusion q)‖=1 := by
  rw [norm_div,norm_hillRealNativeCoordinate_spatialTranslation,div_self (norm_ne_zero_iff.mpr hz)]

end NLS.Articles.KdVPseudomeasures
