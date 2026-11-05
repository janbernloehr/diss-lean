import NLS.ZakharovShabat.SourceSobolevMomentumTranslation
import NLS.ZakharovShabat.SourceSpatialTranslation
import NLS.ZakharovShabat.SourceIsospectralSet

/-! Actual canonical actions are stationary under actual spatial translation,
including closed gaps. The physical period-one derivative has its factor2*pi. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Actual spatial translation preserves every actual indexed action. -/
theorem sourceComplexAction_spatialTranslation (φ : realTypeSourceSubmodule 2) (t : ℝ) (n : ℤ) :
    sourceComplexAction (by simp) (by norm_num) n (sourceSpatialTranslation t φ.val)=
      sourceComplexAction (by simp) (by norm_num) n φ.val := by
  let ψ : realTypeSourceSubmodule 2 :=
    ⟨sourceSpatialTranslation t φ.val,sourceSpatialTranslation_realType t φ.val φ.property⟩
  have hi : ψ ∈ sourceIsospectralSet (by simp) φ :=
    ⟨sourcePeriodicSpectrum_spatialTranslation (by simp) t φ.val,
      sourcePeriodicAlgebraicMultiplicity_spatialTranslation (by simp) t φ.val⟩
  exact (sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n ψ.val ψ.property).trans
    ((sourceRealAction_eq_of_isospectral (by simp) (by norm_num) φ ψ hi n).trans
      (sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property).symm)

/-- The actual action differential vanishes on the actual spatial derivative. -/
theorem sourceComplexAction_spatial_derivative_zero (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) (n : ℤ) :
    (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) (sobolevSourceInclusion a))
      (sourceSobolevSpatialDerivative a)=0 := by
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a,ha⟩
  have hF : HasFDerivAt (sourceComplexAction (by simp) (by norm_num) n)
      (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val)
      (sourceSpatialTranslation 0 φ.val) := by
    simpa only [sourceSpatialTranslation_zero] using
      (analyticAt_sourceComplexAction_of_realType (by simp) (by norm_num) n φ.val φ.property).differentiableAt.hasFDerivAt
  have hd := (hF.restrictScalars ℝ).comp_hasDerivAt 0
    (hasDerivAt_sourceSpatialTranslation_sobolev a 0)
  simp only [sourceSpatialTranslation_zero] at hd
  change HasDerivAt (fun t => sourceComplexAction (by simp) (by norm_num) n
    (sourceSpatialTranslation t φ.val))
    ((fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val) (sourceSobolevSpatialDerivative a)) 0 at hd
  simp_rw [sourceComplexAction_spatialTranslation φ] at hd
  exact hd.unique (hasDerivAt_const 0 _)

end NLS.ZakharovShabat
