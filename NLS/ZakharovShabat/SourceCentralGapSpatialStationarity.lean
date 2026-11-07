import NLS.ZakharovShabat.SourceActionSpatialStationarity
import NLS.ZakharovShabat.SourceSection20MomentumBracket
import NLS.ZakharovShabat.SourceBirkhoffRegularCotangent
import NLS.ZakharovShabat.SourceBirkhoffJacobianInvertible
import NLS.ZakharovShabat.SourceFiniteGapSobolev

/-! A real Dirac source with no noncentral open gap is spatially constant.
The proof uses actual physical translation, actual momentum normalization
and the actual Birkhoff derivative, including closed coordinates. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

theorem jacobian_spatial_closed_coordinate
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n=0) :
    (sourceBirkhoffJacobian (by simp) (by norm_num) s (sobolevSourceInclusion a)
      (sourceSobolevSpatialDerivative a)).1 n=0 ∧
    (sourceBirkhoffJacobian (by simp) (by norm_num) s (sobolevSourceInclusion a)
      (sourceSobolevSpatialDerivative a)).2 n=0 := by
  let F := sourceBirkhoffMap (p := 2) (by simp) (by norm_num) s
  have hF : @HasFDerivAt ℂ inferInstance
      (CoeffPair 2) (inferInstance : NormedAddCommGroup (CoeffPair 2)).toAddCommGroup
      (inferInstance : NormedSpace ℂ (CoeffPair 2)).toModule inferInstance
      (Coeff 2 × Coeff 2) (inferInstance : NormedAddCommGroup (Coeff 2 × Coeff 2)).toAddCommGroup
      (inferInstance : NormedSpace ℂ (Coeff 2 × Coeff 2)).toModule inferInstance
      F (sourceBirkhoffJacobian (by simp) (by norm_num) s (sobolevSourceInclusion a))
      (sourceSpatialTranslation 0 (sobolevSourceInclusion a)) := by
    simpa only [F,sourceBirkhoffJacobian,sourceSpatialTranslation_zero] using
      (D.analytic _ (D.real_subset ha)).differentiableAt.hasFDerivAt
  have hd := (hF.restrictScalars ℝ).comp_hasDerivAt 0
    (hasDerivAt_sourceSpatialTranslation_sobolev a 0)
  simp only [sourceSpatialTranslation_zero] at hd
  let ex : (Coeff 2 × Coeff 2) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2))
  let ey : (Coeff 2 × Coeff 2) →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))
  have hx := (ex.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hd
  have hy := (ey.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hd
  have hz (t : ℝ) : (F (sourceSpatialTranslation t (sobolevSourceInclusion a))).1 n=0 ∧
      (F (sourceSpatialTranslation t (sobolevSourceInclusion a))).2 n=0 := by
    have hreal := sourceSpatialTranslation_realType t (sobolevSourceInclusion a) ha
    apply D.real_closed_gap_zero _ (D.real_subset hreal) hreal n
    simpa only [sourcePeriodicGapDisplacement_apply,
      sourceCanonicalPeriodicGap_spatialTranslation] using hn
  change HasDerivAt (fun t => (F (sourceSpatialTranslation t (sobolevSourceInclusion a))).1 n)
    ((sourceBirkhoffJacobian (by simp) (by norm_num) s (sobolevSourceInclusion a)
      (sourceSobolevSpatialDerivative a)).1 n) 0 at hx
  change HasDerivAt (fun t => (F (sourceSpatialTranslation t (sobolevSourceInclusion a))).2 n)
    ((sourceBirkhoffJacobian (by simp) (by norm_num) s (sobolevSourceInclusion a)
      (sourceSobolevSpatialDerivative a)).2 n) 0 at hy
  simp_rw [(fun t => (hz t).1)] at hx
  simp_rw [(fun t => (hz t).2)] at hy
  exact ⟨hx.unique (hasDerivAt_const 0 0),hy.unique (hasDerivAt_const 0 0)⟩

end SourceBirkhoffMapComplexData
namespace SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}

/-- Every actual Birkhoff coordinate has zero spatial velocity when only
the central gap may be open, including all its collapsed coordinates. -/
theorem jacobian_spatial_eq_zero_of_noncentral_gaps_closed
    (Q : SourceSection20Data D A B U)
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)))
    (hclosed : ∀ n : ℤ, n ≠ 0 → canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n=0) :
    sourceBirkhoffJacobian (by simp) (by norm_num) s (sobolevSourceInclusion a)
      (sourceSobolevSpatialDerivative a)=0 := by
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion a,ha⟩
  have hrow (n : ℤ) :
      (sourceBirkhoffJacobian (by simp) (by norm_num) s φ.val (sourceSobolevSpatialDerivative a)).1 n=0 ∧
      (sourceBirkhoffJacobian (by simp) (by norm_num) s φ.val (sourceSobolevSpatialDerivative a)).2 n=0 := by
    by_cases hn : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem _) n=0
    · exact D.complex.jacobian_spatial_closed_coordinate a ha n hn
    · have hn0 : n=0 := by by_contra h; exact hn (hclosed n h)
      subst n
      have hθ := Q.sobolev_momentum_bracket ⟨a,ha⟩ 0 hn
      rw [sourceSobolevThetaMomentumBracket_eq_spatial] at hθ
      simp only [Int.cast_zero,mul_zero] at hθ
      have hI : (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) 0) φ.val)
          (sourceSobolevSpatialDerivative a)=0 := sourceComplexAction_spatial_derivative_zero a ha 0
      have hθ' : sourceAngularThetaDifferential (by simp) (by norm_num) 0 s φ.val
          (sourceSobolevSpatialDerivative a)=0 := hθ
      have hc := D.previous.original_theta_common_domain.birkhoffXY_fderiv 0 φ hn
      have hj := D.complex.jacobian_coordinates φ.val (D.complex.real_subset ha)
        (sourceSobolevSpatialDerivative a) 0
      rw [hj.1,hj.2,hc.1,hc.2]
      simp only [add_apply,smul_apply,smul_eq_mul]
      constructor <;> rw [hI,hθ'] <;> ring
  apply Prod.ext <;> ext n
  · exact (hrow n).1
  · exact (hrow n).2

/-- Actual derivative injectivity forces the original source to have no
nonzero spatial Fourier coefficient; no inverse spectral assumption is used. -/
theorem spatialDerivative_eq_zero_of_noncentral_gaps_closed
    (Q : SourceSection20Data D A B U)
    (a : ScalarDomain 2 × ScalarDomain 2)
    (ha : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)))
    (hclosed : ∀ n : ℤ, n ≠ 0 → canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n=0) :
    sourceSobolevSpatialDerivative a=0 := by
  apply (D.complex.jacobian_bijective le_rfl ⟨sobolevSourceInclusion a,ha⟩).1
  rw [Q.jacobian_spatial_eq_zero_of_noncentral_gaps_closed a ha hclosed,map_zero]

end SourceSection20Data
end NLS.ZakharovShabat
