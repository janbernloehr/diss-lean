import NLS.ZakharovShabat.SourceSobolevSpatialGraph
import NLS.ZakharovShabat.SourceSobolevAngleMomentum
import NLS.ZakharovShabat.SourceFiniteGapAngleSobolev

/-! # Analytic H¹ recovery of the original angle vector

Differentiating the actual constant momentum bracket and using Hessian
symmetry controls the spatial derivative of the angle vector. Bounded graph
recovery then gives an analytic H¹ map. Its inclusion is the original
Hamiltonian vector wherever the momentum bracket has a constant complex
germ; the original Section 20 package supplies those germs separately.
-/
noncomputable section
open Set Filter Topology Complex
open NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAngularThetaCommonDomainData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Differentiating the actual constant momentum bracket and using the original
theta Hessian symmetry gives a cotangent integration-by-parts identity. -/
theorem thetaDifferential_spatial_identity
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (n : ℤ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ W)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0)
    (c : ℂ) (hflat : sourceSobolevThetaMomentumBracket n s =ᶠ[𝓝 a] (fun _ => c))
    (h : ScalarDomain 2 × ScalarDomain 2) :
    sourceAngularThetaDifferential (by simp) (by norm_num) n s (sobolevSourceInclusion a)
      (sourceSobolevSpatialDerivative h) =
      -(fderiv ℂ (sourceAngularThetaDifferential (by simp) (by norm_num) n s)
        (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative a) (sobolevSourceInclusion h)) := by
  let L := sourceAngularThetaDifferential (by simp) (by norm_num) n s
  have hL := ((E.analyticOnNhd_thetaDifferential n _ ⟨ha,hn⟩).differentiableAt.hasFDerivAt).comp a
    sobolevSourceInclusion.hasFDerivAt
  have hd := hL.clm_apply sourceSobolevSpatialDerivative.hasFDerivAt
  have he : (fun b => L (sobolevSourceInclusion b) (sourceSobolevSpatialDerivative b)) =ᶠ[𝓝 a]
      (fun _ => c) := by
    filter_upwards [hflat] with b hb
    exact (sourceSobolevThetaMomentumBracket_eq_spatial n s b).symm.trans hb
  have hz : fderiv ℂ (fun b => L (sobolevSourceInclusion b) (sourceSobolevSpatialDerivative b)) a = 0 := by
    rw [he.fderiv_eq]
    exact (hasFDerivAt_const c a).fderiv
  have hh := congrArg (fun M : (ScalarDomain 2 × ScalarDomain 2) →L[ℂ] ℂ => M h) (hd.fderiv.symm.trans hz)
  change L (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative h) +
    (fderiv ℂ L (sobolevSourceInclusion a)) (sobolevSourceInclusion h) (sourceSobolevSpatialDerivative a) = 0 at hh
  rw [E.fderiv_thetaDifferential_symmetric n _ ha hn] at hh
  exact eq_neg_of_add_eq_zero_left hh
end NLS.ZakharovShabat.SourceAngularThetaCommonDomainData


namespace NLS.ZakharovShabat

/-- Analytic H¹ recovery from the original vector and the spatially differentiated cotangent.
Its identification with the actual angle vector is proved on constant-momentum germs. -/
def sourceSobolevThetaVector (n : ℤ)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (a : ScalarDomain 2 × ScalarDomain 2) :
    ScalarDomain 2 × ScalarDomain 2 :=
  sourceSpatialGraphRecovery
    (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a),
     sourceHamiltonianDirection le_rfl
       (fderiv ℂ (sourceAngularThetaDifferential (by simp) (by norm_num) n s)
         (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative a)))

/-- Bounded graph recovery gives analyticity in the physical H¹ norm. -/
theorem analyticAt_sourceSobolevThetaVector
    {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (n : ℤ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ W)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    AnalyticAt ℂ (sourceSobolevThetaVector n s) a := by
  have hL := E.analyticOnNhd_thetaDifferential n _ ⟨ha,hn⟩
  have hinc := sobolevSourceInclusion.analyticAt a
  have hX := ((sourceHamiltonianDirection le_rfl).analyticAt _).comp (hL.comp hinc)
  have hK := ((sourceHamiltonianDirection le_rfl).analyticAt _).comp
    (((ContinuousLinearMap.id ℂ (CoeffPair 2 →L[ℂ] (CoeffPair 2 →L[ℂ] ℂ))).analyticAt_bilinear _).comp₂
      (hL.fderiv.comp hinc) (sourceSobolevSpatialDerivative.analyticAt a))
  exact (sourceSpatialGraphRecovery.analyticAt _).comp (hX.prod hK)
end NLS.ZakharovShabat

namespace NLS.ZakharovShabat.SourceAngularThetaCommonDomainData
/-- A constant momentum germ identifies the recovered H¹ vector with the actual original vector. -/
theorem sobolevThetaVector_inclusion_of_momentum_germ
    {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (n : ℤ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ W)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0)
    (c : ℂ) (hflat : sourceSobolevThetaMomentumBracket n s =ᶠ[𝓝 a] (fun _ => c)) :
    sobolevSourceInclusion (sourceSobolevThetaVector n s a) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a) := by
  let L := sourceAngularThetaDifferential (by simp) (by norm_num) n s
  let K := fderiv ℂ L (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative a)
  let X := sourceHamiltonianDirection le_rfl (L (sobolevSourceInclusion a))
  let Y := sourceHamiltonianDirection le_rfl K
  have hm := hamiltonian_spatial_coefficients (L (sobolevSourceInclusion a)) K
    (E.thetaDifferential_spatial_identity n a ha hn c hflat)
  have hx (k : ℤ) : Y.fst k = 2*I*(Real.pi : ℂ)*k*X.fst k := by
    linear_combination -(hm k).1
  have hy (k : ℤ) : Y.snd k = 2*I*(Real.pi : ℂ)*k*X.snd k := by
    linear_combination -(hm k).2
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext k
  · change (sobolevSourceInclusion (sourceSobolevThetaVector n s a)).fst k = X.fst k
    rw [sobolevSourceInclusion_fst]
    exact spatialGraphRecovery_coeff X.fst Y.fst hx k
  · change (sobolevSourceInclusion (sourceSobolevThetaVector n s a)).snd k = X.snd k
    rw [sobolevSourceInclusion_snd]
    exact spatialGraphRecovery_coeff X.snd Y.snd hy k
end NLS.ZakharovShabat.SourceAngularThetaCommonDomainData

namespace NLS.ZakharovShabat

/-- A single bounded graph-recovery operator controls every recovered H¹ vector. -/
theorem norm_sourceSobolevThetaVector_le (n : ℤ)
    (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n) (a : ScalarDomain 2 × ScalarDomain 2) :
    ‖sourceSobolevThetaVector n s a‖ ≤ ‖sourceSpatialGraphRecovery‖ *
      max ‖sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a)‖
        ‖sourceHamiltonianDirection le_rfl
          (fderiv ℂ (sourceAngularThetaDifferential (by simp) (by norm_num) n s)
            (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative a))‖ :=
  sourceSpatialGraphRecovery.le_opNorm _

namespace SourceAngularThetaCommonDomainData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The actual spatial derivative of the recovered angle vector is the
Hamiltonian image of the differentiated cotangent in the source's spatial direction. -/
theorem sobolevThetaVector_spatial_of_momentum_germ
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (n : ℤ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ W)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0)
    (c : ℂ) (hflat : sourceSobolevThetaMomentumBracket n s =ᶠ[𝓝 a] (fun _ => c)) :
    sourceSobolevSpatialDerivative (sourceSobolevThetaVector n s a) =
      sourceHamiltonianDirection le_rfl
        (fderiv ℂ (sourceAngularThetaDifferential (by simp) (by norm_num) n s)
          (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative a)) := by
  obtain ⟨v,hv,hd⟩ := exists_hamiltonian_sobolev_of_spatial_identity
    (sourceAngularThetaDifferential (by simp) (by norm_num) n s (sobolevSourceInclusion a))
    (fderiv ℂ (sourceAngularThetaDifferential (by simp) (by norm_num) n s)
      (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative a))
    (E.thetaDifferential_spatial_identity n a ha hn c hflat)
  have he : sourceSobolevThetaVector n s a = v := sobolevSourceInclusion_injective
    ((E.sobolevThetaVector_inclusion_of_momentum_germ n a ha hn c hflat).trans hv.symm)
  rw [he]
  exact hd
end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
