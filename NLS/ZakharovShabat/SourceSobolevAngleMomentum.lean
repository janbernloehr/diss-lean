import NLS.ZakharovShabat.SourceSobolevMomentumTranslation
import NLS.ZakharovShabat.SourceAngularThetaHamiltonian
import NLS.ZakharovShabat.SourceAngularThetaLocalExactness

/-! # The actual angle–momentum bracket on complex H¹ sources

The bracket uses the physical momentum cotangent and the original angle
differential. It is analytic throughout the original complex open-gap
domain and is the derivative of every local angle under spatial translation.
This module does not yet identify its value with `2πn`.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat
open Poisson

/-- The original angle bracket with physical momentum, without selecting an angle branch. -/
def sourceSobolevThetaMomentumBracket (n : ℤ)
    (s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k)
    (a : ScalarDomain 2 × ScalarDomain 2) : ℂ :=
  sourceBivector le_rfl (sourceAngularThetaDifferential (by simp) (by norm_num) n s
    (sobolevSourceInclusion a)) (sourceSobolevMomentumCotangent a)

theorem sourceSobolevThetaMomentumBracket_eq_spatial (n : ℤ)
    (s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k)
    (a : ScalarDomain 2 × ScalarDomain 2) :
    sourceSobolevThetaMomentumBracket n s a =
      sourceAngularThetaDifferential (by simp) (by norm_num) n s
        (sobolevSourceInclusion a) (sourceSobolevSpatialDerivative a) :=
  sourceBivector_momentum a _

/-- Whenever the actual angle vector has an H¹ lift, its momentum
derivative is the negative of the original angle–momentum bracket. -/
theorem sourceSobolevThetaMomentumBracket_eq_neg_derivative (n : ℤ)
    (s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k)
    (a h : ScalarDomain 2 × ScalarDomain 2)
    (hh : sobolevSourceInclusion h = sourceAngularThetaHamiltonianVector
      (by simp) (by norm_num) le_rfl n s (sobolevSourceInclusion a)) :
    sourceSobolevThetaMomentumBracket n s a =
      -(fderiv ℂ periodOneSobolevMomentum a h) := by
  rw [fderiv_periodOneSobolevMomentum, ContinuousLinearMap.comp_apply, hh,
    sourceAngularThetaHamiltonianVector, apply_sourceHamiltonianDirection,
    sourceBivector_antisymm, neg_neg]
  rfl

namespace SourceAngularThetaCommonDomainData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The physical bracket is analytic on every complex H¹ point of the original open-gap domain. -/
theorem analyticOnNhd_sobolevThetaMomentumBracket
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceSobolevThetaMomentumBracket n s)
      {a | sobolevSourceInclusion a ∈ W ∧ canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0} := by
  intro a ha
  exact ((sourceBivector le_rfl).analyticAt_bilinear _).comp₂
    ((E.analyticOnNhd_thetaDifferential n _ ha).comp (sobolevSourceInclusion.analyticAt a))
    (sourceSobolevMomentumCotangent.analyticAt a)

/-- A constructed local angle realizes the physical bracket as an actual
translation derivative; no angle covariance is assumed. -/
theorem exists_local_theta_translation_derivative
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) W₀ B W s)
    (n : ℤ) (a : ScalarDomain 2 × ScalarDomain 2) (ha : sobolevSourceInclusion a ∈ W)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a)) (periodOnePotential_mem _) n ≠ 0) :
    ∃ θ : CoeffPair 2 → ℂ, AnalyticAt ℂ θ (sobolevSourceInclusion a) ∧
      sourceAngularThetaDifferential (by simp) (by norm_num) n s =ᶠ[𝓝 (sobolevSourceInclusion a)]
        (fun φ => fderiv ℂ θ φ) ∧
      HasDerivAt (fun r => θ (sourceSpatialTranslation r (sobolevSourceInclusion a)))
        (sourceSobolevThetaMomentumBracket n s a) 0 := by
  obtain ⟨θ,hθ,he⟩ := E.exists_local_thetaDifferential_fderiv n _ ha hn
  refine ⟨θ,hθ,he,?_⟩
  rw [sourceSobolevThetaMomentumBracket, he.eq_of_nhds]
  exact hasDerivAt_sourceSpatialTranslation_functional a θ hθ.differentiableAt

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
