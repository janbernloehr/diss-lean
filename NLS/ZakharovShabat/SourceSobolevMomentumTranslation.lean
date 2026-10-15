import NLS.ZakharovShabat.SourceSobolevMomentumDifferential
import NLS.ZakharovShabat.SourceSpatialTranslation
import NLS.SequenceSpaces.PhaseFlowDerivative

/-! # Physical momentum generates the actual spatial translation group

Every complex H¹ source has a norm-differentiable L² translation orbit.
The velocity is exactly the Hamiltonian direction of physical momentum,
with the original source norm and period-one normalization.
-/
noncomputable section
open Complex
namespace NLS.ZakharovShabat
open Poisson

/-- Strong L² differentiation of an arbitrary H¹ Fourier translation. -/
theorem hasDerivAt_periodOneSpatialTranslation (a : ScalarDomain 2) (t : ℝ) :
    HasDerivAt (fun r => Coeff.spatialTranslation (2*Real.pi) r (scalarInclusion a))
      (Coeff.spatialTranslation (2*Real.pi) t (periodOneDerivative a)) t := by
  apply Coeff.hasDerivAt_phaseFlow (by simp)
  intro n
  simp only [periodOneDerivative_apply, scalarInclusion_apply]
  push_cast
  ring

/-- The full source-pair translation orbit has its physical derivative in L². -/
theorem hasDerivAt_sourceSpatialTranslation_sobolev
    (a : ScalarDomain 2 × ScalarDomain 2) (t : ℝ) :
    HasDerivAt (fun r => sourceSpatialTranslation r (sobolevSourceInclusion a))
      (sourceSpatialTranslation t (sourceSobolevSpatialDerivative a)) t := by
  exact ((CoeffPair.toMax 2).symm.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_periodOneSpatialTranslation a.1 t).prodMk
      (hasDerivAt_periodOneSpatialTranslation a.2 t))

/-- Momentum's Hamiltonian direction is the actual tangent of the translation orbit. -/
theorem hasDerivAt_sourceSpatialTranslation_momentum (a : ScalarDomain 2 × ScalarDomain 2) :
    HasDerivAt (fun r => sourceSpatialTranslation r (sobolevSourceInclusion a))
      (sourceHamiltonianDirection le_rfl (sourceSobolevMomentumCotangent a)) 0 := by
  rw [sourceHamiltonianDirection_momentum]
  simpa only [sourceSpatialTranslation_zero] using
    hasDerivAt_sourceSpatialTranslation_sobolev a 0

/-- The momentum bracket of any differentiable Hilbert functional is its
actual derivative under spatial translation. -/
theorem hasDerivAt_sourceSpatialTranslation_functional
    (a : ScalarDomain 2 × ScalarDomain 2) (F : CoeffPair 2 → ℂ)
    (hF : DifferentiableAt ℂ F (sobolevSourceInclusion a)) :
    HasDerivAt (fun r => F (sourceSpatialTranslation r (sobolevSourceInclusion a)))
      (sourceBivector le_rfl (fderiv ℂ F (sobolevSourceInclusion a))
        (sourceSobolevMomentumCotangent a)) 0 := by
  have hf : HasFDerivAt F (fderiv ℂ F (sobolevSourceInclusion a))
      (sourceSpatialTranslation 0 (sobolevSourceInclusion a)) := by
    simpa only [sourceSpatialTranslation_zero] using hF.hasFDerivAt
  have hd := (hf.restrictScalars ℝ).comp_hasDerivAt 0
    (hasDerivAt_sourceSpatialTranslation_momentum a)
  change HasDerivAt (fun r => F (sourceSpatialTranslation r (sobolevSourceInclusion a)))
    ((fderiv ℂ F (sobolevSourceInclusion a))
      (sourceHamiltonianDirection le_rfl (sourceSobolevMomentumCotangent a))) 0 at hd
  simpa only [apply_sourceHamiltonianDirection] using hd

/-- Spatial invariance forces the actual physical momentum bracket to vanish. -/
theorem sourceBivector_momentum_eq_zero_of_translation_invariant
    (a : ScalarDomain 2 × ScalarDomain 2) (F : CoeffPair 2 → ℂ)
    (hF : DifferentiableAt ℂ F (sobolevSourceInclusion a))
    (hinv : ∀ r : ℝ, F (sourceSpatialTranslation r (sobolevSourceInclusion a)) =
      F (sobolevSourceInclusion a)) :
    sourceBivector le_rfl (fderiv ℂ F (sobolevSourceInclusion a))
      (sourceSobolevMomentumCotangent a) = 0 := by
  have hd := hasDerivAt_sourceSpatialTranslation_functional a F hF
  simp_rw [hinv] at hd
  exact hd.unique (hasDerivAt_const 0 _)

end NLS.ZakharovShabat
