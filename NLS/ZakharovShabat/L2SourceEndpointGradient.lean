import NLS.ZakharovShabat.L2EndpointGradient
import NLS.ZakharovShabat.SourcePhysicalL2

/-! # Physical endpoint gradient integrals on the original Hilbert source space -/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Every Hilbert source direction is paired with the actual physical endpoint gradient. -/
theorem fderiv_sourceL2Endpoint_eq_gradient_integral (φ h : CoeffPair 2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    (fderiv ℂ (fun ψ : CoeffPair 2 => ℓ (l2SolutionCurve (sourcePhysicalL2 ψ) z v t)) φ) h =
      ∫ s in (0 : ℝ)..t.val, (l2EndpointGradient (sourcePhysicalL2 φ) z v ℓ t s).1*
        (sourcePhysicalL2 h).ofLp.1 s+
        (l2EndpointGradient (sourcePhysicalL2 φ) z v ℓ t s).2*(sourcePhysicalL2 h).ofLp.2 s := by
  let F := fun u : IntervalPairL2 => ℓ (l2SolutionCurve u z v t)
  have hd := (analyticOnNhd_l2SolutionCurve_potential z v (sourcePhysicalL2 φ) (mem_univ _)).differentiableAt.hasFDerivAt
  let ev : Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := ContinuousMap.evalCLM ℂ t
  have hf : DifferentiableAt ℂ F (sourcePhysicalL2 φ) :=
    (ℓ.hasFDerivAt.comp (sourcePhysicalL2 φ) (ev.hasFDerivAt.comp (sourcePhysicalL2 φ) hd)).differentiableAt
  change (fderiv ℂ (F ∘ sourcePhysicalL2) φ) h = _
  rw [fderiv_comp φ hf sourcePhysicalL2.differentiableAt,ContinuousLinearMap.comp_apply,
    sourcePhysicalL2.fderiv]
  exact fderiv_l2Endpoint_eq_gradient_integral (sourcePhysicalL2 φ) (sourcePhysicalL2 h) z v ℓ t

/-- The formula uses the original Fourier-synthesized source direction with no new normalization. -/
theorem fderiv_sourceL2Endpoint_eq_physical_integral (φ h : CoeffPair 2) (z : ℂ) (v : ℂ × ℂ)
    (ℓ : (ℂ × ℂ) →L[ℂ] ℂ) (t : Icc (0 : ℝ) 1) :
    (fderiv ℂ (fun ψ : CoeffPair 2 => ℓ (l2SolutionCurve (sourcePhysicalL2 ψ) z v t)) φ) h =
      ∫ s in (0 : ℝ)..t.val, (l2EndpointGradient (sourcePhysicalL2 φ) z v ℓ t s).1*
        (physicalBase (periodOnePotential h) s).1+
        (l2EndpointGradient (sourcePhysicalL2 φ) z v ℓ t s).2*(physicalBase (periodOnePotential h) s).2 := by
  rw [fderiv_sourceL2Endpoint_eq_gradient_integral]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le t.property.1]
  filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    (sourcePhysicalL2_representative h)] with s hs
  have h₁ := congrArg Prod.fst hs
  have h₂ := congrArg Prod.snd hs
  change (sourcePhysicalL2 h).ofLp.1 s = (physicalBase (periodOnePotential h) s).1 at h₁
  change (sourcePhysicalL2 h).ofLp.2 s = (physicalBase (periodOnePotential h) s).2 at h₂
  rw [h₁,h₂]

end NLS.ZakharovShabat
