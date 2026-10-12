import NLS.ZakharovShabat.L2CharacteristicGradients
import NLS.ComplexAnalysis.AnalyticImplicitRoot
import NLS.ComplexAnalysis.MovingSpectralParameter

/-! # Actual derivatives of local simple separated-root branches in physical L2 -/

noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

theorem fderiv_l2SeparatedRoot_eq_gradient_quotient (b : BoundaryCondition)
    (μ : IntervalPairL2 → ℂ) (Φ : IntervalPairL2)
    (hμ : ContinuousAt μ Φ)
    (hroot : ∀ᶠ Ψ in 𝓝 Φ, l2SeparatedCharacteristic b Ψ (μ Ψ) = 0)
    (hsimple : deriv (l2SeparatedCharacteristic b Φ) (μ Φ) ≠ 0)
    (H : IntervalPairL2) :
    (fderiv ℂ μ Φ) H = -(deriv (l2SeparatedCharacteristic b Φ) (μ Φ))⁻¹*
      (∫ t in (0 : ℝ)..1, (l2SeparatedGradient b Φ (μ Φ) t).1*H.ofLp.1 t+
        (l2SeparatedGradient b Φ (μ Φ) t).2*H.ofLp.2 t) := by
  let F : ℂ × IntervalPairL2 → ℂ := fun t => l2SeparatedCharacteristic b t.2 t.1
  have hF : AnalyticAt ℂ F (μ Φ,Φ) :=
    analyticOnNhd_l2SeparatedCharacteristic_joint b (μ Φ,Φ) (mem_univ _)
  have hμA : AnalyticAt ℂ μ Φ := by
    apply analyticAt_implicitRoot F μ Φ hF hμ hroot
    rw [← deriv_spectral_section_eq_fderiv F (μ Φ) Φ hF.differentiableAt]
    exact hsimple
  have hzero : (fun Ψ : IntervalPairL2 => F (μ Ψ,Ψ)) =ᶠ[𝓝 Φ] (fun _ => (0 : ℂ)) := hroot
  have hchain := fderiv_moving_spectral_parameter F μ Φ hF.differentiableAt hμA.differentiableAt
  rw [hzero.fderiv_eq] at hchain
  simp only [fderiv_const_apply] at hchain
  have he := congrArg (fun L : IntervalPairL2 →L[ℂ] ℂ => L H) hchain
  simp only [zero_apply,add_apply,smul_apply,smul_eq_mul] at he
  have hquot : (fderiv ℂ μ Φ) H = -(deriv (l2SeparatedCharacteristic b Φ) (μ Φ))⁻¹*
      ((fderiv ℂ (fun Ψ : IntervalPairL2 => l2SeparatedCharacteristic b Ψ (μ Φ)) Φ) H) := by
    change 0 = (fderiv ℂ (fun Ψ : IntervalPairL2 => l2SeparatedCharacteristic b Ψ (μ Φ)) Φ) H+
      deriv (l2SeparatedCharacteristic b Φ) (μ Φ)*(fderiv ℂ μ Φ) H at he
    field_simp [hsimple]
    linear_combination -he
  rw [hquot,fderiv_l2SeparatedCharacteristic_eq_gradient_integral]

end NLS.ZakharovShabat
