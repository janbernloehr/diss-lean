import NLS.ZakharovShabat.ClassicalDirichletGradientNormalization
import NLS.ComplexAnalysis.AnalyticImplicitRoot
import NLS.ComplexAnalysis.MovingSpectralParameter

/-! # The normalized gradient of a genuine local Dirichlet root

A continuous local selection of a simple zero is analytic. Its actual
Fréchet derivative is the physical integral against the normalized
squared eigenfunction. The root is not defined by the gradient formula.
-/

noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- Any continuous local branch of simple classical Dirichlet zeros has
G.7's actual normalized squared-eigenfunction differential. -/
theorem fderiv_classicalDirichletRoot_eq_normalized_integral
    (μ : Curve (ℂ × ℂ) → ℂ) (Φ : Curve (ℂ × ℂ))
    (hμ : ContinuousAt μ Φ)
    (hroot : ∀ᶠ Ψ in 𝓝 Φ, classicalSeparatedCharacteristic .dirichlet Ψ (μ Ψ) = 0)
    (hsimple : deriv (classicalSeparatedCharacteristic .dirichlet Φ) (μ Φ) ≠ 0)
    (H : Curve (ℂ × ℂ)) :
    (fderiv ℂ μ Φ) H = ∫ t in (0 : ℝ)..1,
      (classicalDirichletNormalizedGradient Φ (μ Φ) t).1*(extend H t).1+
      (classicalDirichletNormalizedGradient Φ (μ Φ) t).2*(extend H t).2 := by
  let F : ℂ × Curve (ℂ × ℂ) → ℂ := fun t => classicalSeparatedCharacteristic .dirichlet t.2 t.1
  have hF : AnalyticAt ℂ F (μ Φ,Φ) :=
    analyticOnNhd_classicalSeparatedCharacteristic_joint .dirichlet (μ Φ,Φ) (mem_univ _)
  have hμA : AnalyticAt ℂ μ Φ := by
    apply analyticAt_implicitRoot F μ Φ hF hμ hroot
    rw [← deriv_spectral_section_eq_fderiv F (μ Φ) Φ hF.differentiableAt]
    exact hsimple
  have hzero : (fun Ψ : Curve (ℂ × ℂ) => F (μ Ψ,Ψ)) =ᶠ[𝓝 Φ] (fun _ => (0 : ℂ)) := hroot
  have hchain := fderiv_moving_spectral_parameter F μ Φ hF.differentiableAt hμA.differentiableAt
  rw [hzero.fderiv_eq] at hchain
  simp only [fderiv_const_apply] at hchain
  have he := congrArg (fun L : Curve (ℂ × ℂ) →L[ℂ] ℂ => L H) hchain
  simp only [zero_apply,add_apply,smul_apply,smul_eq_mul] at he
  have hquot : (fderiv ℂ μ Φ) H = -(deriv (classicalSeparatedCharacteristic .dirichlet Φ) (μ Φ))⁻¹*
      ((fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic .dirichlet Ψ (μ Φ)) Φ) H) := by
    change 0 = (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalSeparatedCharacteristic .dirichlet Ψ (μ Φ)) Φ) H+
      deriv (classicalSeparatedCharacteristic .dirichlet Φ) (μ Φ)*(fderiv ℂ μ Φ) H at he
    field_simp [hsimple]
    linear_combination -he
  rw [hquot,fderiv_classicalSeparatedCharacteristic_eq_gradient_integral,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  dsimp only
  rw [classicalDirichletNormalizedGradient_eq_characteristic_quotient Φ (μ Φ)
    hroot.self_of_nhds hsimple ⟨t,ht'⟩]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

end NLS.ZakharovShabat
